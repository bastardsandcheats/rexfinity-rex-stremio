"""Keep newly added RD and TorBox browse torrents out of Rex's library."""
import datetime
from contextlib import closing
import logging
import os
import re
import sys
import threading
import time
from pathlib import Path
import requests

LOG = logging.getLogger('rex-stremio')
HASH = re.compile(r'[0-9a-f]{40}', re.I)


def torbox_matches(rows, pending, seen):
    matches = []
    for row in rows[:100]:
        if not isinstance(row, dict):
            continue
        hash_ = str(row.get('hash') or '').lower()
        if not HASH.fullmatch(hash_) or hash_ in seen:
            continue
        at = added_at(row.get('created_at'))
        if not at or at < min(pending.values()) - 2:
            continue
        name = next((name for file in row.get('files') or [] if isinstance(file, dict)
                     for name in pending if (filename(file.get('short_name')) == name
                     or filename(file.get('name')) == name) and at >= pending[name] - 2), None)
        if name:
            matches.append((hash_, name))
    return matches


def flag_library_exclusions(items, path=None):
    """Use PlexControl's existing hash table and atomic Zurg exclusion publisher."""
    from plexcontrol import external_requests as exclusions
    path = Path(path or exclusions.DEFAULT_DATABASE)
    exclusions.ensure_schema(path)
    now = time.time()
    changed = 0
    with closing(exclusions._open_write_database(path)) as db, db:
        for hash_, title in items:
            hash_ = str(hash_ or '').lower()
            if not HASH.fullmatch(hash_):
                raise ValueError('expected a torrent infohash')
            changed += db.execute('''INSERT INTO external_request_library_exclusions
                (hash,request_id,title,created_at,updated_at) VALUES(?,?,?,?,?)
                ON CONFLICT(hash) DO UPDATE SET request_id=excluded.request_id,title=excluded.title,
                    cleared_at=NULL,clear_reason='',updated_at=excluded.updated_at
                WHERE external_request_library_exclusions.cleared_at IS NOT NULL''',
                (hash_, 'rex-stremio:' + hash_, str(title)[:240], now, now)).rowcount
    if changed:
        exclusions._write_exclusions(path)
    return changed


def filename(value):
    name = os.path.basename(str(value or '')).casefold().strip()
    return name if len(name) >= 12 else ''


def added_at(value):
    try:
        stamp = datetime.datetime.fromisoformat(str(value).replace('Z', '+00:00'))
        return stamp.replace(tzinfo=stamp.tzinfo or datetime.timezone.utc).timestamp()
    except (TypeError, ValueError):
        return 0


class LibraryIgnore:
    def __init__(self):
        self.lock = threading.Lock()
        self.pending = {}
        self.running = False

    def note(self, streams, since):
        names = {filename((stream.get('behaviorHints') or {}).get('filename'))
                 for stream in streams if isinstance(stream, dict)}
        names.discard('')
        if not names:
            return
        with self.lock:
            now = time.time()
            self.pending = {name: at for name, at in self.pending.items() if now - at < 120}
            for name in names:
                self.pending[name] = min(self.pending.get(name, since), since)
            if not self.running:
                self.running = True
                threading.Thread(target=self._run, name='rd-library-ignore', daemon=True).start()

    def _run(self):
        # AIO may add a torrent when the link is opened, after the stream search.
        # One bounded inventory poll serves all browsing/probe activity.
        try:
            sys.path.insert(0, '/opt/plexcontrol')
            from plexcontrol.config import Settings
            from plexcontrol.dmm_rd import rd_request
            settings = Settings.load()
            if not settings.real_debrid_api_key and not settings.torbox_api_key:
                LOG.warning('Library ignore unavailable: PlexControl has no debrid keys')
                return
            seen = set()
            checked = {}
            started = time.monotonic()
            while True:
                with self.lock:
                    now = time.time()
                    self.pending = {name: at for name, at in self.pending.items() if now - at < 120}
                    pending = dict(self.pending)
                if not pending:
                    return
                if settings.real_debrid_api_key:
                  try:
                    rows = rd_request(settings.real_debrid_api_url, settings.real_debrid_api_key,
                                      'GET', '/torrents?limit=100&page=1', timeout=15)
                    if not isinstance(rows, list):
                        raise ValueError('RD inventory was not a list')
                    matches = []
                    for row in rows[:100]:
                        if not isinstance(row, dict):
                            continue
                        hash_ = str(row.get('hash') or '').lower()
                        if not HASH.fullmatch(hash_) or hash_ in seen:
                            continue
                        at = added_at(row.get('added'))
                        if not at or at < min(pending.values()) - 2:
                            continue
                        if time.time() - checked.get(hash_, 0) < 30:
                            continue
                        checked[hash_] = time.time()
                        # The torrent title may be a folder or release name. Check its
                        # actual files before associating it with a Stremio result.
                        info = rd_request(settings.real_debrid_api_url, settings.real_debrid_api_key,
                                          'GET', '/torrents/info/' + str(row['id']), timeout=15)
                        files = (info.get('files') or []) if isinstance(info, dict) else []
                        matched = next((name for file in files if isinstance(file, dict)
                                        for name in pending if filename(file.get('path')) == name
                                        and at >= pending[name] - 2), None)
                        if matched:
                            matches.append((hash_, matched))
                    if matches:
                        count = flag_library_exclusions(matches)
                        seen.update(hash_ for hash_, _ in matches)
                        LOG.info('RD library ignore flagged %d new torrent(s)', count)
                  except Exception as error:
                    LOG.warning('RD library ignore check failed: %s', type(error).__name__)
                if settings.torbox_api_key:
                    try:
                        response = requests.get('https://api.torbox.app/v1/api/torrents/mylist',
                                                headers={'Authorization': 'Bearer ' + settings.torbox_api_key},
                                                params={'bypass_cache': 'true', 'limit': 100, 'offset': 0},
                                                timeout=15)
                        response.raise_for_status()
                        rows = response.json().get('data') or []
                        if not isinstance(rows, list):
                            raise ValueError('TorBox inventory was not a list')
                        matches = torbox_matches(rows, pending, seen)
                        if matches:
                            count = flag_library_exclusions(matches)
                            seen.update(hash_ for hash_, _ in matches)
                            LOG.info('TorBox library ignore flagged %d new torrent(s)', count)
                    except Exception as error:
                        LOG.warning('TorBox library ignore check failed: %s', type(error).__name__)
                time.sleep(3 if time.monotonic() - started < 30 else 10)
        finally:
            with self.lock:
                self.running = False

#!/usr/bin/env python3
"""rex-stremio: Stremio addons' catalogs as a rex source.

Catalogs come from the Stremio addons you add, streams from every addon that serves them, as in
Stremio. Each film or episode goes to rex with its IMDb id, so Plex names it; nothing is
downloaded: rex plays the stream an addon gives at the moment someone presses play.

One process does three things:

* a relay rex reads bytes from: `GET /<library>/<catalog>/<item>.<ext>` asks the stream addons,
  ranks what they give, and answers 302 to the first link that opens (asked again when the
  cached one is an hour old, as addons' links expire).
* a sync loop that registers with rex's feed API (`docs/feed-api.md` in every rex download),
  declares the libraries, and pushes every item of every chosen catalog, each probed once.
* a settings page at `/` for adding addons, choosing catalogs and ranking streams. It answers
  only your own network and writes `config.json`.

Standard library only; ffprobe is a separate executable.
"""
import argparse
import collections
import copy
import email.utils
import functools
import hashlib
import html
import ipaddress
import json
import logging
import math
import os
import re
import subprocess
import sys
import threading
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from rd_library_ignore import LibraryIgnore
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

LOG = logging.getLogger("rex-stremio")
MAX_FORM_BYTES = 1 << 20
MAX_FORM_FIELDS = 2000
MAX_JSON_BYTES = 16 << 20
SEARCH_TIMEOUT = 10
PROBE_TIMEOUT = 10
OPEN_TIMEOUT = 10
VERSION_PROBE_DELAY = 2
PROBE_RETRY_SECONDS = 3
REFUSALS = 3
BACKOFF = 5
MAX_BACKOFF = 60
WARM_FETCH_SCRIPT = ("import sys,urllib.request\n"
                     "url=sys.stdin.readline().rstrip('\\n')\n"
                     "request=urllib.request.Request(url,headers={'User-Agent':'rex-stremio','Accept':'application/json'})\n"
                     "with urllib.request.urlopen(request,timeout=30) as response: sys.stdout.buffer.write(response.read())\n")

DEFAULTS = {
    "rex_url": "http://127.0.0.1:32400",
    "rex_token": None,
    "source": "stremio",
    "listen": "127.0.0.1:9982",
    "relay_url": None,
    "mount": "/mnt/rex-stremio",
    "cache": "cache",
    "ffprobe": "ffprobe",
    "interval_minutes": 360,
    "stream_interval_seconds": 1,
    "retry_minutes": 10,
    "max_resolution": None,
    "collections": False,
    "ondemand_movies_library": "On Demand Movies",
    "ondemand_tv_library": "On Demand TV",
    "hide_ondemand_libraries": True,
    "exclude_rd_library": False,
    "max_size_gb": None,
    "addons": [],
    "catalogs": [],
}

# Series' seasons and episodes come from Cinemeta, whose ids are IMDb's.
CINEMETA = "https://v3-cinemeta.strem.io"
# A catalog that lists TMDB ids (`tmdb:…`: Cartoon Network, Nickelodeon, Sitcom Catalogs...) names
# no IMDb id; when no added addon's meta does, the TMDB addon's does (2026-10-24).
TMDB_META = "https://tmdb.elfhosted.com"

# Where each item's probe is kept. "probes2" since an HLS master is relayed as its best variant
# alone: a probe of the whole master names other streams, so every item is probed once more.
PROBES = "probes2"

# ffprobe's container -> the extension rex takes the file by (an HLS playlist is `.m3u8`).
CONTAINERS = {"hls": "m3u8", "matroska,webm": "mkv", "mov,mp4,m4a,3gp,3g2,mj2": "mp4", "mpegts": "ts", "avi": "avi"}

RESOLUTIONS = [(r"2160p|\b4k\b|\buhd\b", 2160), (r"1440p", 1440), (r"1080p|\bfhd\b", 1080), (r"720p|\bhd\b", 720),
               (r"576p|480p|\bsd\b", 480)]

# A catalog's Stremio type -> its default library and the kind of rex library that holds it. A
# live channel (`tv`) is a film-like row: nothing identifies it, the addon's `display` names it.
LIBRARIES = {"movie": "Stremio Films", "series": "Stremio Shows", "tv": "Live TV"}
REX_KINDS = {"movie": "movies", "series": "shows", "tv": "movies"}


class Refused(Exception):
    pass


def retry_after(value):
    try:
        return max(float(value), 0.0)
    except (TypeError, ValueError):
        pass
    try:
        return max(email.utils.parsedate_to_datetime(value).timestamp() - time.time(), 0.0)
    except (TypeError, ValueError):
        return None


def slug(text):
    return re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-") or "catalog"


def get_json(url, timeout=60):
    request = urllib.request.Request(url, headers={"User-Agent": "rex-stremio", "Accept": "application/json"})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response_json(response)


def response_json(response):
    chunks, total = [], 0
    while True:
        chunk = response.read(min(1 << 16, MAX_JSON_BYTES + 1 - total))
        if not chunk:
            break
        chunks.append(chunk)
        total += len(chunk)
        if total > MAX_JSON_BYTES:
            raise ValueError("JSON response is too large")
    body = b"".join(chunks)
    return json.loads(body or b"{}")


def write_json(path, value, indent=None):
    """Replace a JSON file atomically without exposing addon credentials."""
    directory = os.path.dirname(os.path.abspath(path)) or "."
    descriptor, temporary = tempfile.mkstemp(prefix=".%s-" % os.path.basename(path), dir=directory)
    try:
        if hasattr(os, "fchmod"):  # Windows has none, and its files have no mode bits to set
            os.fchmod(descriptor, 0o600)
        handle = os.fdopen(descriptor, "w")
        # fdopen now owns the descriptor. Do not close its old integer again if a later
        # dump/replace fails: that number may already have been reused by another thread.
        descriptor = None
        with handle:
            json.dump(value, handle, indent=indent)
        os.replace(temporary, path)
    finally:
        if descriptor is not None:
            try:
                os.close(descriptor)
            except OSError:
                pass
        try:
            os.unlink(temporary)
        except OSError:
            pass


def safe_url(url):
    """A URL's scheme and host, without credentials, path or query secrets."""
    try:
        parts = urllib.parse.urlsplit(str(url))
        host = parts.hostname
        if not parts.scheme or not host:
            return "<url>"
        host = "[%s]" % host if ":" in host else host
        if parts.port:
            host += ":%d" % parts.port
        return "%s://%s" % (parts.scheme, host)
    except (TypeError, ValueError):
        return "<url>"


def safe_error(error):
    """Remove credential-bearing URLs before an error reaches logs or status."""
    text = str(error)
    return re.sub(r"https?://[^\s'\"<>]+", lambda match: safe_url(match.group()), text)[:300]


def safe_stream_key(value):
    return safe_url(value) if isinstance(value, str) and value.startswith(("http://", "https://")) else value


def rex_endpoint(base, path):
    """Append a feed route without discarding a configured rex path or query."""
    parts = urllib.parse.urlsplit(base)
    return urllib.parse.urlunsplit((parts.scheme, parts.netloc, parts.path.rstrip("/") + path,
                                    parts.query, ""))


def addon_base(url):
    """A manifest's url as Stremio shows it (`stremio://`, `.../manifest.json`) -> the addon's base."""
    if not isinstance(url, str):
        return ""
    url = url.strip()
    if url.startswith("stremio://"):
        url = "https://" + url[len("stremio://"):]
    return url.removesuffix("/manifest.json").rstrip("/")


def addon_manifest(addon):
    value = addon.get("manifest") if isinstance(addon, dict) else None
    return value if isinstance(value, dict) else {}


def serves(manifest, resource, kind, sid):
    """Whether an addon answers `resource` for `kind` and this id, by its manifest."""
    if not isinstance(manifest, dict) or not isinstance(sid, str):
        return False
    resources = manifest.get("resources")
    if not isinstance(resources, list):
        return False
    for entry in resources:
        if isinstance(entry, str):
            entry = {"name": entry}
        if not isinstance(entry, dict):
            continue
        if entry.get("name") != resource:
            continue
        types = entry.get("types") or manifest.get("types") or []
        prefixes = entry.get("idPrefixes") or manifest.get("idPrefixes")
        if isinstance(types, str):
            types = [types]
        elif not isinstance(types, list):
            types = []
        types = [value for value in types if isinstance(value, str)]
        if isinstance(prefixes, str):
            prefixes = [prefixes]
        elif not isinstance(prefixes, list):
            prefixes = []
        prefixes = [value for value in prefixes if isinstance(value, str)]
        if isinstance(kind, str) and kind in types and (not prefixes or any(sid.startswith(prefix) for prefix in prefixes)):
            return True
    return False


def catalogs_of(manifest):
    """The catalogs of films, series and live channels an addon lists without being asked something first (a
    search catalog needs a query)."""
    if not isinstance(manifest, dict):
        return []
    raw_catalogs = manifest.get("catalogs")
    if not isinstance(raw_catalogs, list):
        return []
    out = []
    for catalog in raw_catalogs:
        if not isinstance(catalog, dict):
            continue
        raw_extra = catalog.get("extra")
        if raw_extra is not None and not isinstance(raw_extra, list):
            continue
        extra = raw_extra if isinstance(raw_extra, list) else []
        required = [entry for entry in extra
                    if isinstance(entry, dict) and entry.get("isRequired")]
        extra_required = catalog.get("extraRequired")
        if extra_required is not None and not isinstance(extra_required, list):
            continue
        if isinstance(extra_required, list):
            required += [name for name in extra_required if isinstance(name, str)]
        if (catalog.get("type") in LIBRARIES and isinstance(catalog.get("id"), str)
                and catalog["id"] and not required):
            out.append({"type": catalog["type"], "id": catalog["id"], "name": catalog.get("name") or catalog["id"]})
    return out


def quality(stream):
    """(resolution, size in bytes) as the stream's labels give them; 0 or None where they do not."""
    if not isinstance(stream, dict):
        return 0, None
    hints = stream.get("behaviorHints") or {}
    if not isinstance(hints, dict):
        hints = {}
    text = " ".join(str(stream.get(key) or "") for key in ("name", "title", "description")) + " " + str(hints.get("filename") or "")
    resolution = next((value for pattern, value in RESOLUTIONS if re.search(pattern, text, re.I)), 0)
    size = hints.get("videoSize")
    try:
        size = float(size) if size else None
    except (TypeError, ValueError, OverflowError):
        size = None
    if size is not None and (not math.isfinite(size) or size <= 0):
        size = None
    if not size:
        found = re.search(r"(\d+(?:\.\d+)?)\s*(GB|MB)\b", text, re.I)
        if found:
            try:
                size = float(found[1]) * (1 << (30 if found[2].upper() == "GB" else 20))
            except (TypeError, ValueError, OverflowError):
                size = None
    if size is not None and (not math.isfinite(size) or size <= 0):
        size = None
    return resolution, int(size) if size else None


def stream_key(stream):
    """What names one stream across asks: its file, else its group, else its link."""
    if not isinstance(stream, dict):
        return None
    hints = stream.get("behaviorHints") or {}
    if not isinstance(hints, dict):
        hints = {}
    return hints.get("filename") or hints.get("bingeGroup") or stream.get("url")


def ranked(streams, config, pinned=None):
    """The streams rex can read, best first: an http(s) `url` (a torrent's `infoHash`, a YouTube
    `ytId` and an `externalUrl` are not files), within the configured limits, highest
    resolution first, the addons' own order breaking ties. The stream an item was probed from
    (`pinned`) goes first, so what plays is what rex was told about."""
    try:
        cap = int(config["max_resolution"]) if config.get("max_resolution") is not None else None
    except (TypeError, ValueError):
        cap = None
    try:
        biggest = config.get("max_size_gb") and float(config["max_size_gb"]) * (1 << 30)
    except (TypeError, ValueError, OverflowError):
        biggest = None
    if biggest is not None and not math.isfinite(biggest):
        biggest = None
    if not isinstance(streams, list):
        return []
    kept = []
    for at, stream in enumerate(streams):
        if not isinstance(stream, dict):
            continue
        if not isinstance(stream.get("url"), str) or not stream["url"].startswith(("http://", "https://")):
            continue
        resolution, size = quality(stream)
        if (cap and resolution > cap) or (biggest and size and size > biggest):
            continue
        kept.append((stream_key(stream) != pinned if pinned else False, -resolution, at, stream))
    return [stream for *_, stream in sorted(kept, key=lambda row: row[:3])]


def request_headers(stream):
    """The headers a stream's link must be asked with (`behaviorHints.proxyHeaders.request`, which
    Stremio's streaming server sends for it). Eclipsia, Hyper, Hydra and BanglaPlex links answer
    403 or 429 without their Referer and 206 with it (2026-10-24). Encoding is left to us: a
    playlist is read and rewritten here."""
    hints = stream.get("behaviorHints") if isinstance(stream, dict) else None
    proxy = hints.get("proxyHeaders") if isinstance(hints, dict) else None
    headers = proxy.get("request") if isinstance(proxy, dict) else None
    if not isinstance(headers, dict):
        return {}
    return {str(name): str(value) for name, value in headers.items()
            if isinstance(value, (str, int)) and str(name).lower() not in ("accept-encoding", "range", "host", "connection", "content-length")}


def opens(url, headers=None, timeout=OPEN_TIMEOUT):
    """The link a stream ends at, when it opens; None when it does not (an expired or refused link,
    or a web page: addons list their configure page, a donation or status page as a "stream", and
    Comet's unconfigured answer was nothing else, 2026-10-24)."""
    request = urllib.request.Request(url, headers=dict({"User-Agent": "rex-stremio"}, **(headers or {}), Range="bytes=0-0"))
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            kind = response.headers.get_content_type()
            if kind == "text/html":
                LOG.info("%s: a web page, not a video", safe_url(url))
                return None
            # A file that answers a Range with all of itself cannot be seeked, and rex reads every
            # file by Range: Google's video-downloads links send the whole 9.6 GB MKV from byte 0
            # (PlavioHD, Flix-Streams, 2026-10-24) and a player reading its end got its start.
            playlist = "mpegurl" in kind or urllib.parse.urlsplit(response.geturl()).path.endswith(".m3u8")
            if response.status == 200 and not playlist and int(response.headers.get("Content-Length") or 0) > 1:
                LOG.info("%s: answers no Range, so it cannot be seeked", safe_url(url))
                return None
            # A "file" of a few bytes is an error body: one of Hydra's links was 150 bytes at play.
            total = re.search(r"/(\d+)$", response.headers.get("Content-Range") or "")
            if total and int(total[1]) < (1 << 20) and not playlist:
                LOG.info("%s: %s bytes, not a video", safe_url(url), total[1])
                return None
            return response.geturl() if response.status in (200, 206) else None
    except Exception as error:
        LOG.info("%s: %s", safe_url(url), safe_error(error))
        return None


def load_config(path):
    with open(path) as handle:
        raw = json.load(handle)
    if not isinstance(raw, dict):
        raise ValueError("config must be an object")
    config = dict(DEFAULTS, **raw)
    if not isinstance(config.get("catalogs"), list) or not isinstance(config.get("addons"), list):
        raise ValueError("addons and catalogs must be lists")
    if not isinstance(config.get("source"), str) or not re.fullmatch(r"[A-Za-z0-9_-]+", config["source"]):
        raise ValueError("source must be a simple name")
    for key in ("rex_url", "relay_url"):
        value = config.get(key)
        if value is None:
            if key == "rex_url":
                raise ValueError("rex_url must be an http(s) URL")
            continue
        if not isinstance(value, str):
            raise ValueError("%s must be an http(s) URL" % key)
        try:
            parts = urllib.parse.urlsplit(value)
            parts.port
            hostname = parts.hostname
        except (TypeError, ValueError):
            raise ValueError("%s must be an http(s) URL" % key)
        if parts.scheme not in ("http", "https") or not hostname:
            raise ValueError("%s must be an http(s) URL" % key)
    if not isinstance(config.get("cache"), str) or not config["cache"]:
        raise ValueError("cache must be a path")
    if config.get("rex_token") is not None and (not isinstance(config["rex_token"], str) or not config["rex_token"]):
        raise ValueError("rex_token must be a non-empty string")
    for key in ("listen", "mount", "ffprobe"):
        if not isinstance(config.get(key), str) or not config[key]:
            raise ValueError("%s must be a string" % key)
    if not re.fullmatch(r"(?:\[[^\]]+\]|[^:]+):\d{1,5}", config["listen"]):
        raise ValueError("listen must be host:port")
    if int(config["listen"].rsplit(":", 1)[1]) > 65535:
        raise ValueError("listen port is out of range")
    try:
        interval = int(config.get("interval_minutes"))
    except (TypeError, ValueError):
        raise ValueError("interval_minutes must be positive")
    if interval <= 0:
        raise ValueError("interval_minutes must be positive")
    config["interval_minutes"] = interval
    if config.get("max_resolution") is not None:
        try:
            config["max_resolution"] = int(config["max_resolution"])
        except (TypeError, ValueError):
            raise ValueError("max_resolution must be a number")
        if config["max_resolution"] <= 0:
            raise ValueError("max_resolution must be positive")
    if config.get("max_size_gb") is not None:
        try:
            config["max_size_gb"] = float(config["max_size_gb"])
        except (TypeError, ValueError):
            raise ValueError("max_size_gb must be a number")
        if not math.isfinite(config["max_size_gb"]) or config["max_size_gb"] <= 0:
            raise ValueError("max_size_gb must be positive")
    if not isinstance(config.get("collections"), bool):
        raise ValueError("collections must be true or false")
    for key in ("ondemand_movies_library", "ondemand_tv_library"):
        if not isinstance(config.get(key), str) or not config[key].strip():
            raise ValueError("%s must be a library name" % key)
        config[key] = config[key].strip()[:160]
    if not isinstance(config.get("hide_ondemand_libraries"), bool):
        raise ValueError("hide_ondemand_libraries must be true or false")
    if config["cache"] and not os.path.isabs(config["cache"]):
        config["cache"] = os.path.join(os.path.dirname(os.path.abspath(path)), config["cache"])
    if not config["relay_url"]:
        config["relay_url"] = "http://" + config["listen"]
    catalogs = []
    explicit_slugs = set()
    records = []
    for raw_catalog in config["catalogs"]:
        if not isinstance(raw_catalog, dict):
            raise ValueError("catalog must be an object")
        catalog = dict(raw_catalog)
        url = catalog.get("url", "")
        if not isinstance(url, str):
            raise ValueError("catalog URL must be a string")
        found = re.fullmatch(r"(https?://.+?)/catalog/(movie|series|tv)/([^/]+?)\.json", url)
        if not found:
            raise ValueError("not a Stremio catalog URL (<addon>/catalog/<movie|series|tv>/<id>.json)")
        catalog = dict({"library": LIBRARIES[found[2]], "limit": 50}, **catalog)
        if not isinstance(catalog.get("library"), str) or not catalog["library"].strip():
            raise ValueError("catalog library must be a name")
        try:
            catalog["limit"] = int(catalog["limit"])
        except (TypeError, ValueError):
            raise ValueError("catalog limit must be positive")
        if catalog["limit"] <= 0:
            raise ValueError("catalog limit must be positive")
        has_slug = "slug" in raw_catalog and raw_catalog.get("slug") not in (None, "")
        if has_slug:
            if not isinstance(catalog.get("slug"), str) or not re.fullmatch(r"[A-Za-z0-9_-]+", catalog["slug"]):
                raise ValueError("catalog slug must be a simple name")
            if catalog["slug"] in explicit_slugs:
                raise ValueError("catalog slugs must be unique")
            explicit_slugs.add(catalog["slug"])
        else:
            catalog.pop("slug", None)
        has_directory = "directory" in raw_catalog and raw_catalog.get("directory") not in (None, "")
        if has_directory and (not isinstance(catalog.get("directory"), str)
                              or not re.fullmatch(r"[A-Za-z0-9_-]+", catalog["directory"])):
            raise ValueError("catalog directory must be a simple name")
        if not has_directory:
            catalog.pop("directory", None)
        catalog["type"] = found[2]
        records.append((catalog, found[3], has_slug, has_directory))
    allocated_slugs = set(explicit_slugs)
    for catalog, catalog_id, has_slug, has_directory in records:
        if not has_slug:
            base = slug(str(catalog.get("title") or catalog_id))
            candidate = base
            while candidate in allocated_slugs:
                # Keep the historical sequence (base, base-2, base-2-2, ...). Existing
                # configs without persisted identity must not move their feed ids on upgrade.
                candidate += "-2"
            catalog["slug"] = candidate
        allocated_slugs.add(catalog["slug"])
        if not has_directory:
            catalog["directory"] = slug(catalog["library"])
        if not isinstance(catalog["directory"], str) or not re.fullmatch(r"[A-Za-z0-9_-]+", catalog["directory"]):
            raise ValueError("catalog directory must be a simple name")
        catalogs.append(catalog)
    libraries = {}
    for catalog in catalogs:
        key = (catalog["directory"], REX_KINDS[catalog["type"]])
        previous = libraries.setdefault(key, catalog["library"])
        if previous != catalog["library"]:
            raise ValueError("catalog directory has conflicting libraries")
    config["catalogs"] = catalogs
    return config


def save_config(path, values):
    """The settings as written, mode 600: addon URLs can hold debrid keys.
    Catalog identity is retained so item ids do not move when rows are reordered."""
    raw = dict(values, catalogs=[{key: value for key, value in catalog.items() if key != "type"}
                                 for catalog in values.get("catalogs") or []])
    if raw.get("relay_url") == "http://%s" % raw.get("listen"):
        del raw["relay_url"]
    write_json(path, raw, indent=2)


def validate_config(path, values):
    """Parse a candidate beside the real file before replacing the saved config."""
    directory = os.path.dirname(os.path.abspath(path)) or "."
    descriptor, candidate = tempfile.mkstemp(prefix=".rex-stremio-config-", dir=directory)
    os.close(descriptor)
    os.chmod(candidate, 0o600)
    try:
        save_config(candidate, values)
        return load_config(candidate)
    finally:
        try:
            os.unlink(candidate)
        except FileNotFoundError:
            pass


@functools.lru_cache(maxsize=None)
def lenient_hls(ffprobe):
    """`-extension_picky 0` where the ffprobe has it. FFmpeg 7.1+ refuses a whole HLS one of
    whose segments' format does not match its URL's extension, as PenguPlay's channels' WebVTT
    rendition does (ffprobe 8.1, 2026-10-24); an older one refuses the unknown option."""
    try:
        out = subprocess.run([ffprobe, "-hide_banner", "-h", "demuxer=hls"], capture_output=True, timeout=2).stdout
    except (OSError, subprocess.SubprocessError):
        return ()
    return ("-extension_picky", "0") if b"-extension_picky" in out else ()


def placeholder(probe):
    """A film or an episode a minute long is an addon's message, not the title: Freedom Media's
    links all played one 10 s clip (2026-10-24), PenguPlay's sign-in prompt is another."""
    try:
        return 0 < float((probe.get("format") or {}).get("duration")) < 60
    except (TypeError, ValueError):
        return False


def expiry(url):
    """A googlevideo manifest names its own expiry (`/expire/<unix>/`); two hours if it does not."""
    match = re.search(r"/expire/(\d+)/", url)
    return int(match[1]) if match else time.time() + 7200


def provisional_probe(meta, video=None):
    """Explicitly provisional bootstrap data, replaced by measured data on open.

    Catalogs contain no codec facts. These deliberately configured assumptions
    keep Rex's probe-gated rows visible; they are not a claim of verification.
    """
    value = {"format": {"format_name": "matroska,webm", "tags": {"comment": "provisional; awaiting playback probe"}},
             "streams": [{"index": 0, "codec_type": "video", "codec_name": "h264", "width": 1920, "height": 1080, "pix_fmt": "yuv420p"},
                         {"index": 1, "codec_type": "audio", "codec_name": "aac", "channels": 2, "sample_rate": "48000"}]}
    runtime = str((video or {}).get("runtime") or meta.get("runtime") or "")
    minutes = re.fullmatch(r"(\d+(?:\.\d+)?)(?: min)?", runtime.strip())
    if minutes:
        value["format"]["duration"] = str(float(minutes[1]) * 60)
    return value


def stremio_item(config, catalog, vid, imdb, meta, video, probe, extension):
    """One feed item (`docs/feed-api.md`): placed by its IMDb id, dressed by the catalog. A live
    channel has no IMDb id (`imdb` is the addon's own id): it goes unplaced, named by `display`."""
    path = "%s/%s/%s.%s" % (catalog["directory"], catalog["slug"], vid, extension)
    held, file = "st-" + vid, path
    if config.get("collections") and catalog["type"] != "tv" and imdb:
        # One id per library, whichever catalog holds the title: when the one holding it stops
        # listing it and the next takes over, rex keeps its row (and watch state) on that id. Its
        # file is its own too: rex refuses a new id for a file another id has.
        rest = vid[len(catalog["slug"]) + 1:]
        held, file = "stc-%s-%s" % (catalog["directory"], rest), "%s/%s.%s" % (catalog["directory"], rest, extension)
    pushed = {
        "id": held,
        "path": path,
        "file": "%s/%s" % (config["mount"].rstrip("/"), file),
        "name": meta.get("name") or imdb or str(meta.get("id")),
        "release": "stremio:%s" % (imdb or meta.get("id")),
        "version_group": "stremio:" + hashlib.sha256(vid.encode()).hexdigest(),
        "media_info": probe,
    }
    if catalog["type"] != "tv" and imdb:
        pushed["ids"] = {"imdb": imdb}
    size = (probe.get("format") or {}).get("size")
    try:
        size = int(size) if size else None
    except (TypeError, ValueError):
        size = None
    if size and extension != "m3u8":
        pushed["size"] = size
    released = lambda value: str(value or "")[:10] if re.match(r"\d{4}-\d{2}-\d{2}", str(value or "")) else None
    year = re.match(r"\d{4}", str(meta.get("year") or meta.get("releaseInfo") or ""))
    if catalog["type"] == "tv":
        display = {"title": meta.get("name"), "summary": meta.get("description"),
                   "thumb": meta.get("poster") or meta.get("logo"), "art": meta.get("background")}
    elif catalog["type"] == "movie":
        pushed["kind"] = "movie"
        display = {"title": meta.get("name"), "summary": meta.get("description"), "thumb": meta.get("poster"),
                   "art": meta.get("background"), "date": released(meta.get("released")) or (year and year[0])}
    else:
        pushed.update(kind="episode", season=video["season"], episode=video["episode"])
        display = {"title": video.get("name") or video.get("title"), "summary": video.get("overview") or video.get("description"),
                   "thumb": video.get("thumbnail"), "date": released(video.get("released") or video.get("firstAired")),
                   "show": {"title": meta.get("name"), "summary": meta.get("description"), "poster": meta.get("poster"),
                            "art": meta.get("background")}}
    pushed["display"] = prune(display)
    return pushed


def prune(value):
    if isinstance(value, dict):
        kept = {key: prune(inner) for key, inner in value.items() if inner not in (None, "", {})}
        return {key: inner for key, inner in kept.items() if inner not in (None, "", {})}
    return value


class StreamSearch:
    """A bounded search whose later results can arrive while a candidate is probed."""
    def __init__(self, addons, ask, control=None):
        self.condition = threading.Condition()
        self.control = control
        self.deadline = time.monotonic() + SEARCH_TIMEOUT
        self.answers = {}
        self.pending = len(addons)
        for index, pair in enumerate(addons):
            threading.Thread(target=self.fetch, args=(index, pair, ask),
                             name="stream-search", daemon=True).start()

    def fetch(self, index, pair, ask):
        try:
            answer = ask(pair)
        except Exception:
            answer = []
        with self.condition:
            if time.monotonic() <= self.deadline and not (self.control and self.control.cancelled.is_set()):
                self.answers[index] = answer
            self.pending -= 1
            self.condition.notify_all()


    def __len__(self):
        with self.condition:
            return sum(len(answer) for answer in self.answers.values())

    def candidates(self, config, pinned, refused, deadline=None):
        deadline = self.deadline if deadline is None else min(deadline, self.deadline)
        seen = set(refused)
        while True:
            with self.condition:
                streams = [stream for index in sorted(self.answers)
                           for stream in self.answers[index]]
                choices = [stream for stream in ranked(streams, config, pinned)
                           if stream_key(stream) not in seen]
                if not choices:
                    remaining = deadline - time.monotonic()
                    if not self.pending or remaining <= 0:
                        return
                    self.condition.wait(remaining)
                    continue
            for stream in choices:
                key = stream_key(stream)
                if key not in seen:
                    seen.add(key)
                    yield stream


class WarmControl:
    """One detail-page search, with provider processes that can be stopped on navigation."""
    def __init__(self):
        self.cancelled = threading.Event()
        self.guard = threading.Lock()
        self.processes = set()
        self.playback = False

    def promote(self):
        with self.guard:
            self.playback = True

    def cancel(self):
        self.cancelled.set()
        with self.guard:
            for process in tuple(self.processes):
                if process.poll() is None:
                    try:
                        process.terminate()
                    except ProcessLookupError:
                        pass

    def get_json(self, url):
        if self.cancelled.is_set():
            return {}
        process = subprocess.Popen([sys.executable, "-c", WARM_FETCH_SCRIPT], stdin=subprocess.PIPE,
                                   stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        with self.guard:
            self.processes.add(process)
            if self.cancelled.is_set():
                if process.poll() is None:
                    try:
                        process.terminate()
                    except ProcessLookupError:
                        pass
        try:
            try:
                output, _ = process.communicate(input=(url + "\n").encode(), timeout=31)
            except subprocess.TimeoutExpired:
                process.kill()
                process.communicate()
                return {}
            if process.returncode or len(output) > MAX_JSON_BYTES or self.cancelled.is_set():
                return {}
            return json.loads(output)
        finally:
            with self.guard:
                self.processes.discard(process)


class Sync:
    def __init__(self, config):
        self.config = config
        self.wake = threading.Event()
        self.hosts, self.hosts_lock = {}, threading.Lock()
        self.retry_soon = False
        self.status = "not synced yet"
        self.cache, self.locks, self.guard = {}, {}, threading.Lock()
        self.cache_locks = {}
        self.prepared = {}
        self.stream_searches = collections.OrderedDict()
        self.playback_searches = collections.OrderedDict()
        self.warm_item = None
        self.warm_control = None
        self.prefetch_pool = ThreadPoolExecutor(max_workers=2, thread_name_prefix="next-episode")
        self.version_pool = ThreadPoolExecutor(max_workers=1, thread_name_prefix="stream-versions")
        self.rd_library_ignore = LibraryIgnore() if config.get("exclude_rd_library") else None
        self.playback_publication_pool = ThreadPoolExecutor(max_workers=1, thread_name_prefix="playback-feed")
        self.prefetching = set()
        self.versioning = set()
        self.playback_started = {}
        # The headers each item's link is asked with, and the links its playlists name, which the
        # relay fetches with them (`relayed`): no other URL is fetched for anyone.
        self.via, self.relayed = {}, {}
        self.config_guard = threading.RLock()
        # Feed publication and settings commits share this lock. Readers never take it, so a
        # stalled rex request cannot stop the relay or settings page from serving.
        self.publication_lock = threading.RLock()
        self.snapshot_playbacks = None
        self.poster_lock = threading.Lock()
        self.poster_schedule_lock = threading.Lock()
        self.poster_pending = None
        self.poster_running = False
        self.config_version = 0
        # Set by a save on the settings page: the next complete snapshot may remove more than half
        # of what rex holds (catalogs unticked, catalogs turned into collections), which rex
        # refuses (409) unless forced. A start never forces, so rex's guard still holds then.
        self.force_next = False
        self.catalog_incomplete = False
        # A sync's titles held by a catalog, `(directory, type, imdb)`, and the IMDb ids the last
        # catalog listed: with `collections` on, one title per library (`catalog_items`).
        self.taken, self.catalog_listed = set(), set()

    def path(self, kind, vid, config=None, version=None):
        config = self.config if config is None else config
        if version is None:
            os.makedirs(os.path.join(config["cache"], kind), exist_ok=True)
        else:
            with self.config_guard:
                current = self.config_version == version
            if current:
                os.makedirs(os.path.join(config["cache"], kind), exist_ok=True)
        return os.path.join(config["cache"], kind, vid + ".json")

    def cached(self, kind, vid, make, config=None, version=None):
        path = self.path(kind, vid, config, version)
        lock = self.record_lock(path)
        with lock:
            try:
                with open(path) as handle:
                    return json.load(handle)
            except FileNotFoundError:
                pass
        value = make()
        with lock:
            if not os.path.exists(path):
                if version is None:
                    write_json(path, value)
                else:
                    with self.config_guard:
                        if self.config_version == version:
                            write_json(path, value)
                return value
            with open(path) as handle:
                return json.load(handle)

    def record_lock(self, path):
        with self.guard:
            return self.cache_locks.setdefault(path, threading.RLock())

    def cache_write(self, path, value, version=None):
        """Write one cache record under its own lock; never hold it during a probe or relay ask."""
        lock = self.record_lock(path)
        with lock:
            if version is not None:
                with self.config_guard:
                    if self.config_version != version:
                        return False
                    write_json(path, value)
            else:
                write_json(path, value)
        return True

    def cache_update(self, path, fields, version=None):
        """Merge a small info-record update while holding its file lock."""
        lock = self.record_lock(path)
        with lock:
            if version is not None:
                with self.config_guard:
                    if self.config_version != version:
                        return False
                    return self._cache_update_locked(path, fields)
            return self._cache_update_locked(path, fields)

    @staticmethod
    def _cache_update_locked(path, fields):
        try:
            with open(path) as handle:
                current = json.load(handle)
        except (FileNotFoundError, ValueError, TypeError):
            current = {}
        if not isinstance(current, dict):
            current = {}
        current.update(fields)
        write_json(path, current)
        return True

    def cache_remove(self, path, version=None):
        lock = self.record_lock(path)
        with lock:
            if version is not None:
                with self.config_guard:
                    if self.config_version != version:
                        return False
                    return self._cache_remove_locked(path)
            return self._cache_remove_locked(path)

    @staticmethod
    def _cache_remove_locked(path):
        try:
            os.unlink(path)
        except FileNotFoundError:
            pass
        return True

    def store_cache(self, version, vid, value, headers=None):
        with self.config_guard:
            if self.config_version != version:
                return
            with self.guard:
                self.cache[vid] = value
                self.via[vid] = headers or {}

    def imdb_of(self, kind, sid, config, version):
        """The IMDb id of a catalog item known by another id, as a meta addon names it: an added
        addon that serves meta for it, else the TMDB addon for a `tmdb:` id. Kept once found."""
        def ask():
            bases = [addon_base(addon["url"]) for addon in config["addons"]
                     if isinstance(addon, dict) and isinstance(addon.get("url"), str) and serves(addon_manifest(addon), "meta", kind, sid)]
            if sid.startswith("tmdb:"):
                bases.append(TMDB_META)
            for base in bases:
                try:
                    found = get_json("%s/meta/%s/%s.json" % (base, kind, urllib.parse.quote(sid)), SEARCH_TIMEOUT).get("meta") or {}
                except Exception as error:
                    LOG.info("%s: %s: %s", sid, safe_url(base), safe_error(error))
                    continue
                imdb = str(found.get("imdb_id") or "") if isinstance(found, dict) else ""
                if re.fullmatch(r"tt\d+", imdb):
                    return {"imdb": imdb}
            raise LookupError("no meta addon names an IMDb id")
        try:
            return self.cached("ids", re.sub(r"[^A-Za-z0-9_-]", "-", "%s-%s" % (kind, sid)), ask, config, version)["imdb"]
        except Exception:
            return ""

    def own_meta(self, kind, sid, config):
        """A series only its addon knows, with its episodes (`videos`), from an addon that serves
        meta for its id."""
        for addon in config["addons"]:
            if not (isinstance(addon, dict) and isinstance(addon.get("url"), str) and serves(addon_manifest(addon), "meta", kind, sid)):
                continue
            try:
                found = get_json("%s/meta/%s/%s.json" % (addon_base(addon["url"]), kind, urllib.parse.quote(sid)), 60).get("meta")
            except Exception as error:
                LOG.warning("%s: %s", sid, safe_error(error))
                continue
            if isinstance(found, dict) and isinstance(found.get("videos"), list) and found["videos"]:
                return found
        return None

    def refuse(self, vid, config, version):
        """Set aside for a day the stream an item is pinned to, and what was learned from it.
        False when nothing is pinned (no stream opened at all)."""
        path = self.path("info", vid, config, version)
        try:
            with open(path) as handle:
                info = json.load(handle)
        except (OSError, ValueError):
            return False
        if not isinstance(info, dict) or not info.get("stream"):
            return False
        now = time.time()
        refused = [entry for entry in info.get("refused") or [] if isinstance(entry, dict) and now - entry.get("at", 0) < 86400]
        refused = (refused + [{"key": info["stream"], "at": now}])[-20:]
        LOG.warning("%s: %s set aside, trying the next stream", vid, safe_stream_key(info["stream"]))
        self.cache_update(path, {"stream": None, "refused": refused}, version)
        self.cache_remove(self.path(PROBES, vid, config, version), version)
        with self.guard:
            self.cache.pop(vid, None)
        return True

    def remember(self, vid, url):
        """A link an item's playlist names, as the relay path it is fetched through."""
        token = hashlib.sha256(url.encode()).hexdigest()[:20]
        extension = re.search(r"\.([A-Za-z0-9]{1,5})$", urllib.parse.urlsplit(url).path)
        with self.guard:
            links = self.relayed.setdefault(vid, collections.OrderedDict())
            links[token] = url
            links.move_to_end(token)
            while len(links) > 4096:  # a live playlist names new segments for ever
                links.popitem(last=False)
        return "/_relay/%s/%s.%s" % (vid, token, extension[1] if extension else "bin")

    def relayed_link(self, vid, token):
        with self.guard:
            return (self.relayed.get(vid) or {}).get(token), self.via.get(vid) or {}

    def stale(self, version):
        with self.config_guard:
            return version is not None and self.config_version != version

    def publish(self, version, method, path, body, config):
        """Make one feed request only while its generation is still current.

        The publication lock serializes this request with a settings commit, but the catalog
        scan and probes happen before this method is entered. No config lock is held over I/O.
        """
        with self.publication_lock:
            with self.config_guard:
                if self.config_version != version:
                    return None
            if isinstance(body, dict) and "items" in body:
                body = dict(body, items=self.lazy_chunk(body["items"], config, version))
            answer = self.rex(method, path, body, config)
        self.schedule_collection_posters(config)
        return answer

    def rex(self, method, path, body=None, config=None):
        config = self.config if config is None else config
        headers = {"Content-Type": "application/json", "Accept": "application/json"}
        if config.get("rex_token"):
            headers["X-Plex-Token"] = config["rex_token"]
        request = urllib.request.Request(rex_endpoint(config["rex_url"], path), method=method,
                                         data=None if body is None else json.dumps(body).encode(),
                                         headers=headers)
        with urllib.request.urlopen(request, timeout=600) as response:
            answer = response_json(response)
        if not isinstance(answer, dict):
            raise ValueError("rex response must be an object")
        return answer

    def register(self, config=None):
        config = self.config if config is None else config
        directories = {}
        for catalog in config["catalogs"]:
            kind = REX_KINDS[catalog["type"]]
            directories.setdefault(catalog["directory"], {"name": catalog["directory"]}).setdefault(kind, catalog["library"])
        directories.setdefault("ondemand-movies", {"name": "ondemand-movies"})["movies"] = config["ondemand_movies_library"]
        directories.setdefault("ondemand-tv", {"name": "ondemand-tv"})["shows"] = config["ondemand_tv_library"]
        answer = self.rex("PUT", "/rex/sources/" + config["source"],
                          {"url": config["relay_url"], "mount": config["mount"], "directories": list(directories.values()),
                           "detail_search": True}, config)
        for ignored in answer.get("ignored") or []:
            if not isinstance(ignored, dict):
                continue
            LOG.warning("rex ignored %s: %s", safe_error(ignored.get("entry")), safe_error(ignored.get("reason")))
        self.set_ondemand_library_visibility(config)

    def set_ondemand_library_visibility(self, config=None):
        """Apply the configured Rex visibility to the dedicated virtual-card sections."""
        config = self.config if config is None else config
        answer = self.rex("GET", "/library/sections", config=config)
        rows = ((answer.get("MediaContainer") or {}).get("Directory") or [])
        if isinstance(rows, dict):
            rows = [rows]
        wanted = {
            ("movie", "ondemand-movies"): config["ondemand_movies_library"],
            ("show", "ondemand-tv"): config["ondemand_tv_library"],
        }
        for row in rows:
            if not isinstance(row, dict):
                continue
            kind = "show" if row.get("type") in ("show", "2") else "movie"
            key = row.get("key")
            locations = row.get("Location") or []
            if isinstance(locations, dict):
                locations = [locations]
            directories = [str(location.get("path", "")).rstrip("/").rsplit("/", 1)[-1]
                           for location in locations if isinstance(location, dict)]
            directory = next((name for name in wanted if name[0] == kind and name[1] in directories), None)
            if directory is None or not isinstance(key, (str, int)):
                continue
            section = str(key).rstrip("/").rsplit("/", 1)[-1]
            if section.isdigit():
                title = wanted[directory]
                if row.get("title") != title:
                    agent = "tv.plex.agents.series" if kind == "show" else "tv.plex.agents.movie"
                    query = urllib.parse.urlencode({"agent": agent, "type": kind, "name": title})
                    self.rex("PUT", "/library/sections/%s?%s" % (section, query), config=config)
                hidden = "2" if config["hide_ondemand_libraries"] else "0"
                self.rex("PUT", "/library/sections/%s/prefs?hidden=%s" % (section, hidden), config=config)

    def streams(self, kind, sid, config=None, also=(), warm_control=None):
        """Every stream the addons that serve this item give, in the addons' order. Each addon is
        asked by the id it serves: its catalog's own id (`also`) first, as Stremio asks by the id
        a catalog gave, else the item's IMDb id."""
        config = self.config if config is None else config
        addons = []
        for addon in config["addons"]:
            if isinstance(addon, dict) and isinstance(addon.get("url"), str):
                named = next((one for one in [*also, sid] if serves(addon_manifest(addon), "stream", kind, one)), None)
                if named:
                    addons.append((addon, named))

        def ask(pair):
            addon, sid = pair
            manifest = addon_manifest(addon)
            try:
                target = "%s/stream/%s/%s.json" % (addon_base(addon["url"]), kind, urllib.parse.quote(sid))
                answer = warm_control.get_json(target) if warm_control else self.ask_addon(target, config)
                streams = answer.get("streams") if isinstance(answer, dict) else []
                LOG.debug("SEARCH addon=%s episode=%s candidates=%d", manifest.get("name") or "addon", sid, len(streams) if isinstance(streams, list) else 0)
                return [stream for stream in streams or [] if isinstance(stream, dict)] if isinstance(streams, list) else []
            except Exception as error:
                LOG.warning("%s: %s: %s", sid, manifest.get("name") or "addon", safe_error(error))
                return []
        if config.get("lazy_catalogs"):
            key = (self.config_version, kind, sid, tuple(also))
            with self.guard:
                search = self.stream_searches.get(key)
                expired_warm = (search is not None and warm_control is None and search.control
                                and time.monotonic() >= search.deadline and not len(search))
                if search is None or time.monotonic() > search.deadline + PROBE_TIMEOUT or (search.control and search.control.cancelled.is_set()) or expired_warm:
                    if expired_warm:
                        search.control.cancel()
                    search = StreamSearch(addons, ask, warm_control)
                    self.stream_searches[key] = search
                    self.stream_searches.move_to_end(key)
                    while len(self.stream_searches) > 128:
                        self.stream_searches.popitem(last=False)
                elif warm_control is None and search.control and search.pending:
                    # Playback joining a detail search gets its own full search window.
                    # The provider request stays in flight; no second request is queued.
                    search.control.promote()
                    with search.condition:
                        search.deadline = max(search.deadline, time.monotonic() + SEARCH_TIMEOUT)
                return search
        with ThreadPoolExecutor(max(len(addons), 1)) as pool:
            return [stream for answer in pool.map(ask, addons) for stream in answer]

    def ask_addon(self, url, config):
        """A stream addon's answer, its host paced and its refusals waited out (see REFUSALS).
        A host that keeps refusing is not asked until `retry_minutes` pass: {} meanwhile."""
        host = urllib.parse.urlsplit(url).netloc
        while True:
            with self.hosts_lock:
                state = self.hosts.setdefault(host, {"next": 0.0, "refusals": 0})
                now = time.time()
                if state["refusals"] >= REFUSALS and state["next"] > now:
                    self.retry_soon = True
                    return {}
                start = max(now, state["next"])
                state["next"] = start + config["stream_interval_seconds"]
                booked = state.get("refused", 0)
            time.sleep(start - now)
            with self.hosts_lock:
                # Items are asked for in parallel (`probe_workers`): an ask that took its turn before
                # a refusal takes a new turn after it, or the asks already queued would each be
                # refused and the host given up for the pass at once.
                if state.get("refused", 0) != booked:
                    continue
            try:
                asked_at = time.time()
                answer = get_json(url, 30)
                if isinstance(answer, dict) and "streams" in answer and not isinstance(answer["streams"], list):
                    raise Refused("streams is not an array")  # 111477's while its own index is throttled
            except (urllib.error.HTTPError, Refused) as error:
                if isinstance(error, urllib.error.HTTPError) and error.code != 429:
                    raise
                with self.hosts_lock:
                    self.retry_soon = True
                    state["refusals"] += 1
                    if state["refusals"] >= REFUSALS:
                        state["next"] = time.time() + config["retry_minutes"] * 60
                        state["refused"] = state.get("refused", 0) + 1
                        LOG.warning("%s refused %d times in a row (%s): not asked again before %s", host, state["refusals"],
                                    safe_error(error), time.strftime("%H:%M", time.localtime(state["next"])))
                        return {}
                    wait = retry_after(error.headers.get("Retry-After")) if isinstance(error, urllib.error.HTTPError) else None
                    wait = min(BACKOFF * 2 ** (state["refusals"] - 1) if wait is None else wait, MAX_BACKOFF)
                    state["next"] = time.time() + wait  # turns taken before now are taken again
                    state["refused"] = state.get("refused", 0) + 1
                LOG.info("%s refused (%s): asking again in %.0f s", host, safe_error(error), wait)
                continue
            with self.hosts_lock:
                state["refusals"] = 0
            if self.rd_library_ignore and isinstance(answer, dict) and isinstance(answer.get("streams"), list):
                self.rd_library_ignore.note(answer["streams"], asked_at)
            return answer

    def warm_search(self, vid):
        # An on-demand episode may be catalogued by Rex before its virtual file
        # has ever been opened. Register its lightweight info now so the season
        # listing can start the provider search ahead of Play.
        with self.config_guard:
            catalogs = copy.deepcopy(self.config["catalogs"])
        owner = max((catalog for catalog in catalogs if vid.startswith(catalog["slug"] + "-")),
                    key=lambda catalog: len(catalog["slug"]), default=None)
        if owner:
            self.route_vid("/%s/%s/%s.mkv" % (owner["directory"], owner["slug"], vid))
        with self.config_guard:
            config = copy.deepcopy(self.config)
        try:
            with open(self.path("info", vid)) as handle:
                info = json.load(handle)
        except (OSError, ValueError):
            return
        if not info.get("kind") or not info.get("sid") or info.get("variant_stream"):
            return
        with self.guard:
            if self.warm_item == vid:
                return
            if self.warm_control and not self.warm_control.playback:
                self.warm_control.cancel()
            control = WarmControl()
            self.warm_item, self.warm_control = vid, control
        self.streams(info["kind"], info["sid"], config, info.get("also") or (), control)
        LOG.info("SEARCH warm item=%s", vid)

    def resolve(self, vid):
        with self.config_guard:
            config, version = copy.deepcopy(self.config), self.config_version
        return self._resolve(vid, config, version)

    def _resolve(self, vid, config, version):
        """The link an item plays from now: the best stream that opens. Cached an hour."""
        with self.guard:
            lock = self.locks.setdefault(vid, threading.Lock())
        with lock:  # one ask per item; other items resolve meanwhile
            started = time.monotonic()
            with self.guard:
                url, good_until = self.cache.get(vid, (None, 0))
            if time.time() < good_until:
                with self.guard:
                    headers = self.via.get(vid) or {}
                checked = opens(url, headers)
                if checked:
                    self.store_cache(version, vid, (checked, good_until), headers)
                    return checked
                with self.guard:
                    self.cache.pop(vid, None)
            with open(self.path("info", vid, config, version)) as handle:
                info = json.load(handle)
            wanted_stream = info.get("variant_stream")
            refused = {entry.get("key") for entry in info.get("refused") or []
                       if isinstance(entry, dict) and time.time() - entry.get("at", 0) < 86400}
            if config.get("lazy_catalogs") and time.monotonic() - started >= SEARCH_TIMEOUT:
                raise RuntimeError("stream lookup timed out after %ss" % SEARCH_TIMEOUT)
            streams = self.streams(info["kind"], info["sid"], config, info.get("also") or ())
            if not wanted_stream:
                with self.guard:
                    self.playback_searches[vid] = streams
                    self.playback_searches.move_to_end(vid)
                    while len(self.playback_searches) > 128:
                        self.playback_searches.popitem(last=False)
            LOG.info("TIMING providers item=%s duration_s=%.3f initial_candidates=%d (providers may still be searching)", vid, time.monotonic()-started, len(streams))
            candidates = streams.candidates(config, info.get("stream"), refused, started + SEARCH_TIMEOUT) if isinstance(streams, StreamSearch) else ranked(streams, config, info.get("stream"))
            for stream in candidates:
                if wanted_stream and stream_key(stream) != wanted_stream:
                    continue
                if stream_key(stream) in refused:
                    continue
                opened = time.monotonic()
                if config.get("lazy_catalogs"):
                    remaining = SEARCH_TIMEOUT - (opened - started)
                    if remaining <= 0:
                        raise RuntimeError("stream search timed out after %ss" % SEARCH_TIMEOUT)
                    url = opens(stream["url"], request_headers(stream), timeout=remaining)
                else:
                    url = opens(stream["url"], request_headers(stream))
                LOG.info("TIMING open item=%s duration_s=%.3f result=%s", vid, time.monotonic()-opened, "ok" if url else "unavailable")
                if not url:
                    continue
                if not info.get("stream"):  # the first one that opens is what the probe describes
                    self.cache_update(self.path("info", vid, config, version), {"stream": stream_key(stream)}, version)
                elif stream_key(stream) != info["stream"]:
                    # The stream rex was told about is gone, and this one can differ (codec,
                    # container, a live channel's other mirror and its stream layout), so this
                    # play may fail. It is pinned, probed and pushed again on a sync started now.
                    LOG.warning("%s: probed stream gone, playing %s", vid, safe_stream_key(stream_key(stream)))
                    self.cache_update(self.path("info", vid, config, version), {"stream": stream_key(stream)}, version)
                    self.cache_remove(self.path(PROBES, vid, config, version), version)
                    self.wake.set()
                self.store_cache(version, vid, (url, max(time.time(), min(expiry(stream["url"]), expiry(url)) - 3600)),
                                 request_headers(stream))
                return url
            raise RuntimeError("no stream addon has a stream that opens")

    def route_vid(self, path):
        """Return an item id only for a configured directory, catalog and extension."""
        match = re.fullmatch(r"/([A-Za-z0-9_-]+)/([A-Za-z0-9_-]+)/([A-Za-z0-9_-]+)\.([A-Za-z0-9]+)", path)
        if not match:
            return None
        directory, catalog_slug, vid, extension = match.groups()
        with self.config_guard:
            catalogs, cache = copy.deepcopy(self.config["catalogs"]), self.config["cache"]
        catalog = next((catalog for catalog in catalogs
                        if catalog["directory"] == directory and catalog["slug"] == catalog_slug), None)
        if not catalog:
            return None
        # An item id is its catalog's slug and the item's (an IMDb id, or an addon's own): the
        # longest slug it starts with is its catalog's (`cat-2-tt1` is cat-2's, not cat's).
        owner = max((other["slug"] for other in catalogs if vid.startswith(other["slug"] + "-")), key=len, default=None)
        if owner != catalog_slug or len(vid) <= len(catalog_slug) + 1:
            return None
        info_path = os.path.join(cache, "info", vid + ".json")
        if not os.path.isfile(info_path):
            # Rex recommendation cards name a movie by IMDb id. Register the
            # virtual file on first access; playback still searches addons and
            # probes a real stream in prepare().
            match_id = re.fullmatch(re.escape(catalog_slug) + r"-(tt\d+)-ondemand", vid)
            episode_id = re.fullmatch(re.escape(catalog_slug) + r"-(tt\d+)-s(\d+)e(\d+)-ondemand", vid)
            if extension != "mkv" or not ((match_id and catalog["type"] == "movie")
                                          or (episode_id and catalog["type"] == "series")):
                return None
            imdb = (match_id or episode_id)[1]
            item_path = "%s/%s/%s.mkv" % (directory, catalog_slug, vid)
            item = {"id": "st-" + vid, "path": item_path,
                    "file": self.config["mount"].rstrip("/") + "/" + item_path,
                    "name": imdb, "release": "stremio:" + imdb,
                    "version_group": "stremio:" + hashlib.sha256(vid.encode()).hexdigest(),
                    "media_info": provisional_probe({"name": imdb}),
                    "ids": {"imdb": imdb}, "kind": "movie" if match_id else "episode",
                    "display": {"title": imdb}}
            if episode_id:
                item["season"], item["episode"] = int(episode_id[2]), int(episode_id[3])
                sid = "%s:%s:%s" % (imdb, episode_id[2], episode_id[3])
            else:
                sid = imdb
            self.cached("info", vid, lambda: {
                "kind": catalog["type"], "sid": sid, "also": [],
                "catalog": catalog, "item": item, "next": None,
                "extension": "mkv"})
        if extension in ("stream", "probe"):
            return vid
        try:
            with open(info_path) as handle:
                info = json.load(handle)
            if not isinstance(info, dict) or info.get("kind") != catalog["type"]:
                return None
            expected = info.get("extension")
            if not expected:
                probe_path = os.path.join(cache, PROBES, vid + ".json")
                with open(probe_path) as handle:
                    probe = json.load(handle)
                expected = CONTAINERS.get((probe.get("format") or {}).get("format_name"))
            return vid if expected == extension else None
        except (AttributeError, OSError, ValueError, TypeError):
            return None

    def probe(self, vid, catalog, config=None):
        config = self.config if config is None else config
        url = rex_endpoint(config["relay_url"], "/%s/%s/%s.probe" % (catalog["directory"], catalog["slug"], vid))
        started = time.monotonic()
        flags = lenient_hls(config["ffprobe"])
        for attempt in range(2):
            budget = PROBE_TIMEOUT if config.get("lazy_catalogs") else 300
            out = subprocess.run([config["ffprobe"], "-v", "error", *flags, "-print_format", "json",
                                  "-show_format", "-show_streams", "-show_chapters", url], capture_output=True,
                                 timeout=max(.001, budget - (time.monotonic() - started)))
            if out.returncode == 0:
                return json.loads(out.stdout)
            error = out.stderr.decode(errors="replace").strip()[-300:] or "ffprobe failed"
            if attempt or "Server returned 5XX" not in error:
                raise RuntimeError(error)
            if config.get("lazy_catalogs") and time.monotonic() - started + PROBE_RETRY_SECONDS >= PROBE_TIMEOUT:
                raise RuntimeError(error)
            time.sleep(PROBE_RETRY_SECONDS)

    def measured_item(self, item, probe):
        extension = CONTAINERS.get((probe.get("format") or {}).get("format_name"))
        if not extension:
            raise RuntimeError("probe found an unsupported container")
        result = dict(item, media_info=probe)
        result["path"] = item["path"].rsplit(".", 1)[0] + "." + extension
        result["file"] = item["file"].rsplit(".", 1)[0] + "." + extension
        size = (probe.get("format") or {}).get("size")
        result.pop("size", None)
        if size and extension != "m3u8":
            result["size"] = int(size)
        return result

    def prepare(self, vid, *, prefetch=True):
        """Measure on play; probe transport bypasses preparation to avoid recursion."""
        with self.config_guard:
            config, version = copy.deepcopy(self.config), self.config_version
        with self.guard:
            lock = self.locks.setdefault("prepare:" + vid, threading.Lock())
        with lock:
            for attempt in range(3):
                url = self.resolve(vid)
                with open(self.path("info", vid, config, version)) as handle:
                    info = json.load(handle)
                if self.prepared.get((version, vid)) == url:
                    LOG.debug("PROBE item=%s already prepared; cached stream still opens", vid)
                    break
                try:
                    LOG.info("PROBE start %s item=%s attempt=%d mode=%s", self.episode_label(vid), vid, attempt+1, "playback" if prefetch else "next-episode")
                    probe = self.probe(vid, info["catalog"], config)
                    LOG.info("PROBE complete item=%s container=%s tracks=%d", vid, (probe.get("format") or {}).get("format_name"), len(probe.get("streams") or []))
                    if info["kind"] == "tv":
                        probe = dict(probe, format=dict(probe.get("format") or {}))
                        probe["format"].pop("duration", None)
                    elif placeholder(probe):
                        raise RuntimeError("placeholder clip")
                    if not any(t.get("codec_type") == "video" for t in probe.get("streams") or []):
                        raise RuntimeError("probe returned no picture")
                    measured = self.measured_item(info["item"], probe)
                except subprocess.TimeoutExpired:
                    # A slow stream must fail this play rather than spending another ten
                    # seconds on each fallback. subprocess.run kills and reaps ffprobe.
                    self.refuse(vid, config, version)
                    raise RuntimeError("stream probe timed out after %ss" % PROBE_TIMEOUT)
                except Exception:
                    if attempt == 2 or not self.refuse(vid, config, version):
                        raise
                    continue
                with self.config_guard:
                    if self.config_version != version:
                        raise RuntimeError("settings changed during playback preparation")
                self.cache_write(self.path(PROBES, vid, config, version), probe, version)
                self.cache_update(self.path("info", vid, config, version), {"extension": measured["path"].rsplit(".", 1)[-1]}, version)
                # Feed publication can wait behind a large Rex/Zurg update. Keep
                # the episode request free so Rex's part read does not time out;
                # publish the measured tracks in the background.
                if prefetch:
                    self.playback_publication_pool.submit(self.publish_playback, vid, measured, config, version)
                else:
                    self.publish_playback(vid, measured, config, version)
                self.prepared[(version, vid)] = url
                LOG.info("PLAYBACK prepared item=%s mode=%s", vid, "foreground" if prefetch else "prefetch")
                break
        return url

    def publish_playback(self, vid, measured, config, version):
        try:
            with self.publication_lock:
                if self.stale(version):
                    return
                answer = self.rex("POST", "/rex/feed/%s/items" % config["source"], {"items": [measured]}, config)
                if answer.get("rejected"):
                    raise RuntimeError("Rex rejected the measured item")
                if self.snapshot_playbacks is not None:
                    self.snapshot_playbacks[measured["id"]] = measured
            LOG.info("PLAYBACK feed ready item=%s", vid)
        except Exception as error:
            LOG.warning("PLAYBACK feed failed item=%s error=%s", vid, safe_error(error))
            raise

    def episode_label(self, vid):
        try:
            with open(self.path("info", vid)) as handle:
                info = json.load(handle)
            sid = info.get("sid", "")
            match = re.search(r":(\d+):(\d+)$", sid)
            title = (info.get("item") or {}).get("name") or vid
            return "%s S%02dE%02d" % (title, int(match[1]), int(match[2])) if match else title
        except (OSError, ValueError, TypeError):
            return vid

    def started_stream(self, vid):
        # Called only after a media body write, never HEAD, playlist or ffprobe.
        now = time.monotonic()
        with self.guard:
            if now - self.playback_started.get(vid, -3600) < 300:
                return
            self.playback_started[vid] = now
            if len(self.playback_started) > 2048:
                self.playback_started = {key: at for key, at in self.playback_started.items() if now-at < 300}
        LOG.info("PLAYBACK feeding Rex: %s item=%s first media bytes sent", self.episode_label(vid), vid)
        if not re.search(r"-v[0-9a-f]{12}$", vid):
            self.prepare_versions(vid)
        try:
            with open(self.path("info", vid)) as handle:
                info = json.load(handle)
            next_vid = info.get("next")
            if next_vid:
                LOG.info("NEXT_EPISODE playing=%s target=%s action=search-and-probe", self.episode_label(vid), self.episode_label(next_vid))
                self.prefetch(next_vid)
            else:
                LOG.info("NEXT_EPISODE item=%s no next episode in catalog", vid)
        except (OSError, ValueError) as error:
            LOG.warning("NEXT_EPISODE item=%s cannot read episode chain: %s", vid, safe_error(error))

    def prepare_versions(self, vid):
        """Try five other ranked streams only after the first media bytes were sent."""
        with self.guard:
            if vid in self.versioning:
                return
            self.versioning.add(vid)
            playback_search = self.playback_searches.pop(vid, None)

        def work():
            try:
                with self.config_guard:
                    config, version = copy.deepcopy(self.config), self.config_version
                with open(self.path("info", vid, config, version)) as handle:
                    base = json.load(handle)
                if not base.get("item") or not base.get("stream"):
                    return
                search = playback_search if playback_search is not None else self.streams(base["kind"], base["sid"], config, base.get("also") or ())
                if isinstance(search, StreamSearch):
                    with search.condition:
                        while search.pending and time.monotonic() < search.deadline:
                            search.condition.wait(max(.001, search.deadline - time.monotonic()))
                        streams = [stream for index in sorted(search.answers) for stream in search.answers[index]]
                else:
                    streams = search
                chosen = base.get("stream")
                seen = {chosen}
                seen.update(entry.get("key") for entry in base.get("refused") or []
                            if isinstance(entry, dict) and time.time() - entry.get("at", 0) < 86400)
                candidates = []
                for stream in ranked(streams, config):
                    key = stream_key(stream)
                    if key in seen:
                        continue
                    seen.add(key)
                    candidates.append((key, stream))
                    if len(candidates) == 5:
                        break
                if candidates:
                    # Let the initial stream buffer before opening and probing alternatives.
                    time.sleep(VERSION_PROBE_DELAY)
                for key, stream in candidates:
                    if self.stale(version):
                        return
                    suffix = hashlib.sha256(str(key).encode()).hexdigest()[:12]
                    variant = vid + "-v" + suffix
                    try:
                        opened = opens(stream["url"], request_headers(stream))
                        if not opened:
                            continue
                        item = dict(base["item"])
                        item["id"] = base["item"]["id"] + "-v" + suffix
                        item["release"] = base["item"]["release"] + ":v" + suffix
                        item["path"] = base["item"]["path"].rsplit("/", 1)[0] + "/" + variant + ".mkv"
                        item["file"] = config["mount"].rstrip("/") + "/" + item["path"]
                        info = {k: base[k] for k in ("kind", "sid", "also", "catalog") if k in base}
                        info.update(item=item, stream=key, variant_stream=key, extension="mkv")
                        self.cache_write(self.path("info", variant, config, version), info, version)
                        self.store_cache(version, variant, (opened, max(time.time(), min(expiry(stream["url"]), expiry(opened)) - 3600)), request_headers(stream))
                        probe = self.probe(variant, base["catalog"], config)
                        if base["kind"] == "tv":
                            probe = dict(probe, format=dict(probe.get("format") or {}))
                            probe["format"].pop("duration", None)
                        elif placeholder(probe):
                            raise RuntimeError("placeholder clip")
                        if not any(track.get("codec_type") == "video" for track in probe.get("streams") or []):
                            raise RuntimeError("probe returned no picture")
                        measured = self.measured_item(item, probe)
                        with self.publication_lock:
                            if self.stale(version):
                                return
                            answer = self.rex("POST", "/rex/feed/%s/items" % config["source"], {"items": [measured]}, config)
                            if answer.get("rejected"):
                                raise RuntimeError("Rex rejected version")
                            self.cache_write(self.path(PROBES, variant, config, version), probe, version)
                            self.cache_update(self.path("info", variant, config, version), {"extension": measured["path"].rsplit(".", 1)[-1]}, version)
                            with open(self.path("info", vid, config, version)) as handle:
                                latest = json.load(handle)
                            variants = list(latest.get("variants") or [])
                            if variant not in variants:
                                variants.append(variant)
                                self.cache_update(self.path("info", vid, config, version), {"variants": variants}, version)
                        LOG.info("VERSION ready item=%s candidate=%s", vid, suffix)
                    except Exception as error:
                        LOG.warning("VERSION failed item=%s candidate=%s error=%s", vid, suffix, safe_error(error))
            except Exception as error:
                LOG.warning("VERSION search failed item=%s error=%s", vid, safe_error(error))
            finally:
                with self.guard:
                    self.versioning.discard(vid)

        self.version_pool.submit(work)

    def published_versions(self, items, config, version):
        """Keep successfully measured versions in complete feed snapshots."""
        extras = []
        for item in items:
            vid = item["path"].rsplit("/", 1)[-1].rsplit(".", 1)[0]
            try:
                with open(self.path("info", vid, config, version)) as handle:
                    variants = json.load(handle).get("variants") or []
            except (OSError, ValueError, AttributeError):
                continue
            for variant in variants:
                try:
                    with open(self.path("info", variant, config, version)) as handle:
                        version_item = json.load(handle)["item"]
                    with open(self.path(PROBES, variant, config, version)) as handle:
                        probe = json.load(handle)
                    extras.append(self.measured_item(version_item, probe))
                except (OSError, ValueError, KeyError, RuntimeError):
                    continue
        return extras

    def prefetch(self, vid):
        # Only the immediate next episode; preparation by a prefetch never
        # schedules another, so opening episode one cannot resolve a season.
        with self.guard:
            if vid in self.prefetching:
                LOG.debug("NEXT_EPISODE item=%s already preparing", vid)
                return
            self.prefetching.add(vid)
        def work():
            started = time.monotonic()
            LOG.info("NEXT_EPISODE start %s item=%s searching/opening/probing", self.episode_label(vid), vid)
            try:
                self.prepare(vid, prefetch=False)
                LOG.info("NEXT_EPISODE ready %s item=%s duration_s=%.3f measured feed accepted by Rex", self.episode_label(vid), vid, time.monotonic()-started)
            except Exception as error:
                LOG.warning("NEXT_EPISODE failed %s item=%s duration_s=%.3f error=%s", self.episode_label(vid), vid, time.monotonic()-started, safe_error(error))
            finally:
                with self.guard:
                    self.prefetching.discard(vid)
        self.prefetch_pool.submit(work)

    def catalog_answer(self, catalog, config):
        answer = get_json(catalog["url"])
        if not config.get("lazy_catalogs") or not isinstance(answer, dict) or not isinstance(answer.get("metas"), list):
            return answer
        # Cinemeta is the fixed metadata source for these Popular catalogs. It need not be
        # registered as a stream addon merely to page its public catalog.
        supports_skip = catalog["url"].startswith(CINEMETA + "/catalog/")
        for addon in config["addons"]:
            if addon_base(addon["url"]) != catalog["url"].split("/catalog/", 1)[0]:
                continue
            for declaration in addon_manifest(addon).get("catalogs", []):
                if declaration.get("type") == catalog["type"] and declaration.get("id") == catalog["url"].rsplit("/", 1)[-1][:-5]:
                    supports_skip = "skip" in declaration.get("extraSupported", []) or any(isinstance(e, dict) and e.get("name") == "skip" for e in declaration.get("extra", []))
        if not supports_skip:
            return answer
        rows = list(answer["metas"])
        identity = lambda row: str(row.get("imdb_id") or row.get("id") or "") if isinstance(row, dict) else ""
        seen = {identity(row) for row in rows} - {""}
        offset = len(rows)
        while rows and len(seen) < catalog["limit"]:
            url = catalog["url"][:-5] + "/skip=%d.json" % offset
            try:
                page = get_json(url)
                if not isinstance(page, dict) or not isinstance(page.get("metas"), list):
                    raise ValueError("catalog page has no metas list")
            except Exception as error:
                return dict(answer, metas=rows, _incomplete=True)
            fresh = [row for row in page["metas"] if identity(row) and identity(row) not in seen]
            if not fresh:
                break
            rows.extend(fresh)
            seen.update(identity(row) for row in fresh)
            offset += len(page["metas"])
        return dict(answer, metas=rows)

    def catalog_items(self, catalog, config=None, version=None):
        """A catalog's films, or its series' episodes (Cinemeta's list of them), pushed by their
        IMDb ids so Plex names them; the catalog's own names and pictures are `display`, shown
        only until Plex names them. With `collections` on, a title an earlier catalog of the same
        library took (`self.taken`) is left to it; `self.catalog_listed` keeps the IMDb ids listed."""
        config = self.config if config is None else config
        self.catalog_listed = set()
        kind, limit = catalog["type"], catalog["limit"]
        complete = True
        answer = self.catalog_answer(catalog, config)
        complete = not answer.get("_incomplete", False) if isinstance(answer, dict) else False
        if not isinstance(answer, dict) or not isinstance(answer.get("metas"), list):
            raise ValueError("catalog response has no metas list")
        if not answer["metas"]:
            # An empty answer can be a provider outage. Keep the last feed rows until a
            # non-empty response proves that this catalog is really empty.
            complete = False
        wanted, skipped = [], 0
        titles = set()
        for meta in answer["metas"]:
            if not isinstance(meta, dict):
                complete = False
                continue
            if (len(titles) if config.get("lazy_catalogs") else len(wanted) + skipped) >= limit:
                continue
            if kind == "tv":
                # A channel is known only by the addon's own id (`ustv-…`, `pp-live:…`), which is
                # what its stream is asked by; the item id keeps only what a relay path can hold.
                if not isinstance(meta.get("id"), str) or not meta["id"]:
                    complete = False
                    continue
                if config.get("lazy_catalogs"):
                    if meta["id"] in titles:
                        continue
                    titles.add(meta["id"])
                wanted.append(("%s-%s" % (catalog["slug"], re.sub(r"[^A-Za-z0-9_-]", "-", meta["id"])), meta["id"], meta, None, (), None))
                continue
            own = meta["id"] if isinstance(meta.get("id"), str) else ""
            imdb = str(meta.get("imdb_id") or "")
            if not re.fullmatch(r"tt\d+", imdb):
                # An addon's own id can carry it (Cotonet's `cotonet:tt28942997`).
                found = re.search(r"(?<![A-Za-z0-9])tt\d{5,}(?!\d)", own)
                imdb = found[0] if found else (self.imdb_of(kind, own, config, version) if own else "")
            if not imdb and not own:
                complete = False
                continue
            if config.get("lazy_catalogs"):
                identity = imdb or own
                if identity in titles:
                    continue
                titles.add(identity)
            # Ids carry the catalog: one film in two catalogs is two items, unless catalogs are
            # collections, when the first catalog of its library to list it holds it.
            if imdb and config.get("collections"):
                self.catalog_listed.add(imdb)
                if (catalog["directory"], kind, imdb) in self.taken:
                    # A film another catalog holds still counts as one of this catalog's.
                    skipped += kind == "movie"
                    continue
                self.taken.add((catalog["directory"], kind, imdb))
            if not imdb:
                # Only the addon knows it (One Pace, Sosac, Bamabin): it goes to rex named by the
                # catalog (`display`), and plays from the addons that serve its own id.
                label = re.sub(r"[^A-Za-z0-9_-]", "-", own)
                if kind == "movie":
                    wanted.append(("%s-%s" % (catalog["slug"], label), own, meta, None, (), None))
                    continue
                full = self.own_meta(kind, own, config)
                if not full:
                    complete = False
                    continue
            elif kind == "movie":
                wanted.append(("%s-%s" % (catalog["slug"], imdb), imdb, meta, None, (own,) if own and own != imdb else (), imdb))
                continue
            else:
                label = imdb
                try:
                    response = get_json("%s/meta/series/%s.json" % (CINEMETA, imdb))
                    full = response.get("meta") if isinstance(response, dict) else None
                    if not isinstance(full, dict):
                        raise ValueError("series response has no meta")
                except Exception as error:
                    complete = False
                    LOG.warning("%s: %s", imdb, safe_error(error))
                    continue
            raw_videos = full.get("videos")
            if not isinstance(raw_videos, list) or not raw_videos:
                complete = False
                continue
            episodes = []
            for raw_video in raw_videos:
                if not isinstance(raw_video, dict):
                    complete = False
                    continue
                try:
                    season, episode = int(raw_video.get("season")), int(raw_video.get("episode"))
                except (TypeError, ValueError):
                    complete = False
                    continue
                if season <= 0 or episode <= 0:
                    complete = False
                    continue
                episodes.append(dict(raw_video, season=season, episode=episode))
            episodes.sort(key=lambda video: (video["season"], video["episode"]))
            for video in (episodes if config.get("lazy_catalogs") else episodes[:limit - len(wanted)]):
                vid = "%s-%s-%d-%d" % (catalog["slug"], label, video["season"], video["episode"])
                if imdb:
                    also = ("%s:%d:%d" % (own, video["season"], video["episode"]),) if own and own != imdb else ()
                    wanted.append((vid, "%s:%d:%d" % (imdb, video["season"], video["episode"]), dict(full, **meta), video, also, imdb))
                elif isinstance(video.get("id"), str) and video["id"]:
                    wanted.append((vid, video["id"], dict(full, **meta), video, (), None))
        items = []
        for at, (vid, sid, meta, video, also, imdb) in enumerate(wanted):
            if self.stale(version):
                # A settings save invalidated this catalog's relay paths and cache generation.
                complete = False
                break
            if config.get("lazy_catalogs"):
                probe = provisional_probe(meta, video)
                if kind == "tv":
                    probe["format"].pop("duration", None)
                item = stremio_item(config, catalog, vid, sid if kind == "tv" else imdb, meta, video, probe, "mkv")
                next_vid = wanted[at + 1][0] if video and at + 1 < len(wanted) and wanted[at + 1][0].rsplit("-", 2)[0] == vid.rsplit("-", 2)[0] else None
                self.cache_update(self.path("info", vid, config, version), dict(kind=kind, sid=sid, also=list(also), catalog={k: catalog[k] for k in ("type", "slug", "directory", "library", "title") if k in catalog}, item=item, next=next_vid, extension="mkv"), version)
                items.append(item)
                continue
            info_path = self.path("info", vid, config, version)
            expected_info = dict({"kind": kind, "sid": sid}, **({"also": list(also)} if also else {}))
            try:
                info = self.cached("info", vid, lambda: expected_info, config, version)
            except Exception as error:
                complete = False
                LOG.warning("%s: %s", vid, safe_error(error))
                # A truncated JSON file is just as stale as a valid record for another item.
                # Repair it before the probe so the next relay request sees a usable identity.
                info = expected_info
                self.cache_write(info_path, info, version)
                self.cache_remove(self.path(PROBES, vid, config, version), version)
            info_valid = isinstance(info, dict) and info.get("kind") == kind and info.get("sid") == sid
            if info_valid and (info.get("also") or []) != list(also):
                self.cache_update(info_path, {"also": list(also)}, version)
            if not info_valid:
                # Repair identity before probing. A stale identity means the derived probe belongs
                # to a different source item and must not be reused for this one.
                complete = False
                info = expected_info
                self.cache_write(info_path, info, version)
                self.cache_remove(self.path(PROBES, vid, config, version), version)

            # A corrupt or shape-invalid derived probe is repairable. Remove just that record
            # and ask ffprobe once more; a real probe failure is still recorded as a partial
            # catalog without repeatedly hammering the source.
            probe_path = self.path(PROBES, vid, config, version)
            extension = None
            # A stream ffprobe cannot read or rex cannot take gives way to the next one: an
            # addon's best-labelled link was a .zip of another show (Eclipsia, 2026-10-24), and
            # pinned, it kept the title out of rex on every sync.
            for _ in range(3):
                probe = None
                for attempt in range(2):
                    had_cache = os.path.isfile(probe_path)
                    try:
                        probe = self.cached(PROBES, vid, lambda: self.probe(vid, catalog, config), config, version)
                    except Exception as error:  # no stream that opens, or one ffprobe could not read
                        complete = False
                        if attempt == 0 and had_cache:
                            self.cache_remove(probe_path, version)
                            continue
                        LOG.warning("%s: %s", vid, safe_error(error))
                        break
                    if isinstance(probe, dict) and isinstance(probe.get("format"), dict):
                        break
                    complete = False
                    if attempt == 0:
                        self.cache_remove(probe_path, version)
                        continue
                    LOG.warning("%s: ffprobe returned no format", vid)
                    probe = None
                if isinstance(probe, dict) and isinstance(probe.get("format"), dict):
                    extension = CONTAINERS.get(probe["format"].get("format_name"))
                    if extension and kind != "tv" and placeholder(probe):
                        LOG.warning("%s: a %ss clip, not the title", vid, probe["format"].get("duration"))
                        extension = None
                    if extension and not any(isinstance(stream, dict) and stream.get("codec_type") == "video"
                                             for stream in probe.get("streams") or []):
                        # Pluto's MST3K probed as a subtitle track alone (2026-10-24).
                        LOG.warning("%s: no picture in it", vid)
                        extension = None
                    if extension:
                        break
                    complete = False
                    LOG.warning("%s: a %s stream rex cannot take", vid, probe["format"].get("format_name"))
                if not self.refuse(vid, config, version):
                    break
            if not extension:
                continue
            if info.get("extension") != extension:
                if not self.cache_update(info_path, {"extension": extension}, version):
                    complete = False
                    continue
            try:
                item = stremio_item(config, catalog, vid, sid if kind == "tv" else imdb, meta, video, probe, extension)
                items.append(item)
                self.cache_update(info_path, {"item": item, "catalog": {k: catalog[k] for k in ("type", "slug", "directory", "library", "title") if k in catalog},
                                              "also": list(also)}, version)
            except Exception as error:
                complete = False
                LOG.warning("%s: %s", vid, safe_error(error))
        LOG.info("%s: %d of %d ready", safe_url(catalog["url"]), len(items), len(wanted))
        self.catalog_incomplete = not complete
        return items

    def lazy_chunk(self, chunk, config, version):
        if not config.get("lazy_catalogs"):
            return chunk
        result = []
        for item in chunk:
            vid = item["path"].rsplit("/", 1)[-1].rsplit(".", 1)[0]
            self.cache_update(self.path("info", vid, config, version), {"item": item}, version)
            try:
                with open(self.path(PROBES, vid, config, version)) as handle:
                    item = self.measured_item(item, json.load(handle))
                self.cache_update(self.path("info", vid, config, version), {"extension": item["path"].rsplit(".", 1)[-1]}, version)
            except (OSError, ValueError, RuntimeError):
                pass
            result.append(item)
        return result

    def once(self):
        with self.config_guard:
            config, version = copy.deepcopy(self.config), self.config_version
        return self._once(config, version)

    def _once(self, config, version):
        # Register is one serialized feed request. The catalog scan and ffprobe calls below take
        # neither publication_lock nor config_guard, so settings remain responsive while a source
        # is slow. Each later request rechecks the generation immediately before publishing.
        with self.publication_lock:
            with self.config_guard:
                if self.config_version != version:
                    return
            self.register(config)
        items = []
        batch_size = max(1, min(1000, int(config.get("feed_batch_size", 200))))
        incomplete = False
        self.taken, listed = set(), []
        for catalog in config["catalogs"]:
            before = len(items)
            try:
                items += self.catalog_items(catalog, config, version)
                items += self.published_versions(items[before:], config, version)
                listed.append((catalog, self.catalog_listed))
                incomplete |= self.catalog_incomplete
            except Exception as error:
                incomplete = True
                self.status = "failed at %s: %s" % (safe_error(catalog.get("title") or catalog["slug"]), safe_error(error))
                LOG.warning("%s: %s", safe_url(catalog["url"]), safe_error(error))
                continue
            if self.stale(version):
                self.status = "settings changed during sync; retrying"
                return
            # Each catalog shows in rex once it is checked, not hours later when the last one is;
            # the snapshot at the end still removes what is gone.
            for at in range(0, len(items) - before, batch_size):
                answer = self.publish(version, "POST", "/rex/feed/%s/items" % config["source"],
                                      {"items": items[before + at:before + at + batch_size]}, config)
                if answer is None:
                    self.status = "settings changed during sync; retrying"
                    return
                for rejected in answer.get("rejected") or []:
                    if isinstance(rejected, dict):
                        LOG.warning("rex rejected %s: %s", rejected.get("id"), safe_error(rejected.get("reason")))
        if config.get("collections"):
            # Every file of a title names all its collections: rex keeps the last list it was sent.
            for item in items:
                imdb = (item.get("ids") or {}).get("imdb")
                if imdb:
                    directory = item["path"].split("/", 1)[0]
                    kind = "movie" if item.get("kind") == "movie" else "series"
                    item["collections"] = [catalog.get("title") or catalog["slug"] for catalog, ids in listed
                                           if catalog["directory"] == directory and catalog["type"] == kind and imdb in ids]
        if incomplete:
            # Every item went up with its catalog; only the collections, known now, are left to send.
            chunks = [items[at:at + batch_size] for at in range(0, len(items), batch_size)] if config.get("collections") else []
            for chunk in chunks:
                answer = self.publish(version, "POST", "/rex/feed/%s/items" % config["source"], {"items": chunk}, config)
                if answer is None:
                    self.status = "settings changed during sync; retrying"
                    return
            self.status = "%s: partial sync, %d items upserted" % (time.strftime("%Y-%m-%d %H:%M"), len(items))
            self.update_collection_posters(config)
            LOG.warning("upserted %d items without removing existing rows", len(items))
            return
        with self.publication_lock:
            session = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            present = {item["id"] for item in items}
            items.extend(item for item in self.published_versions(items, config, version) if item["id"] not in present)
            chunks = [items[at:at + batch_size] for at in range(0, len(items), batch_size)] or [[]]
            self.snapshot_playbacks = {}
        try:
            for part, chunk in enumerate(chunks):
                body = {"session": session, "part": part, "complete": part == len(chunks) - 1, "items": chunk}
                if body["complete"] and self.force_next:
                    body["force"] = True
                answer = self.publish(version, "PUT", "/rex/feed/%s/snapshot" % config["source"], body, config)
                if answer is None:
                    self.status = "settings changed during sync; retrying"
                    return
                for rejected in answer.get("rejected") or []:
                    if not isinstance(rejected, dict):
                        continue
                    LOG.warning("rex rejected %s: %s", rejected.get("id"), safe_error(rejected.get("reason")))
        finally:
            # Let a play publish between snapshot chunks. Replay those measured
            # rows after the final chunk, which may have contained older probes.
            with self.publication_lock:
                measured = list((self.snapshot_playbacks or {}).values())
                self.snapshot_playbacks = None
                if measured and not self.stale(version):
                    answer = self.rex("POST", "/rex/feed/%s/items" % config["source"],
                                      {"items": measured}, config)
                    if answer.get("rejected"):
                        LOG.warning("rex rejected %d playback refresh(es)", len(answer["rejected"]))
        with self.config_guard:
            if self.config_version == version:
                self.force_next = False
        self.status = "%s: %d items in rex" % (time.strftime("%Y-%m-%d %H:%M"), len(items))
        self.update_collection_posters(config)
        LOG.info("pushed %d items: %s", len(items), {key: answer.get(key) for key in ("created", "updated", "removed")})

    def schedule_collection_posters(self, config):
        """Coalesce feed batches into a background cover pass, including a trailing pass."""
        if not (config.get("collections") and config.get("collection_posters")):
            return
        with self.poster_schedule_lock:
            self.poster_pending = config
            if self.poster_running:
                return
            self.poster_running = True
        threading.Thread(target=self.collection_poster_worker,
                         name="collection-posters", daemon=True).start()

    def collection_poster_worker(self):
        while True:
            with self.poster_schedule_lock:
                config = self.poster_pending
                self.poster_pending = None
                if config is None:
                    self.poster_running = False
                    return
            self.update_collection_posters(config)

    def update_collection_posters(self, config):
        if config.get("collections") and config.get("collection_posters"):
            try:
                from collection_posters import sync_posters
                with self.poster_lock:
                    sync_posters(config)
            except Exception as error:
                LOG.warning("collection posters: %s", safe_error(error))

    def forever(self):
        soon = 0
        while True:
            self.status = "syncing since %s" % time.strftime("%H:%M")
            self.retry_soon = False
            try:
                self.once()
            except Exception as error:
                self.status = "failed: %s" % safe_error(error)
                LOG.warning("sync: %s", safe_error(error))
            soon = soon + 1 if self.retry_soon and soon < 3 else 0
            with self.config_guard:
                interval = self.config["retry_minutes"] if soon else self.config["interval_minutes"]
            self.wake.wait(interval * 60)
            self.wake.clear()


def fetch_text(url, agent):
    """A playlist's text and the link it was read from, after redirects."""
    request = urllib.request.Request(url, headers={"User-Agent": agent})
    with urllib.request.urlopen(request, timeout=30) as response:
        return response.read(MAX_JSON_BYTES).decode("utf-8", "replace"), response.geturl()


def one_variant(text, base, cap=None):
    """An HLS master as its best variant alone (the highest within `cap`, then the most bandwidth),
    with the renditions it names and every link absolute; None for a media playlist or a master
    of one. rex takes a master's first video stream, the lowest or an unreadable variant (PlavioHD's
    height 0, PenguPlay's SD), and FFmpeg opened all of PenguPlay's four before a picture (20-30 s)."""
    lines = text.splitlines()
    variants = []
    for at, line in enumerate(lines):
        if line.startswith("#EXT-X-STREAM-INF"):
            uri = next((other.strip() for other in lines[at + 1:] if other.strip() and not other.startswith("#")), None)
            height = re.search(r"RESOLUTION=\d+x(\d+)", line)
            bandwidth = re.search(r"(?<![-A-Z])BANDWIDTH=(\d+)", line)
            if uri:
                variants.append((line, uri, int(height[1]) if height else 0, int(bandwidth[1]) if bandwidth else 0))
    if len(variants) < 2:
        return None
    fitting = [variant for variant in variants if not cap or variant[2] <= int(cap)] or variants
    line, uri, _, _ = max(fitting, key=lambda variant: variant[2:])
    # One audio rendition (the default) and no subtitle playlists: rex maps tracks by the probe's
    # indexes, and Pluto TV's masters list a different number of renditions per session, so a
    # channel probed with four tracks before its picture played with fewer (2026-10-24).
    line = re.sub(r',?SUBTITLES="[^"]*"', "", line)
    groups = set(re.findall(r'(?:AUDIO|VIDEO|CLOSED-CAPTIONS)="([^"]+)"', line))
    kept = ["#EXTM3U"] + [other for other in lines if other.startswith(("#EXT-X-VERSION", "#EXT-X-INDEPENDENT-SEGMENTS"))]
    renditions = [other for other in lines if other.startswith("#EXT-X-MEDIA:") and "TYPE=SUBTITLES" not in other
                  and (re.search(r'GROUP-ID="([^"]+)"', other) or [None, None])[1] in groups]
    audio = [other for other in renditions if "TYPE=AUDIO" in other]
    chosen = next((other for other in audio if "DEFAULT=YES" in other), audio[0] if audio else None)
    kept += [other for other in renditions if "TYPE=AUDIO" not in other or other is chosen]
    return rewrite_playlist("\n".join(kept + [line, uri]), base, lambda link: link)


def rewrite_playlist(text, base, relayed):
    """An HLS playlist with every link it names (segments, variants, `URI="..."` keys, maps and
    renditions) replaced by `relayed(absolute link)`."""
    out = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped and not stripped.startswith("#"):
            out.append(relayed(urllib.parse.urljoin(base, stripped)))
        elif stripped.startswith("#") and 'URI="' in stripped:
            out.append(re.sub(r'URI="([^"]+)"', lambda match: 'URI="%s"' % relayed(urllib.parse.urljoin(base, match[1])), line))
        else:
            out.append(line)
    return "\n".join(out) + "\n"


def own_network(handler):
    """Whether a settings request comes from this machine, the home network or Tailscale, to a host
    named by its address (a name could be another site rebinding to us), and not from another
    page's form."""
    try:
        client = ipaddress.ip_address(handler.client_address[0])
        host_header = handler.headers.get("Host") or ""
        parsed_host = urllib.parse.urlsplit("//" + host_header)
        if parsed_host.username or parsed_host.password or parsed_host.path or parsed_host.query or parsed_host.fragment:
            return False
        parsed_host.port  # reject an invalid port in a forged Host header
        host = parsed_host.hostname or ""
        if host != "localhost":
            ipaddress.ip_address(host)
    except ValueError:
        return False
    origin = handler.headers.get("Origin")
    if handler.command == "POST" and origin and origin != "http://" + handler.headers.get("Host"):
        return False
    return client.is_loopback or client.is_private or client in TAILSCALE


TAILSCALE = ipaddress.ip_network("100.64.0.0/10")


PAGE = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>rex-stremio</title>
<style>
:root{color-scheme:light dark;--fg:#1d1d1f;--bg:#fafafa;--muted:#6e6e73;--line:#d2d2d7;--accent:#b4500f;--on-accent:#fff}
@media (prefers-color-scheme:dark){:root{--fg:#f5f5f7;--bg:#161617;--muted:#a1a1a6;--line:#3a3a3c;--accent:#ff9a62;--on-accent:#1a0d05}}
body{font:15px/1.5 system-ui,sans-serif;color:var(--fg);background:var(--bg);max-width:860px;margin:0 auto;padding:16px}
h1{font-size:22px;margin:0 0 4px}h2{font-size:17px;margin:28px 0 8px}p.muted,small{color:var(--muted)}
table{width:100%%;border-collapse:collapse}td,th{padding:6px 4px;border-bottom:1px solid var(--line);text-align:left;vertical-align:middle}
input[type=text],input[type=url],input[type=number],select{font:inherit;padding:4px 6px;border:1px solid var(--line);border-radius:6px;background:transparent;color:inherit;max-width:100%%}
button{font:inherit;padding:5px 12px;border-radius:6px;border:1px solid var(--accent);background:var(--accent);color:var(--on-accent);cursor:pointer}
button.plain{background:transparent;color:var(--accent)}form.inline{display:inline}.row{display:flex;gap:8px;flex-wrap:wrap;align-items:center}
.scroll{overflow-x:auto}input[type=checkbox]{accent-color:var(--accent)}
</style></head><body>
<h1>rex-stremio</h1><p class="muted">Stremio catalogs as rex libraries. Sync: %(status)s</p>
<h2>Addons</h2>
<p class="muted">Paste an addon's manifest link, as you would in Stremio. Catalogs come from any addon; streams from every addon that has them.</p>
<div class="scroll"><table><tr><th>Addon</th><th>Gives</th><th></th></tr>%(addons)s</table></div>
<form method="post" action="/addons" class="row" style="margin-top:8px">
<label for="add">Manifest link</label><input id="add" type="url" name="url" required placeholder="https://…/manifest.json" style="flex:1;min-width:220px">
<button>Add</button></form>
<form method="post" action="/settings">
<h2>Catalogs</h2>
<p class="muted">Each chosen catalog goes into the library you name. With collections enabled, Collection name labels its collection and generated poster. Limits count movies, shows or live channels.</p>
<div class="scroll"><table><tr><th>Take</th><th>Catalog</th><th>Collection name</th><th>Library</th><th>Titles / shows</th></tr>%(catalogs)s</table></div>
<div class="row" style="margin-top:8px"><input type="checkbox" id="collections" name="collections" value="1"%(collections)s>
<label for="collections">Catalogs as collections: each catalog is a collection in its library, and a title in several is there once</label></div>
<h2>Streams</h2>
<p class="muted">The highest resolution within these limits plays; ties go by the addons' own order. If a link no longer opens, the next one plays.</p>
<div class="row"><label for="res">Highest resolution</label><select id="res" name="max_resolution">%(resolutions)s</select>
<label for="size">Largest file (GB)</label><input id="size" type="number" min="0" step="0.1" name="max_size_gb" value="%(max_size_gb)s" placeholder="any"></div>
<h2>rex</h2>
<div class="row"><label for="rex">rex's address</label><input id="rex" type="url" name="rex_url" value="%(rex_url)s" required style="flex:1;min-width:220px"></div>
<h2>On-demand libraries</h2>
<p class="muted">Virtual movie and show cards use these separate libraries. Hidden libraries stay out of Home and global search.</p>
<div class="row"><label for="ondemand_movies_library">Movies library</label><input id="ondemand_movies_library" type="text" name="ondemand_movies_library" value="%(ondemand_movies_library)s" required maxlength="160">
<label for="ondemand_tv_library">TV library</label><input id="ondemand_tv_library" type="text" name="ondemand_tv_library" value="%(ondemand_tv_library)s" required maxlength="160"></div>
<div class="row"><input type="checkbox" id="hide_ondemand_libraries" name="hide_ondemand_libraries" value="1"%(hide_ondemand_libraries)s><label for="hide_ondemand_libraries">Hide on-demand libraries from Home and global search</label></div>
<p style="margin-top:20px"><button>Save and sync</button></p>
</form></body></html>"""


def shown(url):
    """An addon's link without what may be a key in its path or query."""
    parts = urllib.parse.urlsplit(addon_base(url))
    return parts.hostname or "addon"


def page(config, status):
    esc = lambda value: html.escape(str(value), quote=True)
    rows = []
    for at, addon in enumerate(config["addons"]):
        if not isinstance(addon, dict) or not isinstance(addon.get("url"), str):
            continue
        manifest = addon_manifest(addon)
        resources = manifest.get("resources") if isinstance(manifest.get("resources"), list) else []
        gives = [name for name in ("catalog", "stream") if any((entry if isinstance(entry, str) else entry.get("name")) == name
                                                                  for entry in resources if isinstance(entry, (str, dict)))]
        rows.append('<tr><td>%s<br><small>%s</small></td><td>%s</td><td><form class="inline" method="post" action="/addons/remove">'
                    '<input type="hidden" name="at" value="%d"><button class="plain">Remove</button></form></td></tr>'
                    % (esc(manifest.get("name") or "addon"), esc(shown(addon["url"])), esc(", ".join(gives) or "nothing rex uses"), at))
    taken = {catalog["url"]: catalog for catalog in config["catalogs"]}
    catalogs, n = [], 0
    for addon in config["addons"]:
        if not isinstance(addon, dict) or not isinstance(addon.get("url"), str):
            continue
        manifest = addon_manifest(addon)
        for catalog in catalogs_of(manifest):
            url = "%s/catalog/%s/%s.json" % (addon_base(addon["url"]), catalog["type"], catalog["id"])
            chosen = taken.get(url) or {}
            library = chosen.get("library") or LIBRARIES[catalog["type"]]
            addon_name = manifest.get("name") or "addon"
            name = "%s: %s (%s)" % (addon_name, catalog["name"],
                                    {"movie": "films", "series": "episodes", "tv": "channels"}[catalog["type"]])
            collection_name = chosen.get("title") or catalog["name"]
            catalogs.append(
                f'<tr><td><input type="checkbox" id="c{n}" name="take" value="{n}"'
                + (' checked' if chosen else '') + '>'
                + f'<input type="hidden" name="url{n}" value="{esc(url)}">'
                + f'<input type="hidden" name="slug{n}" value="{esc(chosen.get("slug") or "")}">'
                + f'<input type="hidden" name="directory{n}" value="{esc(chosen.get("directory") or "")}"></td>'
                + f'<td><label for="c{n}">{esc(name)}</label></td>'
                + f'<td><input type="text" name="title{n}" value="{esc(collection_name)}" aria-label="Collection name" required maxlength="160"></td>'
                + f'<td><input type="text" name="library{n}" value="{esc(library)}" aria-label="Library"></td>'
                + f'<td><input type="number" min="1" name="limit{n}" value="{esc(chosen.get("limit") or 50)}" aria-label="How many" style="width:5em"></td></tr>')
            n += 1
    resolutions = "".join('<option value="%s"%s>%s</option>' % (value, " selected" if str(config.get("max_resolution") or "") == value else "", label)
                          for value, label in (("", "any"), ("2160", "2160p (4K)"), ("1080", "1080p"), ("720", "720p")))
    return PAGE % {"status": esc(safe_error(status)), "addons": "".join(rows) or '<tr><td colspan="3"><small>None yet.</small></td></tr>',
                   "catalogs": "".join(catalogs) or '<tr><td colspan="5"><small>Add an addon with catalogs, such as Cinemeta.</small></td></tr>',
                   "resolutions": resolutions, "collections": " checked" if config.get("collections") else "", "max_size_gb": esc("%g" % config["max_size_gb"] if config.get("max_size_gb") else ""),
                   "ondemand_movies_library": esc(config["ondemand_movies_library"]),
                   "ondemand_tv_library": esc(config["ondemand_tv_library"]),
                   "hide_ondemand_libraries": " checked" if config.get("hide_ondemand_libraries") else "",
                   # The settings field is an authorized private input and must round-trip exactly;
                   # safe_url is reserved for logs/status and addon display.
                   "rex_url": esc(config["rex_url"])}


class App:
    """The relay and the settings page, on one listener."""

    def __init__(self, config_path, config, sync):
        self.config_path, self.config, self.sync = config_path, config, sync
        self.saving = threading.RLock()

    def settings(self, form):
        """The settings form -> the config, saved, then a sync."""
        with self.saving:
            values = dict(self.config)
            catalogs = []
            for at in form.get("take", []):
                url = form.get("url" + at, [""])[0]
                limit = form.get("limit" + at, ["50"])[0]
                catalog = {"url": url, "title": form.get("title" + at, [""])[0].strip()[:160] or None,
                           "library": form.get("library" + at, [""])[0].strip() or None,
                           "limit": int(limit) if limit.isdigit() and int(limit) > 0 else 50}
                for key in ("slug", "directory"):
                    value = form.get(key + at, [""])[0]
                    if value:
                        catalog[key] = value
                previous = next((saved for saved in self.config["catalogs"] if saved["url"] == url), None)
                if (previous and catalog.get("directory") == previous.get("directory")
                        and catalog.get("library") != previous.get("library")
                        and previous.get("directory") == slug(previous.get("library", ""))):
                    # The hidden directory is a derived value from the prior library. Re-derive it
                    # when that label changes; a different prior directory is a deliberate override.
                    catalog["directory"] = slug(catalog.get("library") or "")
                catalogs.append(catalog)
            values["catalogs"] = [{key: value for key, value in catalog.items() if value} for catalog in catalogs]
            values["collections"] = form.get("collections", [""])[0] == "1"
            values["ondemand_movies_library"] = form.get("ondemand_movies_library", [DEFAULTS["ondemand_movies_library"]])[0].strip()[:160]
            values["ondemand_tv_library"] = form.get("ondemand_tv_library", [DEFAULTS["ondemand_tv_library"]])[0].strip()[:160]
            values["hide_ondemand_libraries"] = form.get("hide_ondemand_libraries", [""])[0] == "1"
            values["max_resolution"] = int(form["max_resolution"][0]) if form.get("max_resolution", [""])[0].isdigit() else None
            size = form.get("max_size_gb", [""])[0]
            values["max_size_gb"] = float(size) if re.fullmatch(r"\d+(\.\d+)?", size) and float(size) > 0 else None
            rex_url = form.get("rex_url", [""])[0].strip()
            if not rex_url.startswith(("http://", "https://")):
                raise ValueError("rex_url must be an http(s) URL")
            values["rex_url"] = rex_url
            self.save(values)

    def add_addon(self, url):
        base = addon_base(url)
        if not base.startswith(("http://", "https://")):
            raise ValueError("not an addon link")
        manifest = get_json(base + "/manifest.json", 30)
        if (not isinstance(manifest, dict) or not isinstance(manifest.get("id"), str)
                or not manifest["id"] or not isinstance(manifest.get("resources"), list)):
            raise ValueError("no Stremio manifest at that link")
        with self.saving:
            addons = [addon for addon in self.config["addons"]
                      if isinstance(addon, dict) and addon_base(addon.get("url")) != base]
            self.save(dict(self.config, addons=addons + [{"url": base + "/manifest.json", "manifest": manifest}]), sync=False)

    def remove_addon(self, at):
        with self.saving:
            if not isinstance(at, int) or at < 0 or at >= len(self.config["addons"]):
                raise ValueError("addon index is out of range")
            addons = list(self.config["addons"])
            gone = addons.pop(at)
            prefix = addon_base(gone["url"]) + "/catalog/"
            self.save(dict(self.config, addons=addons,
                           catalogs=[c for c in self.config["catalogs"] if not c["url"].startswith(prefix)]))

    def save(self, values, sync=True):
        with self.saving:
            fresh = validate_config(self.config_path, values)
            with self.sync.publication_lock:
                with self.sync.config_guard:
                    # Persist the same normalized identity that is installed in memory. This makes
                    # the first save durable across restart and keeps later reorder/remove stable.
                    save_config(self.config_path, fresh)
                    self.config.clear()
                    self.config.update(fresh)
                    self.sync.config_version += 1
                    self.sync.force_next = True
                    with self.sync.guard:
                        self.sync.cache.clear()
        if sync:
            self.sync.wake.set()

    def handler(self):
        app = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *args):
                pass

            def do_GET(self):
                path = urllib.parse.urlsplit(self.path).path
                self.probe_request = path.endswith(".probe") or urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query).get("probe") == ["1"]
                warm = re.fullmatch(r"/_rex/detail/([A-Za-z0-9_-]+)", path)
                if warm:
                    if not own_network(self):
                        self.send_error(403)
                        return
                    app.sync.warm_search(warm[1])
                    self.send_response(200)
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                if path == "/":
                    if not own_network(self):
                        self.send_error(403)
                        return
                    with app.sync.config_guard:
                        body = page(app.config, app.sync.status).encode()
                    self.send_response(200)
                    self.send_header("Content-Type", "text/html; charset=utf-8")
                    self.send_header("Content-Length", str(len(body)))
                    self.send_header("Cache-Control", "no-store")
                    self.end_headers()
                    if self.command != "HEAD":
                        self.wfile.write(body)
                    return
                relayed = re.fullmatch(r"/_relay/([A-Za-z0-9_-]+)/([0-9a-f]{20})\.[A-Za-z0-9]+", path)
                if relayed:
                    url, headers = app.sync.relayed_link(*relayed.groups())
                    if not url:
                        self.send_error(404)
                        return
                    self.relay(relayed[1], url, headers)
                    return
                if path.startswith("/collection-posters/"):
                    from collection_posters import poster_key, render
                    with app.sync.config_guard:
                        names = [c.get("title") or c["slug"] for c in app.sync.config["catalogs"] if c["type"] != "tv"]
                    name = next((n for n in names if path == "/collection-posters/" + poster_key(n) + ".png"), None)
                    if name is None:
                        self.send_error(404)
                        return
                    body = render(name)
                    self.send_response(200)
                    self.send_header("Content-Type", "image/png")
                    self.send_header("Content-Length", str(len(body)))
                    self.send_header("Cache-Control", "public, max-age=86400")
                    self.end_headers()
                    if self.command != "HEAD": self.wfile.write(body)
                    return
                vid = app.sync.route_vid(path)
                if not vid:
                    self.send_error(404)
                    return
                # Rex's file-availability checks use HEAD. A catalog entry is a
                # virtual file: its existence does not require a playable link yet.
                if self.command == "HEAD" and not path.endswith(".probe"):
                    self.send_response(200)
                    self.send_header("Content-Type", "application/octet-stream")
                    self.send_header("Cache-Control", "no-store")
                    self.end_headers()
                    return
                try:
                    url = app.sync.prepare(vid) if app.sync.config.get("lazy_catalogs") and not path.endswith(".probe") else app.sync.resolve(vid)
                except Exception as error:
                    LOG.warning("resolve %s: %s", vid, safe_error(error))
                    self.send_error(502, "No stream addon has a stream that opens")
                    return
                with app.sync.guard:
                    headers = app.sync.via.get(vid) or {}
                if headers or app.sync.config.get("lazy_catalogs"):
                    self.relay(vid, url, headers)
                    return
                master = self.trimmed(url, self.headers.get("User-Agent")) if urllib.parse.urlsplit(url).path.endswith(".m3u8") else None
                if master:
                    self.send_response(200)
                    self.send_header("Content-Type", "application/vnd.apple.mpegurl")
                    self.send_header("Content-Length", str(len(master)))
                    self.end_headers()
                    if self.command != "HEAD":
                        self.wfile.write(master)
                    return
                self.send_response(302)
                self.send_header("Location", url)
                self.send_header("Content-Length", "0")
                self.end_headers()

            do_HEAD = do_GET

            def trimmed(self, url, agent):
                """An HLS master's best variant alone (`one_variant`), or None to send rex to it.
                Asked as the player asks: ABC's Akamai links name a variant only the User-Agent
                that fetched the master may read (403 for any other, 2026-10-24)."""
                try:
                    text, final = fetch_text(url, agent or "rex-stremio")
                except Exception as error:
                    LOG.info("%s: %s", safe_url(url), safe_error(error))
                    return None
                master = one_variant(text, final, app.config.get("max_resolution")) if text.lstrip().startswith("#EXTM3U") else None
                return master.encode() if master else None

            def relay(self, vid, url, headers):
                """A link that needs its headers, fetched here: bytes as they come (the client's
                Range passed on), a playlist with every link it names sent back through here."""
                ask = dict({"User-Agent": "rex-stremio"}, **headers)
                if self.headers.get("Range"):
                    ask["Range"] = self.headers["Range"]
                try:
                    upstream = urllib.request.urlopen(urllib.request.Request(url, headers=ask), timeout=30)
                except urllib.error.HTTPError as error:
                    self.send_error(error.code if 400 <= error.code < 600 else 502)
                    return
                except Exception as error:
                    LOG.warning("relay %s: %s", vid, safe_error(error))
                    self.send_error(502)
                    return
                with upstream:
                    kind = upstream.headers.get("Content-Type") or ""
                    if "mpegurl" in kind.lower() or urllib.parse.urlsplit(upstream.geturl()).path.endswith(".m3u8"):
                        text = upstream.read(MAX_JSON_BYTES).decode("utf-8", "replace")
                        if text.lstrip().startswith("#EXTM3U"):
                            text = one_variant(text, upstream.geturl(), app.config.get("max_resolution")) or text
                            body = rewrite_playlist(text, upstream.geturl(), lambda link: app.sync.remember(vid, link) + ("?probe=1" if self.probe_request else "")).encode()
                            self.send_response(200)
                            self.send_header("Content-Type", "application/vnd.apple.mpegurl")
                            self.send_header("Content-Length", str(len(body)))
                            self.end_headers()
                            if self.command != "HEAD":
                                self.wfile.write(body)
                            return
                        raw = text.encode()
                        self.send_response(upstream.status)
                        self.send_header("Content-Length", str(len(raw)))
                        self.end_headers()
                        if self.command != "HEAD":
                            self.wfile.write(raw)
                        return
                    self.send_response(upstream.status)
                    for name in ("Content-Type", "Content-Length", "Content-Range", "Accept-Ranges", "Last-Modified", "ETag"):
                        if upstream.headers.get(name):
                            self.send_header(name, upstream.headers[name])
                    self.end_headers()
                    if self.command == "HEAD":
                        return
                    try:
                        while True:
                            chunk = upstream.read(1 << 16)
                            if not chunk:
                                break
                            self.wfile.write(chunk)
                            if not self.probe_request:
                                app.sync.started_stream(vid)
                    except (BrokenPipeError, ConnectionResetError):
                        pass

            def do_POST(self):
                if not own_network(self):
                    self.send_error(403)
                    return
                try:
                    length = int(self.headers.get("Content-Length") or 0)
                except ValueError:
                    self.send_error(400, "invalid request")
                    return
                if length < 0:
                    self.send_error(400, "invalid request")
                    return
                if length > MAX_FORM_BYTES:
                    self.send_error(413, "request body too large")
                    return
                try:
                    form = urllib.parse.parse_qs(self.rfile.read(length).decode(errors="replace"),
                                                 max_num_fields=MAX_FORM_FIELDS)
                except ValueError:
                    self.send_error(400, "invalid request")
                    return
                path = urllib.parse.urlsplit(self.path).path
                self.probe_request = path.endswith(".probe") or urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query).get("probe") == ["1"]
                try:
                    if path == "/addons":
                        app.add_addon(form.get("url", [""])[0])
                    elif path == "/addons/remove":
                        value = form.get("at", [""])[0]
                        if not re.fullmatch(r"\d+", value):
                            raise ValueError("addon index is out of range")
                        app.remove_addon(int(value))
                    elif path == "/settings":
                        app.settings(form)
                    else:
                        self.send_error(404)
                        return
                except Exception as error:
                    LOG.warning("settings: %s", safe_error(error))
                    self.send_error(400, "invalid request")
                    return
                self.send_response(303)
                self.send_header("Location", "/")
                self.send_header("Content-Length", "0")
                self.end_headers()

        return Handler


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--config", default="config.json")
    parser.add_argument("--debug", action="store_true", help="detailed search/probe/playback logs (no stream URLs)")
    parser.add_argument("--once", action="store_true", help="sync once while the relay runs, then exit")
    args = parser.parse_args(argv)
    logging.basicConfig(level=logging.DEBUG if args.debug else logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    if not os.path.exists(args.config):
        save_config(args.config, {"listen": os.environ.get("REX_STREMIO_LISTEN") or DEFAULTS["listen"]})
    config = load_config(args.config)
    LOG.info("debug logging=%s; next episode searches begin after first media bytes to Rex", args.debug)
    sync = Sync(config)
    host, port = config["listen"].rsplit(":", 1)
    server = ThreadingHTTPServer((host, int(port)), App(args.config, config, sync).handler())
    threading.Thread(target=server.serve_forever, daemon=True).start()
    LOG.info("relay and settings on http://%s/, %d catalog(s), rex at %s", config["listen"], len(config["catalogs"]), safe_url(config["rex_url"]))
    if args.once:
        sync.once()
        return 0
    sync.forever()


if __name__ == "__main__":
    sys.exit(main())

"""Playback deadlines must not wait for slow providers or retry timed-out probes."""
import subprocess
import threading
import time
import unittest
from unittest.mock import Mock, patch

import rex_stremio as addon
from test_lazy_playback import LazyPlayback


class SearchDeadline(unittest.TestCase):
    def test_empty_search_finishes_immediately(self):
        started = time.monotonic()
        search = addon.StreamSearch([0], lambda _: [])
        self.assertEqual(list(search.candidates({}, None, set())), [])
        self.assertLess(time.monotonic() - started, .5)

    def test_hung_search_stops_at_deadline(self):
        release = threading.Event()
        self.addCleanup(release.set)
        with patch.object(addon, 'SEARCH_TIMEOUT', .08):
            search = addon.StreamSearch([0], lambda _: release.wait(2) or [])
        started = time.monotonic()
        self.assertEqual(list(search.candidates({}, None, set())), [])
        self.assertLess(time.monotonic() - started, .5)

    def test_other_addon_can_finish_while_first_candidate_is_probed(self):
        probing, later = threading.Event(), threading.Event()
        first = {'url': 'https://stream.invalid/first'}
        second = {'url': 'https://stream.invalid/second'}
        def ask(index):
            if index == 1:
                probing.wait(2)
                later.set()
                return [second]
            return [first]
        search = addon.StreamSearch([0, 1], ask)
        candidates = search.candidates({}, None, set())
        self.assertEqual(next(candidates), first)
        probing.set()
        self.assertTrue(later.wait(2))
        self.assertEqual(next(candidates), second)
        self.assertEqual(list(candidates), [])


class ProbeDeadline(LazyPlayback):
    def test_probe_timeout_fails_without_trying_three_candidates(self):
        self.seed()
        self.sync.resolve = Mock(return_value='https://stream.invalid/file')
        self.sync.probe.side_effect = subprocess.TimeoutExpired('ffprobe', 10)
        self.sync.refuse = Mock(return_value=True)
        with self.assertRaisesRegex(RuntimeError, 'timed out after 10s'):
            self.sync.prepare('shows-tt1000001-1-1', prefetch=False)
        self.assertEqual(self.sync.resolve.call_count, 1)
        self.assertEqual(self.sync.probe.call_count, 1)
        self.sync.rex.assert_not_called()

    def test_no_search_results_never_start_a_probe(self):
        self.seed()
        self.sync.resolve = Mock(side_effect=RuntimeError('no stream addon has a stream that opens'))
        with self.assertRaisesRegex(RuntimeError, 'no stream'):
            self.sync.prepare('shows-tt1000001-1-1', prefetch=False)
        self.sync.probe.assert_not_called()
        self.sync.rex.assert_not_called()

    def test_real_relay_returns_502_for_empty_search_and_failed_probe(self):
        import urllib.error
        import urllib.request
        from http.server import ThreadingHTTPServer
        self.config['catalogs'] = [self.catalog]
        self.seed()
        server = ThreadingHTTPServer(('127.0.0.1', 0), addon.App('unused', self.config, self.sync).handler())
        threading.Thread(target=server.serve_forever, daemon=True).start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        url = 'http://127.0.0.1:%s/shows/shows/shows-tt1000001-1-1.stream' % server.server_address[1]
        self.sync.resolve = Mock(side_effect=RuntimeError('no stream addon has a stream that opens'))
        with self.assertRaises(urllib.error.HTTPError) as failure:
            urllib.request.urlopen(url, timeout=2)
        self.assertEqual(failure.exception.code, 502)
        self.sync.probe.assert_not_called()
        self.sync.resolve = Mock(return_value='https://stream.invalid/file')
        self.sync.probe.side_effect = subprocess.TimeoutExpired('ffprobe', 10)
        with self.assertRaises(urllib.error.HTTPError) as failure:
            urllib.request.urlopen(url, timeout=2)
        self.assertEqual(failure.exception.code, 502)
        self.assertEqual(self.sync.probe.call_count, 1)
        self.sync.rex.assert_not_called()

    def test_actual_probe_process_is_killed_at_deadline(self):
        import os
        import tempfile
        with tempfile.TemporaryDirectory() as work:
            executable = os.path.join(work, 'ffprobe')
            with open(executable, 'w') as handle:
                handle.write('#!/usr/bin/python3\nimport time\ntime.sleep(30)\n')
            os.chmod(executable, 0o700)
            config = dict(self.config, ffprobe=executable)
            with patch.object(addon, 'PROBE_TIMEOUT', .08), patch.object(addon, 'lenient_hls', return_value=()):
                started = time.monotonic()
                with self.assertRaises(subprocess.TimeoutExpired):
                    addon.Sync.probe(self.sync, 'example', self.catalog, config)
                self.assertLess(time.monotonic() - started, .5)

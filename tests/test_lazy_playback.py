"""Deferred playback must never ask stream providers while indexing a catalog."""
import json
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock, patch
import rex_stremio as addon


class LazyPlayback(unittest.TestCase):
    def setUp(self):
        self.work=tempfile.TemporaryDirectory();self.addCleanup(self.work.cleanup)
        self.config=dict(addon.DEFAULTS,lazy_catalogs=True,cache=self.work.name,relay_url='http://relay.invalid',catalogs=[])
        self.catalog=dict(type='series',limit=1,url='https://catalog.invalid/catalog/series/top.json',slug='shows',directory='shows',library='Shows')
        self.sync=addon.Sync(self.config)
        self.addCleanup(self.sync.prefetch_pool.shutdown,wait=True)
        self.addCleanup(self.sync.version_pool.shutdown,wait=True)
        self.addCleanup(self.sync.playback_publication_pool.shutdown,wait=True)
        def metadata(url):
            if url==self.catalog['url']:return {'metas':[{'id':'tt1000001','name':'First'},{'id':'tt1000001','name':'Duplicate'},{'id':'tt1000002','name':'Second'}]}
            return {'meta':{'name':'Example','videos':[{'season':1,'episode':n,'name':f'Episode {n}'} for n in [3,1,2]]}}
        self.meta=patch.object(addon,'get_json',side_effect=metadata);self.meta.start();self.addCleanup(self.meta.stop)
        self.sync.probe=Mock(return_value={'format':{'format_name':'matroska,webm','size':'1234'},'streams':[{'index':0,'codec_type':'video','codec_name':'hevc'}]})
        self.sync.streams=Mock(side_effect=AssertionError('catalog indexing searched streams'))
        self.sync.rex=Mock(return_value={})

    def seed(self):return self.sync.catalog_items(self.catalog)

    def test_limit_counts_unique_shows_and_keeps_every_episode_without_search_or_probe(self):
        self.assertEqual(len(self.seed()),3)
        self.sync.streams.assert_not_called();self.sync.probe.assert_not_called()
        self.catalog['limit']=2
        self.assertEqual(len(self.seed()),6)
        with open(self.sync.path('info','shows-tt1000001-1-3')) as f:self.assertIsNone(json.load(f)['next'])

    def test_prepare_reuses_probe_and_first_media_bytes_prefetch_only_next(self):
        self.seed();self.sync.resolve=Mock(return_value='https://stream.invalid/file')
        self.sync.prefetch=Mock()
        for _ in range(2):self.assertEqual(self.sync.prepare('shows-tt1000001-1-1'),'https://stream.invalid/file')
        self.sync.playback_publication_pool.submit(lambda:None).result()
        self.assertEqual(self.sync.probe.call_count,1)
        self.sync.prefetch.assert_not_called()
        self.sync.started_stream('shows-tt1000001-1-1')
        self.sync.started_stream('shows-tt1000001-1-1')
        self.sync.prefetch.assert_called_once_with('shows-tt1000001-1-2')
        item=self.sync.rex.call_args.args[2]['items'][0]
        self.assertEqual(item['media_info']['streams'][0]['codec_name'],'hevc')
        self.assertEqual(item['id'],'st-shows-tt1000001-1-1')
        self.assertEqual(item['size'],1234)
        self.sync.resolve.return_value='https://stream.invalid/replacement'
        self.sync.prepare('shows-tt1000001-1-1',prefetch=False)
        self.assertEqual(self.sync.probe.call_count,2)

    def test_prefetch_does_not_schedule_a_chain(self):
        self.seed();done=threading.Event()
        def prepared(vid,*,prefetch):self.assertFalse(prefetch);done.set()
        self.sync.prepare=Mock(side_effect=prepared)
        self.sync.prefetch('shows-tt1000001-1-2')
        self.assertTrue(done.wait(2));self.assertEqual(self.sync.prepare.call_count,1)

    def test_first_episode_does_not_wait_for_busy_rex_feed(self):
        self.seed()
        self.sync.resolve=Mock(return_value='https://stream.invalid/file')
        started, release=threading.Event(), threading.Event()
        self.addCleanup(release.set)
        def slow_feed(*args):
            started.set()
            self.assertTrue(release.wait(3))
            return {}
        self.sync.rex=Mock(side_effect=slow_feed)
        self.assertEqual(self.sync.prepare('shows-tt1000001-1-1'), 'https://stream.invalid/file')
        self.assertTrue(started.wait(2))
        self.assertFalse(release.is_set())
        release.set()
        self.sync.playback_publication_pool.submit(lambda:None).result(timeout=3)
        self.sync.playback_publication_pool.submit(lambda:None).result(timeout=3)

    def test_opening_another_detail_cancels_the_previous_search_without_a_queue(self):
        self.catalog['limit']=2
        self.seed()
        seen=[]
        self.sync.streams=Mock(side_effect=lambda kind,sid,config,also,control:seen.append((sid,control)))
        first='shows-tt1000001-1-1';second='shows-tt1000002-1-1'
        self.sync.warm_search(first)
        self.sync.warm_search(first)
        self.assertEqual(len(seen),1)
        self.sync.warm_search(second)
        self.assertEqual(len(seen),2)
        self.assertTrue(seen[0][1].cancelled.is_set())
        self.assertFalse(seen[1][1].cancelled.is_set())

    def test_season_hint_registers_an_unopened_on_demand_episode(self):
        self.config['catalogs'] = [self.catalog]
        self.sync.config['catalogs'] = [self.catalog]
        self.sync.streams = Mock()
        vid = 'shows-tt1000001-s1e1-ondemand'
        self.sync.warm_search(vid)
        self.sync.streams.assert_called_once()
        self.assertEqual(self.sync.streams.call_args.args[:2], ('series', 'tt1000001:1:1'))
        with open(self.sync.path('info', vid)) as handle:
            self.assertEqual(json.load(handle)['sid'], 'tt1000001:1:1')

    def test_play_reuses_in_progress_detail_search_with_a_fresh_deadline(self):
        release=threading.Event();self.addCleanup(release.set)
        self.sync.streams=addon.Sync.streams.__get__(self.sync)
        control=addon.WarmControl()
        with patch.object(addon,'SEARCH_TIMEOUT',.2):
            search=addon.StreamSearch([0],lambda _:release.wait(2) or [],control)
            key=(self.sync.config_version,'series','tt1000001:1:1',())
            self.sync.stream_searches[key]=search
            time.sleep(.1)
            before=time.monotonic()
            self.assertIs(self.sync.streams('series','tt1000001:1:1',self.config,()),search)
            self.assertGreater(search.deadline-before,.18)
        self.assertFalse(control.cancelled.is_set())
        self.assertTrue(control.playback)

    def test_new_detail_does_not_cancel_a_search_claimed_by_playback(self):
        self.catalog['limit']=2;self.seed()
        first='shows-tt1000001-1-1';second='shows-tt1000002-1-1'
        control=addon.WarmControl();control.promote()
        self.sync.warm_item,self.sync.warm_control=first,control
        self.sync.streams=Mock()
        self.sync.warm_search(second)
        self.assertFalse(control.cancelled.is_set())
        self.assertEqual(self.sync.warm_item,second)

    def test_play_restarts_an_expired_empty_detail_search(self):
        release=threading.Event();self.addCleanup(release.set)
        self.sync.streams=addon.Sync.streams.__get__(self.sync)
        control=addon.WarmControl()
        search=addon.StreamSearch([0],lambda _:release.wait(2) or [],control)
        search.deadline=time.monotonic()-1
        key=(self.sync.config_version,'series','tt1000001:1:1',())
        self.sync.stream_searches[key]=search
        self.assertIsNot(self.sync.streams('series','tt1000001:1:1',self.config,()),search)
        self.assertTrue(control.cancelled.is_set())

    def test_later_streams_become_persistent_measured_versions(self):
        self.config['catalogs']=[self.catalog]
        self.seed()
        vid='shows-tt1000001-1-1'
        self.sync.cache_update(self.sync.path('info',vid),{'stream':'first'})
        streams=[{'url':'https://streams.invalid/first','behaviorHints':{'filename':'first'}},
                 *[{'url':f'https://streams.invalid/{n}','behaviorHints':{'filename':f'next-{n}'}} for n in range(7)]]
        self.sync.playback_searches[vid]=streams
        self.sync.streams=Mock(side_effect=AssertionError('the first search should be reused'))
        self.sync.prefetch=Mock()
        with open(self.sync.path('info',vid)) as f:self.assertNotIn('variants',json.load(f))
        with patch.object(addon,'opens',side_effect=lambda url,headers=None,timeout=None:url), \
             patch.object(addon.time,'sleep') as delay:
            self.sync.started_stream(vid)
            self.sync.version_pool.shutdown(wait=True)
        delay.assert_called_once_with(addon.VERSION_PROBE_DELAY)
        with open(self.sync.path('info',vid)) as f:variants=json.load(f)['variants']
        self.assertEqual(len(variants),5)
        for variant in variants:
            with open(self.sync.path('info',variant)) as f:info=json.load(f)
            self.assertEqual(info['variant_stream'].startswith('next-'),True)
            self.assertNotEqual(info['item']['release'],'stremio:tt1000001')
        self.sync.once()
        snapshots=[call.args[2] for call in self.sync.rex.call_args_list if call.args[1].endswith('/snapshot')]
        self.assertEqual(len(snapshots),1)
        self.assertEqual(len(snapshots[0]['items']),8)
        self.assertEqual(len({item['id'] for item in snapshots[0]['items']}),8)

    def test_snapshot_reuses_real_probe_without_stream_lookup(self):
        self.config['catalogs']=[self.catalog]
        self.seed()
        with open(self.sync.path(addon.PROBES,'shows-tt1000001-1-1'),'w') as f:json.dump(self.sync.probe.return_value,f)
        self.sync.once()
        items=self.sync.rex.call_args.args[2]['items']
        self.assertEqual(items[0]['media_info']['streams'][0]['codec_name'],'hevc')
        self.assertIn('provisional',items[1]['media_info']['format']['tags']['comment'])
        self.sync.streams.assert_not_called();self.sync.probe.assert_not_called()

    def test_next_episode_crosses_season_boundary_without_crossing_shows(self):
        with patch.object(addon,'get_json',side_effect=lambda url: {'metas':[{'id':'tt1000001'}]} if url==self.catalog['url'] else {'meta':{'videos':[{'season':2,'episode':1},{'season':1,'episode':9}]}}):
            self.seed()
        with open(self.sync.path('info','shows-tt1000001-1-9')) as f:self.assertEqual(json.load(f)['next'],'shows-tt1000001-2-1')
        with open(self.sync.path('info','shows-tt1000001-2-1')) as f:self.assertIsNone(json.load(f)['next'])

    def test_probe_transport_bypasses_recursive_playback_preparation(self):
        import subprocess
        with patch.object(addon.subprocess,'run',return_value=subprocess.CompletedProcess([],0,b'{"streams":[{}]}',b'')) as run:
            addon.Sync.probe(self.sync,'example',self.catalog)
        self.assertTrue(run.call_args.args[0][-1].endswith('/example.probe'))

    def test_later_snapshot_chunk_sees_concurrent_playback_probe(self):
        self.config['catalogs']=[self.catalog]
        def meta(url):return {'metas':[{'id':'tt1000001'}]} if url==self.catalog['url'] else {'meta':{'videos':[{'season':1,'episode':n} for n in range(1,202)]}}
        snapshots=[]
        def publish(method,path,body,*args):
            if path.endswith('/snapshot'):
                snapshots.append(body)
                if body['part']==0:
                    with open(self.sync.path(addon.PROBES,'shows-tt1000001-1-201'),'w') as f:json.dump(self.sync.probe.return_value,f)
            return {}
        self.sync.rex.side_effect=publish
        with patch.object(addon,'get_json',side_effect=meta):self.sync.once()
        self.assertEqual(len(snapshots),2)
        self.assertEqual(snapshots[1]['items'][0]['media_info']['streams'][0]['codec_name'],'hevc')

    def test_playback_can_publish_between_snapshot_chunks_and_is_replayed(self):
        self.config['catalogs']=[self.catalog]
        self.config['feed_batch_size']=200
        self.catalog['limit']=1
        with patch.object(addon,'get_json',side_effect=lambda url: {'metas':[{'id':'tt1000001'}]} if url==self.catalog['url'] else {'meta':{'videos':[{'season':1,'episode':n} for n in range(1,202)]}}):
            self.seed()
            with open(self.sync.path('info','shows-tt1000001-1-1')) as handle:
                measured=json.load(handle)['item']
            measured['media_info']=self.sync.probe.return_value
            published=[]
            self.sync.rex.side_effect=lambda method,path,body,*args: published.append((path,body)) or {}
            original=self.sync.publish
            def publish(*args):
                answer=original(*args)
                if args[2].endswith('/snapshot') and args[3]['part']==0:
                    worker=threading.Thread(target=lambda:self.sync.publish_playback('shows-tt1000001-1-1',measured,self.config,0))
                    worker.start();worker.join(2)
                    self.assertFalse(worker.is_alive(),'playback waited for the whole snapshot')
                return answer
            self.sync.publish=publish
            self.sync.once()
        paths=[path for path,_ in published]
        first=paths.index('/rex/feed/stremio/snapshot')
        self.assertIn('/rex/feed/stremio/items',paths[first+1:-1],paths)
        self.assertEqual(paths[-1],'/rex/feed/stremio/items')

    def test_playback_skips_placeholder_and_persists_measured_probe_in_current_cache(self):
        self.seed()
        self.sync.resolve=Mock(side_effect=['https://stream.invalid/placeholder','https://stream.invalid/real'])
        self.sync.refuse=Mock(return_value=True)
        real={'format':{'format_name':'matroska,webm','duration':'1800'},'streams':[{'codec_type':'video','codec_name':'hevc'}]}
        self.sync.probe.side_effect=[dict(real,format=dict(real['format'],duration='10')),real]
        self.assertEqual(self.sync.prepare('shows-tt1000001-1-1',prefetch=False),'https://stream.invalid/real')
        self.sync.refuse.assert_called_once()
        with open(self.sync.path(addon.PROBES,'shows-tt1000001-1-1')) as handle:
            self.assertEqual(json.load(handle),real)

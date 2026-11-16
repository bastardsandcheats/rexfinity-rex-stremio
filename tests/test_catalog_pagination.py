import unittest
from unittest.mock import patch
import rex_stremio as addon


class Pagination(unittest.TestCase):
    def setUp(self):
        self.config=dict(addon.DEFAULTS,lazy_catalogs=True,addons=[{'url':'https://catalog.invalid/manifest.json','manifest':{'catalogs':[{'type':'movie','id':'top','extra':[{'name':'skip'}]}]}}])
        self.catalog=dict(type='movie',url='https://catalog.invalid/catalog/movie/top.json',limit=3)
        self.sync=addon.Sync(self.config)
        self.addCleanup(self.sync.prefetch_pool.shutdown)

    def test_declared_pages_fill_collection_limit_despite_overlap(self):
        with patch.object(addon,'get_json',side_effect=[{'metas':[{'id':'tt1'},{'id':'tt2'}]},{'metas':[{'id':'tt2'},{'id':'tt3'}]}]) as read:
            answer=self.sync.catalog_answer(self.catalog,self.config)
        self.assertEqual([x['id'] for x in answer['metas']],['tt1','tt2','tt3'])
        self.assertTrue(read.call_args.args[0].endswith('/skip=2.json'))

    def test_provider_ignoring_skip_stops_without_loop(self):
        with patch.object(addon,'get_json',return_value={'metas':[{'id':'tt1'}]}) as read:
            self.assertEqual(len(self.sync.catalog_answer(self.catalog,self.config)['metas']),1)
        self.assertEqual(read.call_count,2)

    def test_failed_page_marks_partial_and_keeps_first_page(self):
        with patch.object(addon,'get_json',side_effect=[{'metas':[{'id':'tt1'}]},RuntimeError('offline')]):
            answer=self.sync.catalog_answer(self.catalog,self.config)
        self.assertTrue(answer['_incomplete'])
        self.assertEqual(answer['metas'],[{'id':'tt1'}])

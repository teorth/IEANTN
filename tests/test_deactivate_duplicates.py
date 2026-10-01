from test_ieantn import FixtureRepo, LITERATURE, ieantn


class TestDuplicateDeactivation(FixtureRepo):
    def test_repeated_node_retains_original_status(self):
        self.write_node('A.v1', LITERATURE, status='awaiting-solution')
        self.assertTrue(ieantn.deactivate(['A.v1', 'A.v1'], 'Parked.'))
        meta = ieantn.load_nodes(include_inactive=True)['A.v1']['node']
        self.assertEqual(meta['status_before_deactivation'], 'awaiting-solution')
        self.assertTrue(ieantn.reactivate('A.v1'))
        self.assertEqual(ieantn.load_nodes()['A.v1']['node']['status'], 'awaiting-solution')

from test_ieantn import FixtureRepo, LITERATURE, ieantn


class TestInactiveOnlyGraph(FixtureRepo):
    def test_inactive_reason_is_required_even_without_live_nodes(self):
        directory = self.write_node('A.v1', LITERATURE, status='inactive')
        self.assertFalse(ieantn.check_graph())
        path = directory / 'formalization.yaml'
        text = path.read_text(encoding='utf-8')
        path.write_text(text.replace('  status: inactive\n',
                                    '  status: inactive\n  inactive_reason: Parked.\n'),
                        encoding='utf-8')
        self.assertTrue(ieantn.check_graph())

    def test_empty_repository_still_passes(self):
        self.assertTrue(ieantn.check_graph())

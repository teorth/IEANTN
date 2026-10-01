from test_ieantn import FixtureRepo, LITERATURE, ieantn


class TestVersionProgress(FixtureRepo):
    def test_new_version_does_not_inherit_solution_progress(self):
        self.write_node('A.v1', LITERATURE + '''
  progress:
    solution: Solutions/A.v1/
    state: in-progress
    remaining_holes: 7
''')
        self.assertTrue(ieantn.new_version('A'))
        nodes = ieantn.load_nodes()
        self.assertIn('progress', nodes['A.v1']['conclusions'][0])
        self.assertNotIn('progress', nodes['A.v2']['conclusions'][0])
        self.assertFalse((self.root / 'Solutions/A.v2').exists())

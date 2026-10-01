from test_ieantn import FixtureRepo, LITERATURE, ieantn


class TestVersionReferences(FixtureRepo):
    def test_other_family_suffix_and_version_prefix_are_preserved(self):
        directory = self.write_node('A.v1', LITERATURE)
        self.write_node('BA.v1', LITERATURE)
        path = directory / 'Conclusions.lean'
        path.write_text('import IEANTN.Nodes.BA.v1.Conclusions\n'
                        '-- A.v10 is a different version; BA.v1 is another family.\n'
                        'namespace A.v1\ndef main : Prop := BA.v1.main\nend A.v1\n',
                        encoding='utf-8')
        self.assertTrue(ieantn.new_version('A'))
        copied = (directory.parent / 'v2/Conclusions.lean').read_text(encoding='utf-8')
        self.assertIn('namespace A.v2', copied)
        self.assertIn('IEANTN.Nodes.BA.v1.Conclusions', copied)
        self.assertIn(':= BA.v1.main', copied)
        self.assertIn('A.v10 is a different version', copied)

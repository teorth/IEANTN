from test_ieantn import FixtureRepo, ieantn


class TestCommentBoundaries(FixtureRepo):
    def test_comment_separates_import_keyword_from_module(self):
        path = self.root / 'IEANTN/Vocabulary/Bad.lean'
        path.write_text('import/- explanation -/Solutions.A\n', encoding='utf-8')
        self.assertEqual(ieantn.imports_of(path), ['Solutions.A'])
        self.assertFalse(ieantn.check_closure())

    def test_multiline_comment_preserves_next_import(self):
        path = self.root / 'x.lean'
        path.write_text('import Mathlib/- nested /- comment -/\n-/import Solutions.A\n',
                        encoding='utf-8')
        self.assertEqual(ieantn.imports_of(path), ['Mathlib', 'Solutions.A'])

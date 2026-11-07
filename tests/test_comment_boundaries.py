import re

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

    def test_a_string_cannot_open_a_block_comment(self):
        """`/-` inside a string is text. Treating it as a comment hid the next import."""
        path = self.root / 'x.lean'
        path.write_text('def s := "/-"\nimport Solutions.A\n-/\n', encoding='utf-8')
        self.assertEqual(ieantn.imports_of(path), ['Solutions.A'])

    def test_sorry_inside_a_string_is_not_a_hole(self):
        text = 'def s := "this is not a sorry"\ntheorem t : True := trivial\n'
        self.assertIsNone(re.search(r'\bsorry\b', ieantn.strip_lean_comments(text)))

    def test_a_string_cannot_hide_a_later_sorry(self):
        text = 'def s := "--"\ntheorem t : True := sorry\n'
        self.assertIsNotNone(re.search(r'\bsorry\b', ieantn.strip_lean_comments(text)))

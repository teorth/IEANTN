import contextlib
import io
import re

from test_ieantn import FixtureRepo, ieantn


class TestRawStringBoundaries(FixtureRepo):
    def test_raw_string_does_not_hide_a_later_sorry(self):
        text = 'def s := r#"a " quote"#\nexample : True := by sorry\n'
        self.assertIsNotNone(re.search(r'\bsorry\b', ieantn.strip_lean_comments(text)))

    def test_import_rewriting_leaves_raw_string_contents_unchanged(self):
        literal = 'def s := r#"a " quote\nimport Helper\nend"#\n'
        text = 'import Helper\n' + literal
        self.assertEqual(
            ieantn.rewrite_vendored_imports(text, {'Helper': 'vendored.A.v1.Helper'}),
            'import vendored.A.v1.Helper\n' + literal,
        )

    def test_raw_delimiters_require_all_their_hashes(self):
        for width in [1, 2, 4]:
            with self.subTest(width=width):
                hashes = '#' * width
                shorter = '"' + '#' * (width - 1)
                literal = f'r{hashes}"λ {shorter} -- /- sorry\nimport Fake\nend"{hashes}'
                text = f'def s := {literal}\ndef marker := true\n'
                stripped = ieantn.strip_lean_comments(text)
                self.assertEqual(len(stripped), len(text))
                self.assertEqual([i for i, c in enumerate(stripped) if c == '\n'],
                                 [i for i, c in enumerate(text) if c == '\n'])
                self.assertIsNone(re.search(r'\bsorry\b', stripped))
                self.assertEqual(ieantn.IMPORT_RE.findall(stripped), [])
                self.assertEqual(stripped.index('def marker'), text.index('def marker'))

    def test_zero_hash_raw_strings_do_not_treat_backslash_as_an_escape(self):
        text = 'def s := r"literal ' + '\\' + '"\nexample : True := by sorry\n'
        self.assertIsNotNone(re.search(r'\bsorry\b', ieantn.strip_lean_comments(text)))

    def test_normal_string_gaps_keep_their_newline_positions(self):
        text = 'def s := "first ' + '\\' + '\n  second"\ndef marker := true\n'
        stripped = ieantn.strip_lean_comments(text)
        self.assertEqual([i for i, c in enumerate(stripped) if c == '\n'],
                         [i for i, c in enumerate(text) if c == '\n'])

    def test_bridge_check_rejects_a_hole_after_a_closed_raw_string(self):
        bridge = self.root / 'IEANTN/Bridges/Raw.lean'
        bridge.parent.mkdir(parents=True, exist_ok=True)
        bridge.write_text('def s := r#"a " quote"#\nexample : True := by sorry\n')
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertFalse(ieantn.check_closure())
        self.assertIn('a bridge may not contain `sorry`', output.getvalue())

    def test_a_sorry_inside_a_raw_string_is_not_a_bridge_hole(self):
        bridge = self.root / 'IEANTN/Bridges/Raw.lean'
        bridge.parent.mkdir(parents=True, exist_ok=True)
        bridge.write_text('def s := r#"a " sorry literal"#\nexample : True := True.intro\n')
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(ieantn.check_closure())

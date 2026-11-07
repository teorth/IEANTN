"""Lean quoted names must not create strings, comments, imports or proof holes."""
import re

from test_ieantn import FixtureRepo, ieantn


class TestQuotedIdentifiers(FixtureRepo):
    def test_quote_in_a_name_cannot_hide_a_real_bridge_hole(self):
        self.write_bridge('def «a " quote» : Nat := 0\nexample : True := by sorry\n')
        self.assertFalse(ieantn.check_closure())

    def test_comment_delimiter_in_a_name_cannot_hide_a_real_bridge_hole(self):
        self.write_bridge('def «a /- name» : Nat := 0\nexample : True := by sorry\n')
        self.assertFalse(ieantn.check_closure())

    def test_keyword_in_a_name_is_not_a_bridge_hole(self):
        self.write_bridge('def «literal sorry» : Nat := 0\nexample : True := by trivial\n')
        self.assertTrue(ieantn.check_closure())

    def test_a_multiline_name_cannot_invent_an_import(self):
        path = self.write_bridge('import Mathlib.Data.Nat.Basic\ndef «a\nimport External\nname» : Nat := 0\n')
        self.assertEqual(ieantn.imports_of(path), ["Mathlib.Data.Nat.Basic"])
        self.assertTrue(ieantn.check_closure())

    def test_quoted_external_module_is_still_a_visible_disallowed_import(self):
        path = self.write_bridge('import «External"name»\n')
        self.assertTrue(ieantn.imports_of(path))
        self.assertFalse(ieantn.check_closure())

    def test_quoted_imports_and_open_names_keep_their_original_spelling(self):
        path = self.write_bridge('import Mathlib.«Data».Nat.Basic\nopen «Real»\n')
        self.assertEqual(ieantn.imports_of(path), ['Mathlib.«Data».Nat.Basic'])
        self.assertEqual(ieantn.opens_of(path), ['open «Real»'])

    def test_import_rewriting_preserves_quoted_suffixes_and_ignores_names(self):
        source = 'import Helper.«Part»\ndef «a\nimport Helper\nname» : Nat := 0\n'
        # A project can contain both Helper.lean and Helper/Part.lean. Keep
        # this fixture valid for both root-prefix and full-module export maps.
        modules = {"Helper": "Vendor.Helper", "Helper.Part": "Vendor.Helper.«Part»"}
        rewritten = ieantn.rewrite_vendored_imports(source, modules)
        self.assertEqual(rewritten, source.replace('import Helper.«Part»',
                                                   'import Vendor.Helper.«Part»'))

    def test_nested_opening_guillemet_is_part_of_the_name_and_offsets_survive(self):
        source = 'def «α « name /- "\n sorry» : Nat := 0\nexample : True := by sorry\n'
        masked = ieantn.strip_lean_comments(source)
        self.assertEqual(len(masked), len(source))
        self.assertEqual([i for i, char in enumerate(masked) if char == "\n"],
                         [i for i, char in enumerate(source) if char == "\n"])
        self.assertEqual([match.start() for match in re.finditer(r"\bsorry\b", masked)],
                         [source.rindex("sorry")])

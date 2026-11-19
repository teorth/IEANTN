"""Check the original YAML before normalizing its Palomar-facing fields."""
import contextlib
import importlib.util
import io
import pathlib
import sys
import tempfile
import types
import unittest
from unittest import mock

import yaml

SPEC = importlib.util.spec_from_file_location(
    "check_palomar_metadata",
    pathlib.Path(__file__).resolve().parent.parent / "scripts" / "check_palomar_metadata.py",
)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


class StrictLoader(yaml.SafeLoader):
    """Contract test double: reject syntax safe_load would normalize away."""

    def construct_mapping(self, node, deep=False):
        keys = set()
        for key_node, _ in node.value:
            if key_node.tag == "tag:yaml.org,2002:merge":
                raise ValueError("YAML merge keys are not allowed")
            key = self.construct_object(key_node, deep=deep)
            if key in keys:
                raise ValueError(f"duplicate key: {key}")
            keys.add(key)
        return super().construct_mapping(node, deep=deep)


METADATA = """\
version: v0.4
node: {id: Example.v1, status: stub}
conclusions: []
project:
  name: Example
  description: A metadata validation fixture.
  authors: &authors [Example Author]
  responsible_maintainers: *authors
  license: Apache-2.0
classification: {arxiv: [math.NT], msc2020: [11N05]}
sources:
  - {title: Example source, type: paper, relationship: formalizes}
automation: {methods: [{method: manual}]}
review: {status: unreviewed}
"""


class TestPalomarMetadata(unittest.TestCase):
    def check_nodes(self, documents):
        loaded_documents = []

        def load_metadata(path):
            data = yaml.load(path.read_text(encoding="utf-8"), Loader=StrictLoader)
            if not isinstance(data, dict):
                raise ValueError("must contain one top-level mapping")
            loaded_documents.append(data)
            return data

        contract = types.SimpleNamespace(
            load_formalization_metadata=mock.Mock(side_effect=load_metadata),
            normalized_provenance=lambda data: {"result_origin": "source-based"},
        )
        package = types.ModuleType("scripts")
        package.submission_contract = contract
        output = io.StringIO()
        with tempfile.TemporaryDirectory() as temporary:
            nodes = pathlib.Path(temporary) / "IEANTN" / "Nodes"
            for name, text in documents.items():
                directory = nodes / name / "v1"
                directory.mkdir(parents=True)
                (directory / "formalization.yaml").write_text(text, encoding="utf-8")
            with mock.patch.object(checker, "NODES_DIR", nodes), \
                 mock.patch.object(sys, "argv", ["check_palomar_metadata.py", temporary]), \
                 mock.patch.object(sys, "path", sys.path.copy()), \
                 mock.patch.dict(sys.modules, {"scripts": package}), \
                 contextlib.redirect_stdout(output):
                result = checker.main()
        return result, output.getvalue(), loaded_documents

    def test_plain_metadata_strips_only_ieantn_fields(self):
        result, output, loaded = self.check_nodes({"A": METADATA})
        self.assertEqual(result, 0)
        self.assertIn("ok    A.v1", output)
        expected = yaml.safe_load(METADATA)
        expected.pop("node")
        expected.pop("conclusions")
        self.assertEqual(loaded, [expected])

    def test_duplicate_keys_fail_without_skipping_the_next_node(self):
        duplicate = METADATA.replace("  name: Example\n", "  name: Old\n  name: Example\n")
        result, output, loaded = self.check_nodes({"A": duplicate, "B": METADATA})
        self.assertEqual(result, 1)
        self.assertIn("FAIL  A.v1: duplicate key: name", output)
        self.assertIn("ok    B.v1", output)
        self.assertIn("1 node(s) would be rejected", output)
        self.assertEqual(len(loaded), 1)

    def test_merge_keys_are_not_silently_expanded(self):
        merged = METADATA.replace("  name: Example\n", "  <<: {name: Example}\n")
        result, output, loaded = self.check_nodes({"A": merged})
        self.assertEqual(result, 1)
        self.assertIn("FAIL  A.v1: YAML merge keys are not allowed", output)
        self.assertEqual(loaded, [])

    def test_merge_keys_only_in_ieantn_fields_are_still_ignored(self):
        ignored = METADATA.replace(
            "node: {id: Example.v1, status: stub}\n",
            "node:\n  <<: {id: Example.v1, status: stub}\n",
        )
        result, output, loaded = self.check_nodes({"A": ignored})
        self.assertEqual(result, 0)
        self.assertIn("ok    A.v1", output)
        self.assertNotIn("node", loaded[0])
        self.assertNotIn("conclusions", loaded[0])

    def test_empty_and_non_mapping_documents_fail_without_crashing(self):
        for text in ("", "metadata\n", "- project\n"):
            with self.subTest(text=text):
                result, output, loaded = self.check_nodes({"A": text, "B": METADATA})
                self.assertEqual(result, 1)
                self.assertIn("FAIL  A.v1: must contain one top-level mapping", output)
                self.assertIn("ok    B.v1", output)
                self.assertEqual(len(loaded), 1)

    def test_malformed_yaml_does_not_skip_other_nodes(self):
        result, output, loaded = self.check_nodes({"A": "project: [\n", "B": METADATA})
        self.assertEqual(result, 1)
        self.assertIn("FAIL  A.v1:", output)
        self.assertIn("ok    B.v1", output)
        self.assertEqual(len(loaded), 1)

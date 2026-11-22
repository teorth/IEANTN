"""The RS12 serial build must see real imports and ignore commented ones.

`build_sequential` used to take every line that looked like `import` and decode
Lean with the process locale. A nested block comment names a module that is not
on disk, and the certificate files contain `ψ`, so both mistakes abort the walk
before Lake starts.
"""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / "Solutions" / "RosserSchoenfeld1962.v1" / "scripts"
sys.path.insert(0, str(SCRIPTS))

from build_sequential import build_order, imported_modules  # noqa: E402


class TestRs12BuildOrder(unittest.TestCase):
    def test_a_commented_import_is_not_a_dependency(self) -> None:
        text = textwrap.dedent(
            """\
            /-
            /- closed -/
            import RS12.Commented
            -/
            import RS12.Real
            def note : String := "import RS12.Quoted"
            """
        )
        self.assertEqual(imported_modules(text), ["RS12.Real"])

    def test_commented_module_does_not_abort_the_walk(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "RS12").mkdir()
            (root / "Solution.lean").write_text(
                "/-\nimport RS12.Missing\n-/\nimport RS12.Real\n",
                encoding="utf-8",
            )
            (root / "RS12" / "Real.lean").write_text("-- ψ\n", encoding="utf-8")
            self.assertEqual(build_order(root, root / "missing-leancert"), ["RS12.Real", "Solution"])

    def test_unicode_sources_are_read_in_an_ascii_locale(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "RS12").mkdir()
            (root / "Solution.lean").write_text("import RS12.Child\n", encoding="utf-8")
            (root / "RS12" / "Child.lean").write_text("-- ψ ≤ x\n", encoding="utf-8")
            env = os.environ.copy()
            env["LC_ALL"] = "C"
            env["PYTHONUTF8"] = "0"
            probe = textwrap.dedent(
                f"""\
                import sys
                sys.path.insert(0, {str(SCRIPTS)!r})
                from build_sequential import build_order
                from pathlib import Path
                print("\\n".join(build_order(Path({str(root)!r}), Path({str(root)!r}) / "no-leancert")))
                """
            )
            completed = subprocess.run(
                [sys.executable, "-c", probe],
                capture_output=True,
                text=True,
                encoding="utf-8",
                env=env,
                check=False,
            )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stdout.splitlines(), ["RS12.Child", "Solution"])


if __name__ == "__main__":
    unittest.main()

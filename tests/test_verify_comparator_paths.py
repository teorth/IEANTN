"""Shell verifier path preflight, without any verification tools or dependencies."""
import pathlib
import shutil
import subprocess
import tempfile
import unittest


class TestComparatorScriptPaths(unittest.TestCase):
    def test_repository_root_ignores_cdpath(self):
        bash = shutil.which("bash")
        dirname = shutil.which("dirname")
        if not bash or not dirname:
            self.skipTest("requires bash and dirname")
        bash = str(pathlib.Path(bash).resolve())
        dirname = str(pathlib.Path(dirname).resolve())
        source = pathlib.Path(__file__).resolve().parents[1] / "scripts/verify-comparator.sh"
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory) / "checkout with spaces"
            (root / "scripts").mkdir(parents=True)
            script = root / "scripts/verify-comparator.sh"
            shutil.copyfile(source, script)
            solution = root / "Solutions/Lcm.v1"
            solution.mkdir(parents=True)
            (solution / "comparator.json").write_text("{}", encoding="utf-8")
            commands = pathlib.Path(directory) / "bin"
            commands.mkdir()
            (commands / "dirname").symlink_to(dirname)
            decoy = pathlib.Path(directory) / "another checkout"
            (decoy / "scripts").mkdir(parents=True)

            # PATH contains only dirname. Reaching the missing-cargo guard proves
            # root lookup worked, without permitting any build or fetch command.
            for invocation in ("scripts/verify-comparator.sh", str(script)):
                for cdpath in ("", ".", str(decoy)):
                    with self.subTest(invocation=invocation, cdpath=cdpath):
                        result = subprocess.run(
                            [bash, invocation, "Lcm.v1"],
                            cwd=root,
                            env={"PATH": str(commands), "CDPATH": cdpath},
                            capture_output=True,
                            encoding="utf-8",
                            timeout=5,
                        )
                        self.assertEqual(result.returncode, 1, result.stderr)
                        self.assertEqual(result.stdout, "")
                        self.assertEqual(result.stderr, "error: cargo is required\n")

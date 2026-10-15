"""Exercise the CI verdict with real Lake projects and bundled checkers on Linux."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

PROJECT = Path(__file__).resolve().parents[1]
VERIFY = PROJECT / "scripts/verify-comparator.sh"
HAS_SANDBOX = sys.platform == "linux" and shutil.which("bwrap") is not None


class ComparatorVerdictTests(unittest.TestCase):
    @unittest.skipIf(HAS_SANDBOX, "sandbox is available")
    def test_requires_sandbox(self):
        result = subprocess.run(["bash", str(VERIFY)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("bwrap", result.stdout + result.stderr)

    @unittest.skipUnless(HAS_SANDBOX, "requires Linux and real bubblewrap")
    def test_real_comparator_verdicts(self):
        challenge = "theorem Check.solve : True ∧ True := by sorry\n"
        cases = [
            ("open", challenge, 0, "Open question verified"),
            ("proved", "theorem Check.solve : True ∧ True := ⟨True.intro, True.intro⟩\n",
             0, "Proof accepted"),
            ("statement_mismatch", "theorem Check.solve : True := by sorry\n", 1, None),
            ("extra_axiom", "axiom untrusted : True\n"
             "theorem Check.solve : True ∧ True := ⟨by sorry, untrusted⟩\n", 1, None),
        ]
        for name, solution, expected_status, message in cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "scripts").mkdir()
                shutil.copy2(VERIFY, root / "scripts/verify-comparator.sh")
                shutil.copy2(PROJECT / "lean-toolchain", root / "lean-toolchain")
                (root / "lakefile.toml").write_text(
                    'name = "comparator_verdict_test"\n'
                    '[[lean_lib]]\nname = "Challenge"\n'
                    '[[lean_lib]]\nname = "Solution"\n'
                )
                (root / "Challenge.lean").write_text(challenge)
                (root / "Solution.lean").write_text(solution)
                (root / "comparator.json").write_text(json.dumps({
                    "challenge_module": "Challenge",
                    "solution_module": "Solution",
                    "theorem_names": ["Check.solve"],
                    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                }))
                subprocess.run(["lake", "update"], cwd=root, check=True,
                               capture_output=True, text=True)
                result = subprocess.run(["bash", str(root / "scripts/verify-comparator.sh")],
                                        cwd=PROJECT, capture_output=True, text=True)
                output = result.stdout + result.stderr
                self.assertEqual(result.returncode, expected_status, output)
                if message:
                    self.assertIn(message, output)
                    # con-ron declines any sorryAx, so only the strict pass runs it.
                    kernels = ("Lean default", "nanoda") + (("con-ron",) if name == "proved" else ())
                    for kernel in kernels:
                        self.assertIn(f"{kernel} kernel accepts the solution", output)
                    if name == "open":
                        self.assertNotIn("con-ron", output)
                if name == "extra_axiom":
                    self.assertIn("Illegal axiom detected: 'sorryAx'", output)
                    self.assertIn("Illegal axiom detected: 'untrusted'", output)


if __name__ == "__main__":
    unittest.main()

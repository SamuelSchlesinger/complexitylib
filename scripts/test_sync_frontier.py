"""Check the mechanical rewriting of `sync_frontier.py` and its library-owned modules."""

import unittest

from sync_frontier import CSLIB, MATHLIB, OWNED, PATCHES, ROOT, TARGET, module_path, rewrite


class SyncFrontierTests(unittest.TestCase):
    def test_module_paths(self):
        self.assertEqual(module_path("Sweep.lean"), TARGET / "Sweep.lean")
        self.assertEqual(module_path("Layouts/Kernel.lean"), TARGET / "Layouts/Kernel.lean")
        self.assertEqual(module_path("ForCslib/Program.lean"), CSLIB)
        self.assertEqual(module_path("ForMathlib/SetCard.lean"), MATHLIB / "SetCard.lean")

    def test_rewrite(self):
        modules = {"Frontier.Sweep": "Complexitylib.Circuits.Frontier.Sweep"}
        source = (
            "public import Frontier.Sweep\nimport Mathlib.Tactic\n"
            "namespace Frontier.Gaussian\nopen Frontier\n"
            "theorem t : p.trace_congr = H.cutFinset S := rfl\nend Frontier.Gaussian\n"
        )
        self.assertEqual(rewrite(source, modules), (
            "public import Complexitylib.Circuits.Frontier.Sweep\nimport Mathlib.Tactic\n"
            "namespace Complexity.Frontier.Gaussian\nopen Complexity.Frontier\n"
            "theorem t : p.trace_congr_of_upstream = H.crossingFinset S := rfl\n"
            "end Complexity.Frontier.Gaussian\n"
        ))

    def test_owned_modules_exist(self):
        for module in OWNED:
            with self.subTest(module=module):
                self.assertTrue((TARGET / f"{module}.lean").is_file())

    def test_patches_name_mirrored_files(self):
        for relative, old, new in PATCHES:
            with self.subTest(path=relative):
                self.assertTrue((ROOT / relative).is_file())
                self.assertNotEqual(old, new)


if __name__ == "__main__":
    unittest.main()

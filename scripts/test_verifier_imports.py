"""Guard the neutral verifier entry point and its migrated clients."""

import unittest

import lint_style


class VerifierImportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        paths = list(lint_style.LIBRARY.rglob("*.lean"))
        paths.append(lint_style.ROOT / "Complexitylib.lean")
        _, cls.imports = lint_style.import_graph(paths)

    def closure(self, module):
        self.assertIn(module, self.imports)
        return lint_style.reachable_modules(self.imports, [module])

    def test_generic_verifier_has_no_sat_dependency(self):
        for module in (
            "Complexitylib.Classes.NP.Verifier",
            "Complexitylib.Classes.NP.Verifier.Linear",
            "Complexitylib.Classes.NP.WitnessConstruction",
        ):
            with self.subTest(module=module):
                self.assertFalse(
                    any(name.startswith("Complexitylib.SAT") for name in self.closure(module))
                )

    def test_membership_clients_use_neutral_route(self):
        for module in (
            "Complexitylib.SAT.Headline",
            "Complexitylib.SAT.ThreeSAT.Headline",
            "Complexitylib.SAT.CircuitSatisfiability.Internal",
        ):
            with self.subTest(module=module):
                reachable = self.closure(module)
                self.assertIn("Complexitylib.Classes.NP.Verifier.Linear", reachable)
                self.assertNotIn("Complexitylib.SAT.Internal.GuessVerify", reachable)
                self.assertNotIn("Complexitylib.SAT.Internal.LinearGuessVerify", reachable)

    def test_linear_route_does_not_import_padding(self):
        reachable = self.closure("Complexitylib.Classes.NP.Verifier.Linear")
        self.assertNotIn("Complexitylib.Classes.NP.Internal.Verifier", reachable)
        self.assertNotIn("Complexitylib.Classes.P.Cobham.Internal", reachable)

    def test_legacy_import_preserves_both_apis(self):
        reachable = self.closure("Complexitylib.Classes.NP.Internal.GuessVerify")
        self.assertIn("Complexitylib.Classes.NP.Verifier", reachable)
        self.assertIn("Complexitylib.SAT.Internal.LinearGuessVerify", reachable)
        self.assertIn(
            "Complexitylib.Classes.NP.Internal.GuessVerify",
            self.closure("Complexitylib.SAT.GuessVerify"),
        )


if __name__ == "__main__":
    unittest.main()

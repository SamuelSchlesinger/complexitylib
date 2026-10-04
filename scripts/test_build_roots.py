"""Keep hand-maintained copies of the build roots in step with `BUILD_ROOTS`.

`lint_environment.py` reads `BUILD_ROOTS` directly (see `test_lint_environment`),
but the axiom guard's imports and the documented and CI build commands repeat
the list. A validation root missing from the axiom guard escapes the audit.
"""

import re
import unittest

from lint_style import BUILD_ROOTS, ROOT, module_imports

# Files whose `lake build` command must name every build root.
BUILD_COMMAND_FILES = (
    "AGENTS.md",
    "CONTRIBUTING.md",
    ".github/workflows/lean_action_ci.yml",
)


class BuildRootTests(unittest.TestCase):
    def test_axiom_guard_imports_every_build_root(self):
        text = (ROOT / "scripts" / "AxiomGuard.lean").read_text(encoding="utf-8")
        imported = {entry.name for entry in module_imports(text)}
        for root in BUILD_ROOTS:
            with self.subTest(root=root):
                self.assertIn(root, imported)

    def test_build_commands_name_every_build_root(self):
        for name in BUILD_COMMAND_FILES:
            text = (ROOT / name).read_text(encoding="utf-8")
            for root in BUILD_ROOTS:
                with self.subTest(file=name, root=root):
                    pattern = rf"(?<![\w.]){re.escape(root)}(?![\w.])"
                    self.assertIsNotNone(re.search(pattern, text),
                                         f"{name} does not name {root}")


if __name__ == "__main__":
    unittest.main()

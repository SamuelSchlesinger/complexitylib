"""Check shared import metadata and the pair-builder ownership boundary."""

import subprocess
import tempfile
import unittest
from pathlib import Path

import lint_style
from audit_imports import audit, git_sources
from lint_style import ModuleImport, module_imports


class ImportAuditTests(unittest.TestCase):
    def test_header_commands_need_not_start_new_lines(self):
        self.assertEqual(module_imports("module prelude\nimport A\n"), [
            ModuleImport("A", False, False, False),
        ])
        self.assertEqual(module_imports("module import A\n"), [
            ModuleImport("A", False, False, False),
        ])
        self.assertEqual(module_imports("module\npublic import A import B\n"), [
            ModuleImport("A", True, False, False),
            ModuleImport("B", False, False, False),
        ])
        self.assertEqual(module_imports(
            "module prelude meta import all A public import B public section\n"
            'def text := "import Ignored"\n'), [
            ModuleImport("A", False, True, True),
            ModuleImport("B", True, False, False),
        ])
        self.assertEqual(module_imports("prelude import A import B\n"), [
            ModuleImport("A", True, False, False),
            ModuleImport("B", True, False, False),
        ])
        with self.assertRaisesRegex(ValueError, "unsupported module import token"):
            module_imports("module import A import all")

    def test_git_snapshot_ignores_worktree_edits(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "Complexitylib").mkdir()
            (root / "Complexitylib.lean").write_text("import Complexitylib.Example\n")
            example = root / "Complexitylib" / "Example.lean"
            example.write_text("module\npublic import Foreign.Before\n")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run([
                "git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                "commit", "-qm", "snapshot",
            ], cwd=root, check=True)
            commit, before = git_sources(root, "HEAD")
            example.write_text("module\npublic import Foreign.After\n")
            (root / "Complexitylib" / "Untracked.lean").write_text("module\n")
            self.assertEqual(git_sources(root, commit), (commit, before))
            self.assertEqual(before["Complexitylib.Example"],
                             "module\npublic import Foreign.Before\n")

    def test_shared_reader_visibility_comments_and_staging(self):
        self.assertEqual(module_imports('''/- import Ignored.Header -/
module
import A
public import B -- import Ignored.Line
private import all C
public meta import D
meta import E
public/- nested /- comment -/ -/import
  F
/-! import Ignored.Doc -/
def text := "import Ignored.String"
'''), [ModuleImport("A", False, False, False),
       ModuleImport("B", True, False, False),
       ModuleImport("C", False, False, True),
       ModuleImport("D", True, True, False),
       ModuleImport("E", False, True, False),
       ModuleImport("F", True, False, False)])
        self.assertEqual(module_imports("import A\nprivate import B\n"), [
            ModuleImport("A", True, False, False),
            ModuleImport("B", False, False, False),
        ])
        with self.assertRaisesRegex(ValueError, "unsupported module import token"):
            module_imports("public import A.«Quoted Name»\n")

    def test_source_public_and_reverse_closures_are_distinct(self):
        sources = {
            "A": "module\npublic import B\nimport C\npublic meta import Foreign\n",
            "B": "module\npublic import D\n",
            "C": "module\npublic import D\n",
            "D": "module\n",
            "Legacy": "import A\n",
        }
        result = audit(sources, ["A", "D"])
        self.assertEqual(result["A"]["source_closure"], ["A", "B", "C", "D"])
        self.assertEqual(result["A"]["public_import_closure"], ["A", "B", "D"])
        self.assertEqual(result["A"]["reverse_source_closure"], ["A", "Legacy"])
        self.assertEqual(result["D"]["reverse_source_closure_count"], 5)
        with self.assertRaisesRegex(ValueError, "No project module"):
            audit(sources, ["Missing"])

    def test_generic_pair_builder_clients_do_not_depend_on_np(self):
        paths = list(lint_style.LIBRARY.rglob("*.lean"))
        paths.append(lint_style.ROOT / "Complexitylib.lean")
        _, graph = lint_style.import_graph(paths)
        builder = "Complexitylib.Models.TuringMachine.Subroutines.PairBuild"
        legacy = "Complexitylib.Classes.NP.Internal.PairBuildTM"
        for root in (
            builder,
            "Complexitylib.Models.TuringMachine.Witness.Verifier",
            "Complexitylib.Models.TuringMachine.UTM.Internal.PairSelf",
        ):
            with self.subTest(root=root):
                self.assertIn(root, graph)
                closure = lint_style.reachable_modules(graph, [root])
                self.assertIn(builder, closure)
                self.assertFalse(any(name.startswith("Complexitylib.Classes.NP")
                                     for name in closure))
        self.assertEqual(graph[legacy], {builder})
        self.assertIn(legacy, graph["Complexitylib.SAT.Internal.GuessVerify"])


if __name__ == "__main__":
    unittest.main()

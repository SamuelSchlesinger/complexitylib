"""Regression tests for the dependency-only doc-gen4 cache staging step."""

import sqlite3
import tempfile
import unittest
from contextlib import closing
from pathlib import Path

from cache_docs_dependencies import dependency_import_key, is_dependency_marker, stage_cache
from lint_style import imported_modules, lean_code


class DependencyDocsCacheTest(unittest.TestCase):
    def test_import_reader_rejects_unsupported_tokens(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "Complexitylib.lean"
            for name in ("Mathlib.Fooα", "Mathlib.Fooβ", "«Foreign.One»",
                         "«Foreign.Two»", "Mathlib.«Quoted Name»", "Mathlib.Foo'",
                         "Mathlib.Foo?", "Mathlib."):
                with self.subTest(name=name):
                    path.write_text(f"public meta import {name}\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "unsupported module import token"):
                        imported_modules(path)
                    with self.assertRaisesRegex(ValueError, "unsupported module import token"):
                        dependency_import_key(root)

    def test_import_reader_handles_lean_header_syntax(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "Example.lean"
            path.write_text('''/- Copyright header.
import NotAnImport
-/
module
  public meta import Mathlib.Meta
private import all Mathlib.Private
meta import Mathlib.Other
import/- inline /- nested -/ comment -/Mathlib.Inline
import
  Mathlib.Multiline
/-! Module documentation mentions:
import AlsoNotAnImport
-/
def example := "import NotAStringImport"
''', encoding="utf-8")
            self.assertEqual(imported_modules(path), {
                "Mathlib.Meta", "Mathlib.Private", "Mathlib.Other",
                "Mathlib.Inline", "Mathlib.Multiline",
            })
            # Removing a meta import must also invalidate the dependency cache.
            (path.parent / "Complexitylib.lean").write_text("public meta import Mathlib.Meta\n")
            original = dependency_import_key(path.parent)
            (path.parent / "Complexitylib.lean").write_text("")
            self.assertNotEqual(dependency_import_key(path.parent), original)
        self.assertEqual(lean_code("native_/- comment -/decide"), "native_ decide")

    def test_import_key_tracks_public_external_imports(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "Complexitylib").mkdir()
            (root / "Complexitylib.lean").write_text("import Complexitylib.Example\n")
            example = root / "Complexitylib" / "Example.lean"
            example.write_text("import Mathlib.Example\n/-! Module docs. -/\ndef x := 0\n")
            original = dependency_import_key(root)
            example.write_text("import Mathlib.Example\n/-! Changed docs. -/\ndef x := 1\n")
            # Proofs, docs, and modules outside the public import graph cannot
            # change which dependency documentation is needed.
            (root / "Complexitylib" / "Validation.lean").write_text("import Mathlib.Other\n")
            self.assertEqual(dependency_import_key(root), original)
            example.write_text("import Mathlib.Example\nimport Mathlib.Other\n")
            self.assertNotEqual(dependency_import_key(root), original)
            example.write_text("import Mathlib.Other\n")
            self.assertNotEqual(dependency_import_key(root), original)
            example.write_text("import Complexitylib.Missing\n")
            with self.assertRaises(FileNotFoundError):
                dependency_import_key(root)

    def test_marker_filter(self):
        for name in ("Mathlib.Data.Nat.doc", "Mathlib.Data.Nat.doc.trace",
                     "core-Lean.doc", "core-Lean.doc.hash", "Cslib.Circuits.doc"):
            with self.subTest(name=name):
                self.assertTrue(is_dependency_marker(name))
        for name in ("Complexitylib.doc", "Complexitylib.doc.trace",
                     "Complexitylib.OldName.doc", "Complexitylib.OldName.doc.hash",
                     "Complexitylib--library.docs_built", "Mathlib--library.docs_built.trace",
                     "Complexitylib--library.docsHeader_built", "index.html",
                     "references.json", "references.json.trace", "references.json.hash"):
            with self.subTest(name=name):
                self.assertFalse(is_dependency_marker(name))

    def test_stage_preserves_dependencies_and_source(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            build, cache = root / "build", root / "cache"
            markers = build / "doc-data"
            markers.mkdir(parents=True)
            # Mirror doc-gen4's cascading ownership: module -> declaration -> tactic.
            with closing(sqlite3.connect(build / "api-docs.db")) as database:
                database.executescript("""
                    PRAGMA foreign_keys = ON;
                    CREATE TABLE modules (name TEXT PRIMARY KEY, source_url TEXT);
                    CREATE TABLE name_info (
                        module_name TEXT, name TEXT PRIMARY KEY,
                        FOREIGN KEY (module_name) REFERENCES modules(name) ON DELETE CASCADE
                    );
                    CREATE TABLE tactics (
                        name TEXT REFERENCES name_info(name) ON DELETE CASCADE
                    );
                    CREATE TABLE module_imports (
                        importer TEXT REFERENCES modules(name) ON DELETE CASCADE,
                        imported TEXT
                    );
                """)
                for module in ("Mathlib.Example", "Cslib.Example", "Complexitylib",
                               "Complexitylib.Renamed", "Complexitylib.Removed"):
                    database.execute("INSERT INTO modules VALUES (?, ?)", (module, module))
                    database.execute("INSERT INTO name_info VALUES (?, ?)", (module, module))
                    database.execute("INSERT INTO tactics VALUES (?)", (module,))
                    database.execute("INSERT INTO module_imports VALUES (?, 'Init')", (module,))
                    for suffix in (".doc", ".doc.trace", ".doc.hash"):
                        (markers / (module + suffix)).write_text("analysis", encoding="utf-8")
                database.commit()
            (markers / "core-Lean.doc").touch()
            (markers / "references.json").write_text("[]", encoding="utf-8")
            (markers / "Complexitylib--library.docs_built").touch()
            (build / "doc").mkdir()
            (build / "doc" / "Removed.html").write_text("old HTML", encoding="utf-8")
            (build / "doc-manifest.json").write_text("[]", encoding="utf-8")
            # A restored cache can already exist; the new one replaces it completely.
            cache.mkdir()
            (cache / "old-marker").touch()

            stage_cache(build, cache)

            expected = {"Mathlib.Example", "Cslib.Example"}
            with closing(sqlite3.connect(cache / "api-docs.db")) as database:
                for table, column in (("modules", "name"), ("name_info", "module_name"),
                                      ("tactics", "name"), ("module_imports", "importer")):
                    rows = database.execute(f"SELECT {column} FROM {table}").fetchall()
                    self.assertEqual({row[0] for row in rows}, expected)
                self.assertEqual(database.execute("PRAGMA foreign_key_check").fetchall(), [])
                self.assertEqual(database.execute("PRAGMA integrity_check").fetchone(), ("ok",))
            self.assertEqual({p.name for p in cache.iterdir()}, {"api-docs.db", "doc-data"})
            self.assertEqual(
                {p.name for p in (cache / "doc-data").iterdir()},
                {module + suffix for module in expected
                 for suffix in (".doc", ".doc.trace", ".doc.hash")}
                | {"core-Lean.doc"},
            )
            with closing(sqlite3.connect(build / "api-docs.db")) as database:
                self.assertEqual(database.execute("SELECT count(*) FROM modules").fetchone(), (5,))
            self.assertTrue((build / "doc" / "Removed.html").is_file())
            self.assertTrue((markers / "Complexitylib.Removed.doc").is_file())

    def test_missing_database_does_not_replace_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache = root / "cache"
            cache.mkdir()
            sentinel = cache / "previous-cache"
            sentinel.touch()
            with self.assertRaises(FileNotFoundError):
                stage_cache(root / "missing-build", cache)
            self.assertTrue(sentinel.exists())


if __name__ == "__main__":
    unittest.main()

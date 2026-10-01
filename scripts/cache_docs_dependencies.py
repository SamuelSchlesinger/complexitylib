#!/usr/bin/env python3
"""Stage doc-gen4's dependency analysis cache, without project or rendered docs.

Run after a successful documentation build. The workflow caches the staged
directory separately from Lean CI's compiled-library cache, and restores its
contents into an otherwise fresh docbuild/.lake/build before the next build.

The SQLite schema and marker names are those of the pinned doc-gen4 release.
Deleting project modules with foreign keys enabled also deletes their
declarations, tactics, imports, and source URLs. In particular, removed or
renamed project modules cannot survive in the next build's database or search
index. All project analysis and all HTML are generated again from the checkout.
"""

import hashlib
import shutil
import sqlite3
import sys
import tempfile
from contextlib import closing
from pathlib import Path

from lint_style import imported_modules

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "docbuild" / ".lake" / "build"
CACHE = ROOT / "docbuild" / ".lake" / "dependency-docs-cache"


def dependency_import_key(root: Path) -> str:
    """Fingerprint external imports reachable from the public root module.

    Changing only project proofs need not invalidate dependency analysis.
    Adding/removing an external import does: doc-gen4's tactics index includes
    all database rows, so retaining an unused dependency would be observable.
    Use the same import reader as the repository's import-graph style gate.
    """
    pending, seen, external = ["Complexitylib"], set(), set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        path = root.joinpath(*name.split(".")).with_suffix(".lean")
        for imported in imported_modules(path):
            if imported == "Complexitylib" or imported.startswith("Complexitylib."):
                pending.append(imported)
            else:
                external.add(imported)
    return hashlib.sha256("\n".join(sorted(external)).encode()).hexdigest()


def is_dependency_marker(name: str) -> bool:
    """Keep analysis markers only; never retain project or HTML-build markers."""
    if name.startswith("Complexitylib."):
        return False
    # The cheap bibliography prepass must run again: besides doc-data it also
    # creates references.bib in the fresh (uncached) HTML directory.
    return name.endswith((".doc", ".doc.trace", ".doc.hash"))


def stage_cache(build: Path, cache: Path) -> None:
    """Copy the finished database and retain only dependency documentation."""
    database = build / "api-docs.db"
    if not database.is_file():
        raise FileNotFoundError(f"Documentation database not found: {database}")
    cache.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=cache.parent) as temporary:
        staged = Path(temporary) / "cache"
        staged.mkdir()
        # SQLite backup includes committed WAL data without copying live locks.
        with closing(sqlite3.connect(database.as_uri() + "?mode=ro", uri=True)) as source:
            with closing(sqlite3.connect(staged / "api-docs.db")) as target:
                source.backup(target)
                target.execute("PRAGMA foreign_keys = ON")
                target.execute(
                    "DELETE FROM modules WHERE name = 'Complexitylib' "
                    "OR name GLOB 'Complexitylib.*'"
                )
                target.commit()
                if target.execute("PRAGMA foreign_key_check").fetchone():
                    raise RuntimeError("Documentation cache has dangling foreign keys")
                # Make the cached file self-contained and reclaim removed rows.
                target.execute("PRAGMA journal_mode = DELETE")
                target.execute("VACUUM")
        markers = staged / "doc-data"
        markers.mkdir()
        for path in sorted((build / "doc-data").iterdir()):
            if path.is_file() and is_dependency_marker(path.name):
                shutil.copy2(path, markers / path.name)
        if cache.exists():
            shutil.rmtree(cache)
        staged.rename(cache)


if __name__ == "__main__":
    if sys.argv[1:] == ["--imports-key"]:
        print(dependency_import_key(ROOT))
    elif not sys.argv[1:]:
        stage_cache(BUILD, CACHE)
        print(f"Staged dependency documentation cache: {CACHE.relative_to(ROOT)}")
    else:
        raise SystemExit("usage: cache_docs_dependencies.py [--imports-key]")

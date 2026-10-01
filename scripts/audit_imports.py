#!/usr/bin/env python3
"""Audit project source dependencies at an immutable Git commit.

Usage: python3 scripts/audit_imports.py --ref HEAD MODULE [MODULE ...]

Counts include each root. Public-import closures follow syntactically public
edges; they are not elaborator environment sizes or declaration counts. Reverse
source closures predict possible rebuild fan-out, not actual recompilation.
External imports are excluded. No files or build caches are modified.
"""

import argparse
import io
import json
import subprocess
import tarfile
from pathlib import Path, PurePosixPath

from lint_style import ROOT, module_imports, reachable_modules


def git_sources(root: Path, ref: str) -> tuple[str, dict[str, str]]:
    """Read library Lean sources directly from a fixed Git tree, without checkout."""
    commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", "--end-of-options", f"{ref}^{{commit}}"],
        cwd=root, text=True,
    ).strip()
    archive = subprocess.check_output(
        ["git", "archive", commit, "Complexitylib", "Complexitylib.lean"], cwd=root,
    )
    sources = {}
    with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
        for member in tree:
            if member.isfile() and member.name.endswith(".lean"):
                name = ".".join(PurePosixPath(member.name).with_suffix("").parts)
                sources[name] = tree.extractfile(member).read().decode("utf-8")
    return commit, sources


def audit(sources: dict[str, str], roots: list[str]) -> dict:
    """Report source and public-edge closures separately, sharing the lint parser."""
    entries = {name: module_imports(text, name) for name, text in sources.items()}
    source_graph = {
        name: {entry.name for entry in imports if entry.name in sources}
        for name, imports in entries.items()
    }
    public_graph = {
        name: {entry.name for entry in imports if entry.public and entry.name in sources}
        for name, imports in entries.items()
    }
    reverse = {name: set() for name in sources}
    for importer, imports in source_graph.items():
        for imported in imports:
            reverse[imported].add(importer)
    reports = {}
    for name in roots:
        if name not in sources:
            raise ValueError(f"No project module {name!r} in this Git tree")
        closures = {
            "source_closure": sorted(reachable_modules(source_graph, [name])),
            "public_import_closure": sorted(reachable_modules(public_graph, [name])),
            "reverse_source_closure": sorted(reachable_modules(reverse, [name])),
        }
        reports[name] = {
            **{key + "_count": len(value) for key, value in closures.items()},
            **closures,
            "model_to_class_edges": sorted(
                [importer, imported]
                for importer in closures["source_closure"]
                if importer.startswith("Complexitylib.Models.")
                for imported in source_graph[importer]
                if imported.startswith("Complexitylib.Classes.")
            ),
        }
    return reports


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ref", default="HEAD", help="Git commit/ref to resolve once")
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    commit, sources = git_sources(ROOT, args.ref)
    print(json.dumps({
        "commit": commit,
        "scope": "Project modules only; closures include their root",
        "public_imports": "Syntactic public edges, not elaborator or declaration counts",
        "reverse_imports": "Potential fan-out, not measured recompilation",
        "modules": audit(sources, args.modules),
    }, indent=2))


if __name__ == "__main__":
    main()

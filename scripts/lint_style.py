#!/usr/bin/env python3
"""Style linter for Complexitylib.

Checks every `.lean` file under `Complexitylib/` (and the root
`Complexitylib.lean`) for:

  copyright   — a Mathlib-style copyright header at the top of the file (the
                imported `Complexitylib/Algebraic/` keeps its MIT header)
  moduleDoc   — a module docstring (`/-! ... -/`)
  lineLength  — no line longer than 100 characters (lines containing URLs exempt)
  trailingWs  — no trailing whitespace
  finalNl     — file ends with exactly one newline
  rootEscape  — no `_root_.` escapes; they signal a nested namespace shadowing
                a root namespace (e.g. `SAT.TM` vs `TM`) or a declaration made
                outside its home namespace — fix the structure instead
  rootImport  — every non-Internal, non-Validation module is reachable from
                the public `Complexitylib` root import
  buildImport — every module is reachable from the root or a required
                validation-only build graph

and every `.lean` file of the repository outside hidden directories such as
`.lake/` (so also `scripts/*.lean`) for:

  nativeDecide — no `native_decide`, `decide +native`, `native := true`,
                 `bv_decide`, `bv_check`, or direct
                 `ofReduceBool`/`ofReduceNat` in code (comments and
                 string literals are ignored). The only exemption is a file
                 named `Validation.lean` outside the public `Complexitylib`
                 import graph: the executable validation modules use
                 `native_decide` in `example`s as regression tests, which add
                 no declaration, so `scripts/AxiomGuard.lean` cannot see them
                 and nothing can depend on them.

This is a hard gate: any violation fails the run. The quality refactor cleared
every grandfathered violation, so there is no baseline to maintain. The one
scoped exemption is the imported algebraic-circuits library under
`Complexitylib/Algebraic/` (see `IMPORTED_EXEMPTIONS`).

Usage:
  python3 scripts/lint_style.py
"""

import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBRARY = ROOT / "Complexitylib"
MAX_LINE = 100

COPYRIGHT_RE = re.compile(
    r"\A/-\n"
    r"Copyright \(c\) \d{4} .*\. All rights reserved\.\n"
    r"Released under Apache 2\.0 license as described in the file LICENSE\.\n"
    r"Authors: .*\n"
    r"-/\n"
)
# The imported algebraic-circuits library keeps its original MIT license.
IMPORTED_COPYRIGHT_RE = re.compile(
    r"\A/-\n"
    r"Copyright \(c\) \d{4} .*\. All rights reserved\.\n"
    r"Released under MIT license as described in the file "
    r"Complexitylib/Algebraic/LICENSE\.\n"
    r"Authors: .*\n"
    r"-/\n"
)
MODULE_DOC_RE = re.compile(r"^/-!", re.MULTILINE)
URL_RE = re.compile(r"https?://")
# The repository uses unquoted ASCII module names. Detect every import first,
# then reject richer Lean identifiers rather than truncate or omit them.
MODULE_NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
NON_PUBLIC_COMPONENTS = {"Internal", "Validation"}
# Evaluation by the compiler instead of the kernel: `native_decide`, its
# `decide +native` and `native := true` spellings, `bv_decide` and `bv_check`
# (which evaluate their reflected SAT certificate check the same way), and
# `ofReduceBool`/`ofReduceNat`, the axioms earlier Lean versions used for them.
NATIVE_RE = re.compile(
    r"\bnative_decide\b|\+native\b|\bnative\s*:=\s*true\b"
    r"|\bbv_decide\b|\bbv_check\b"
    r"|\bofReduceBool\b|\bofReduceNat\b"
)
# Every `NATIVE_RE` match contains one of these, so files without any of them
# need not be lexed.
NATIVE_MARKERS = ("native", "bv_decide", "bv_check", "ofReduceBool", "ofReduceNat")
# A character literal such as `'a'`, `'\n'` or `'\u{3b1}'`.
CHAR_LITERAL_RE = re.compile(r"'(?:\\[^'\n]+|[^'\\\n])'")
VALIDATION_FILE = "Validation.lean"
# The algebraic-circuits library, imported wholesale, keeps its upstream style
# for two checks until the consolidation plan (ROADMAP.md, item 7) migrates it:
# it extends CSLib's circuit types through `_root_.Cslib.Circuits` declarations,
# and some of its lines, including module paths in its umbrella imports, exceed
# 100 characters.
IMPORTED_EXEMPTIONS = {
    Path("Complexitylib") / "Algebraic": {"lineLength", "rootEscape"},
    Path("Complexitylib") / "Algebraic.lean": {"lineLength"},
}
IMPORTED_PREFIXES = tuple(IMPORTED_EXEMPTIONS)
BUILD_ROOTS = (
    "Complexitylib",
    "Complexitylib.Classes.P.Cobham.Validation",
    "Complexitylib.Models.TuringMachine.SingleTape.Validation",
    "Complexitylib.Models.TuringMachine.Repetition.Validation",
    "Complexitylib.Circuits.Encoding.Validation",
    "Complexitylib.SAT.Tseitin.Machine.Validation",
)


def check_file(path: Path) -> set[str]:
    """Return the set of check names that `path` violates."""
    text = path.read_text(encoding="utf-8")
    violations = set()
    imported = path.relative_to(ROOT).is_relative_to(IMPORTED_PREFIXES[0]) or (
        path.relative_to(ROOT) == IMPORTED_PREFIXES[1])
    copyright_re = IMPORTED_COPYRIGHT_RE if imported else COPYRIGHT_RE
    if not copyright_re.match(text):
        violations.add("copyright")
    if not MODULE_DOC_RE.search(text):
        violations.add("moduleDoc")
    lines = text.split("\n")
    if any(len(line) > MAX_LINE and not URL_RE.search(line) for line in lines):
        violations.add("lineLength")
    if any(line != line.rstrip() for line in lines):
        violations.add("trailingWs")
    if not text.endswith("\n") or text.endswith("\n\n"):
        violations.add("finalNl")
    if "_root_." in text:
        violations.add("rootEscape")
    return violations


def lean_code(text: str, *, stop_at_module_doc: bool = False) -> str:
    """Return `text` with comments and string literals blanked out.

    Handles nested block comments (`/- ... -/`, including doc comments), line
    comments (`--`), string literals with escapes, and character literals.
    Newlines are kept so that the result has the same lines as `text`.
    Import readers can stop at the first module doc command, after the header.
    """
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif stop_at_module_doc and text.startswith("/-!", i):
            break
        elif text.startswith("/-", i):
            out.append(" ")
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            out.append(" ")
            end = text.find("\n", i)
            i = n if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\n":
                    out.append("\n")
                i += 2 if text[i] == "\\" else 1
            i += 1
            out.append('""')
        elif text[i] == "'" and (i == 0 or not (
                text[i - 1].isalnum() or text[i - 1] in "_'!?." or ord(text[i - 1]) > 127)):
            match = CHAR_LITERAL_RE.match(text, i)
            if match:
                out.append("' '")
                i = match.end()
            else:
                out.append(text[i])
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def uses_native_evaluation(path: Path) -> bool:
    """Whether the code of `path` (outside comments and strings) evaluates natively."""
    text = path.read_text(encoding="utf-8")
    # Blanking comments and literals cannot introduce any of these spellings.
    # Most files contain none, so avoid scanning their entire bodies in Python.
    # Keep the full lexer/regex check for candidates, including commented tokens.
    if not any(token in text for token in NATIVE_MARKERS):
        return False
    return NATIVE_RE.search(lean_code(text)) is not None


def repository_lean_files() -> list[Path]:
    """Return every `.lean` file of the repository outside hidden directories."""
    found = []
    for directory, subdirectories, files in os.walk(ROOT):
        subdirectories[:] = sorted(d for d in subdirectories if not d.startswith("."))
        found.extend(Path(directory) / name for name in files if name.endswith(".lean"))
    return sorted(found)


def module_name(path: Path) -> str:
    """Return the Lean module name corresponding to `path`."""
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


@dataclass(frozen=True)
class ModuleImport:
    """One source import, including its module-system visibility and staging."""

    name: str
    public: bool
    meta: bool
    import_all: bool


def module_imports(text: str, source: str = "<source>") -> list[ModuleImport]:
    """Read source imports once for lint, caches, and dependency-boundary audits.

    Lean also permits Unicode, quoted, and apostrophe-containing identifiers.
    Those need an extended reader before use here: silently truncating or
    omitting them would make both import-graph checks and cache keys unsound.
    Ordinary imports are public in legacy files, private in `module` files.
    """
    # Header commands are whitespace-delimited, not line-delimited: Lean accepts
    # `module prelude import A public import B` on a single line.
    tokens = iter(lean_code(text, stop_at_module_doc=True).split())
    token = next(tokens, None)
    modular = token == "module"
    if modular:
        token = next(tokens, None)
    if token == "prelude":
        token = next(tokens, None)
    imports = []
    while token is not None:
        visibility = token if token in {"public", "private"} else None
        if visibility:
            token = next(tokens, None)
        meta = token == "meta"
        if meta:
            token = next(tokens, None)
        if token != "import":
            break  # The header ends at the first body command (e.g. public section).
        token = next(tokens, None)
        import_all = token == "all"
        name = next(tokens, None) if import_all else token
        if name is None or not MODULE_NAME_RE.fullmatch(name):
            raise ValueError(f"{source}: unsupported module import token {name!r}")
        imports.append(ModuleImport(
            name, visibility == "public" or (visibility is None and not modular),
            meta, import_all,
        ))
        token = next(tokens, None)
    return imports


def imported_modules(path: Path) -> set[str]:
    """Return complete ASCII module names; reject unsupported import tokens."""
    return {entry.name for entry in module_imports(path.read_text(encoding="utf-8"), str(path))}


def import_graph(paths: list[Path]) -> tuple[dict[str, Path], dict[str, set[str]]]:
    """Return local module paths and their local imports."""
    modules = {module_name(path): path for path in paths}
    imports = {
        name: imported_modules(path) & modules.keys()
        for name, path in modules.items()
    }
    return modules, imports


def reachable_modules(imports: dict[str, set[str]], roots: list[str]) -> set[str]:
    """Return modules reachable from `roots` in an import graph."""
    reachable = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        reachable.add(name)
        pending.extend(imports.get(name, set()))
    return reachable


def public_modules(paths: list[Path]) -> set[str]:
    """Return the modules reachable from the public `Complexitylib` root import."""
    _, imports = import_graph(paths)
    return reachable_modules(imports, ["Complexitylib"])


def check_native_evaluation(paths: list[Path]) -> set[str]:
    """Return files that evaluate natively outside the executable validation modules."""
    public = public_modules(paths)
    violations = set()
    for path in repository_lean_files():
        rel = path.relative_to(ROOT)
        validation = (path.name == VALIDATION_FILE and rel.parts[0] == "Complexitylib"
                      and module_name(path) not in public)
        if not validation and uses_native_evaluation(path):
            violations.add(f"{rel} : nativeDecide")
    return violations


def check_import_graph(paths: list[Path]) -> set[str]:
    """Return modules missing from the public or required build graphs."""
    modules, imports = import_graph(paths)
    root_reachable = reachable_modules(imports, ["Complexitylib"])
    build_reachable = reachable_modules(imports, list(BUILD_ROOTS))

    violations = set()
    for name, path in modules.items():
        components = set(path.relative_to(ROOT).with_suffix("").parts)
        if name not in root_reachable and components.isdisjoint(NON_PUBLIC_COMPONENTS):
            violations.add(f"{path.relative_to(ROOT)} : rootImport")
        if name not in build_reachable:
            violations.add(f"{path.relative_to(ROOT)} : buildImport")
    return violations


def collect() -> set[str]:
    """Return all current violations as `path : check` strings."""
    paths = sorted(LIBRARY.rglob("*.lean")) + [ROOT / "Complexitylib.lean"]
    found = set()
    for path in paths:
        rel = path.relative_to(ROOT)
        exempt = set().union(*(
            checks for prefix, checks in IMPORTED_EXEMPTIONS.items()
            if rel.is_relative_to(prefix)
        ))
        for check in check_file(path) - exempt:
            found.add(f"{rel} : {check}")
    found.update(check_import_graph(paths))
    found.update(check_native_evaluation(paths))
    return found


def main() -> int:
    found = sorted(collect())
    for entry in found:
        print(f"style lint: {entry}")
    if found:
        print(f"style lint: FAILED ({len(found)} violation(s))")
        return 1
    print("style lint: OK (no violations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

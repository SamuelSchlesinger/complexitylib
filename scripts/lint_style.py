#!/usr/bin/env python3
"""Style linter for Complexitylib.

Checks every `.lean` file under `Complexitylib/` for:

  copyright   — a Mathlib-style copyright header at the top of the file
  moduleDoc   — a module docstring (`/-! ... -/`)
  lineLength  — no line longer than 100 characters (URL lines and `import`
                lines exempt; module paths cannot be wrapped)
  trailingWs  — no trailing whitespace
  finalNl     — file ends with exactly one newline
  rootEscape  — no `_root_.` escapes; they signal a nested namespace shadowing
                a root namespace (e.g. `SAT.TM` vs `TM`) or a declaration made
                outside its home namespace — fix the structure instead

This is a hard gate: any violation fails the run. The quality refactor cleared
every grandfathered violation, so there is no baseline to maintain.

Usage:
  python3 scripts/lint_style.py
"""

import re
import sys
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
MODULE_DOC_RE = re.compile(r"^/-!", re.MULTILINE)
URL_RE = re.compile(r"https?://")
IMPORT_RE = re.compile(r"^(public )?(meta )?import ")


def check_file(path: Path) -> set[str]:
    """Return the set of check names that `path` violates."""
    text = path.read_text(encoding="utf-8")
    violations = set()
    if not COPYRIGHT_RE.match(text):
        violations.add("copyright")
    if not MODULE_DOC_RE.search(text):
        violations.add("moduleDoc")
    lines = text.split("\n")
    if any(
        len(line) > MAX_LINE and not URL_RE.search(line) and not IMPORT_RE.match(line)
        for line in lines
    ):
        violations.add("lineLength")
    if any(line != line.rstrip() for line in lines):
        violations.add("trailingWs")
    if not text.endswith("\n") or text.endswith("\n\n"):
        violations.add("finalNl")
    if "_root_." in text:
        violations.add("rootEscape")
    return violations


def collect() -> set[str]:
    """Return all current violations as `path : check` strings."""
    found = set()
    for path in sorted(LIBRARY.rglob("*.lean")) + [ROOT / "Complexitylib.lean"]:
        rel = path.relative_to(ROOT)
        for check in check_file(path):
            found.add(f"{rel} : {check}")
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

#!/usr/bin/env python3
"""Validates: every corpus artifact reruns and reproduces its saved evidence.

This is not an asymptotic MCSP lower-bound verifier. The Lean research theorem
is checked separately from finite identities and the production inventory.
"""

from pathlib import Path
import subprocess
import sys


CORPUS = Path(__file__).resolve().parents[1]
REPO = CORPUS.parents[1]


def run(arguments):
    result = subprocess.run(arguments, cwd=REPO, capture_output=True, text=True)
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise SystemExit(result.returncode)
    return result.stdout


def main():
    for script, expected in (
        ("data/check_deductions.py", "data/deductions.txt"),
        ("directions/data/check_routes.py", "directions/data/check_routes.json"),
        ("literature/data/check_scales.py", "literature/data/check_scales.txt"),
    ):
        output = run([sys.executable, "-B", str(CORPUS / script)])
        if output != (CORPUS / expected).read_text():
            raise SystemExit(f"Saved evidence differs: {expected}")
        print(f"PASS: {script} reproduces {expected}")
    expected_inventory = (CORPUS / "formal-toolkit/data/check-output.txt").read_text()
    print(run([sys.executable, "-B", str(CORPUS / "formal-toolkit/data/check_inventory.py")]),
          end="")
    if expected_inventory != (CORPUS / "formal-toolkit/data/check-output.txt").read_text():
        raise SystemExit("Inventory compiler output changed")
    output = run(["lake", "env", "lean", str(CORPUS / "data/RepeatedAnchor.lean")])
    expected = (
        "'Complexity.MCSP.Exploration.cost_le_iff_eq_repeatTarget' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]\n"
    )
    if output != expected:
        raise SystemExit(f"Unexpected research theorem compiler/axiom output:\n{output}")
    print("PASS: repeated-anchor theorem compiles with standard axioms only")
    print(run([sys.executable, "-B", str(CORPUS / "data/check_corpus.py")]), end="")
    print("PASS: all research artifacts reproduced")


if __name__ == "__main__":
    main()

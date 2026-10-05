#!/usr/bin/env python3
"""Validates: all saved finite artifacts reproduce, and corpus links/citations resolve.

Requires Python 3 and NumPy (only the nonlinear-layouts checker uses NumPy).
Does not validate any asymptotic research claim or replay the separate Lean baseline gates.
Run from any directory: python3 /path/to/circuit-lower-bound-frontiers/data/audit.py
"""

from pathlib import Path
import difflib
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    ("data/transfer_coefficients.py", "data/transfer_coefficients.txt"),
    ("nonlinear-layouts/data/check_median.py", "nonlinear-layouts/data/checked-output.json"),
    ("semantic-interfaces/data/validate.py", "semantic-interfaces/data/output.txt"),
    ("branch-decompositions/data/validate.py", "branch-decompositions/data/validation.json"),
    ("multicut-composition/data/multicut_checks.py", "multicut-composition/data/multicut_checks.txt"),
    ("algorithms/data/check_accounting.py", "algorithms/data/check_accounting.txt"),
    ("larger-gates/data/check_backdoors.py", "larger-gates/data/check_backdoors.txt"),
    ("larger-gates/data/check_frontier_independent.py", "larger-gates/data/check_frontier_independent.txt"),
    ("larger-gates/superlinear_checks.py", "larger-gates/data/superlinear_checks.txt"),
    ("communication-lifting/data/check_transfers.py", "communication-lifting/data/check_transfers.txt"),
    ("hard-functions/data/check_robustness.py", "hard-functions/data/check_robustness.txt"),
    ("graph-perspective/data/check_obstructions.py", "graph-perspective/data/checked-output.json"),
    ("barriers-perspective/data/check_obstructions.py", "barriers-perspective/data/check_obstructions.txt"),
]


def main():
    for script, expected in CASES:
        result = subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT,
                                capture_output=True, text=True)
        if result.returncode:
            sys.stderr.write(result.stdout + result.stderr)
            raise SystemExit(f"FAIL: {script}")
        saved = (ROOT / expected).read_text()
        if saved != result.stdout:
            sys.stderr.writelines(difflib.unified_diff(
                saved.splitlines(keepends=True), result.stdout.splitlines(keepends=True),
                fromfile=expected, tofile="recomputed"))
            raise SystemExit(f"FAIL: output drift in {script}")
        print(f"PASS: {script}")
    subprocess.run([sys.executable, str(ROOT / "data/check_corpus.py")], cwd=ROOT, check=True)
    print(f"PASS: {len(CASES)} finite artifacts reproduced exactly")


if __name__ == "__main__":
    main()

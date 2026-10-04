#!/usr/bin/env python3
"""Validates: finite branching-mass, parity, selector, and adaptive-cost calculations.

This is arithmetic and small exhaustive semantics, not a universal circuit theorem.
Run: python3 research/circuit-lower-bound-frontiers/algorithms/data/check_accounting.py
"""

from fractions import Fraction
from math import acos, pi, sqrt
from random import Random
import json


def tree_check(rng, budget, depth):
    """Integer weights stand for 2^mu; every child's total is at most its parent."""
    if depth == 0 or budget < 2 or rng.randrange(5) == 0:
        return budget, 0, 1
    left = rng.randrange(1, budget)
    right = rng.randrange(1, budget - left + 1)
    lc, ld, ln = tree_check(rng, left, depth - 1)
    rc, rd, rn = tree_check(rng, right, depth - 1)
    cost = budget + lc + rc
    actual_depth = 1 + max(ld, rd)
    assert cost <= (actual_depth + 1) * budget
    return cost, actual_depth, 1 + ln + rn


def main():
    coefficient = (3 / pi) * acos((1 + 2 * sqrt(2)) / 4)
    threshold = 1 + 1 / coefficient
    profiles = []
    for deletions in [(4, 4), (5, 5), (1, 9), (2, 8)]:
        mass = sum(2 ** (-coefficient * (d - 1)) for d in deletions)
        profiles.append({"gate_deletions": deletions, "mean": sum(deletions) / 2,
                         "mass_ratio": round(mass, 12), "contracts": mass <= 1})
    assert profiles[0]["mass_ratio"] > 1
    assert profiles[1]["mass_ratio"] < 1
    assert profiles[2]["mean"] > threshold and profiles[2]["mass_ratio"] > 1

    parity_checks = []
    for n in range(3, 13):
        counts = [0, 0]
        for x in range(1 << n):
            counts[x & 1] += x.bit_count() % 2
        assert counts == [1 << (n - 2), 1 << (n - 2)]
        # Parity and its complement each have n-2 binary gates after one fixing.
        parent_excess = (n - 1) - n + 1
        child_excess = (n - 2) - (n - 1) + 1
        assert parent_excess == child_excess == 0
        parity_checks.append({"inputs": n, "satisfying_by_first_bit": counts,
                              "surplus_mass_ratio": 2})

    # For C=x AND B(y), B has k essential inputs and t gates; t>=k-1.
    # Branch 0 is constant; branch 1 has exactly the parent's nonnegative surplus.
    selector_checks = []
    for k, t in [(4, 3), (4, 20), (10, 100)]:
        parent = max((t + 1) - (k + 1) + 1, 0)
        zero_child = 0
        one_child = max(t - k + 1, 0)
        mass = 2 ** (coefficient * (zero_child - parent)) + 1
        assert parent == one_child and mass > 1
        selector_checks.append({"B_inputs": k, "B_gates": t,
                                "mean_deleted_gates": (t + 2) / 2,
                                "mass_ratio": round(mass, 12)})

    # Prefix code {0,10,11}: leaf cylinders partition eight-bit input space.
    n = 8
    fixed = [1, 2, 2]
    remaining = [n - b for b in fixed]
    seeds = [2, 3, 4]
    probabilities = [Fraction(1, 2 ** b) for b in fixed]
    assert sum(probabilities) == 1
    direct_cost = sum(2 ** r for r in seeds)
    weighted_cost = 2 ** n * sum(
        p * Fraction(2 ** r, 2 ** m)
        for p, r, m in zip(probabilities, seeds, remaining)
    )
    assert direct_cost == weighted_cost == 28
    errors = [Fraction(1, 12), Fraction(1, 24), Fraction(1, 6)]
    error_bound = sum(p * err for p, err in zip(probabilities, errors))
    assert error_bound == Fraction(3, 32)

    # The read-input correction: min(m,A(s-m)) never exceeds A*s/(1+A).
    hybrid_checks = 0
    for n in range(2, 101):
        for s in range(n, 5 * n):
            for m in range(n + 1):
                exponent = min(m, coefficient * (s - m))
                assert exponent <= coefficient * s / (1 + coefficient) + 1e-12
                hybrid_checks += 1

    rng = Random(20261004)
    tree_nodes = 0
    for _ in range(1000):
        root = rng.randrange(2, 4097)
        cost, depth, nodes = tree_check(rng, root, 8)
        assert cost <= (depth + 1) * root
        tree_nodes += nodes

    print("Validates: finite branching mass and weighted whole-tree accounting; no coverage theorem.")
    print(json.dumps({"seed": 20261004, "A_gaussian": round(coefficient, 12),
                      "symmetric_gate_deletion_threshold": round(threshold, 12),
                      "abstract_branch_profiles": profiles, "parity": parity_checks,
                      "selector_accounting": selector_checks,
                      "weighted_CAPP": {"direct_seed_evaluations": direct_cost,
                                        "weighted_seed_evaluations": str(weighted_cost),
                                        "weighted_error_bound": str(error_bound)},
                      "hybrid_exponent_checks": hybrid_checks,
                      "random_budget_trees": 1000, "total_tree_nodes": tree_nodes}, indent=2))


if __name__ == "__main__":
    main()

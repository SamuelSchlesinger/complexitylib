#!/usr/bin/env python3
"""Validates: exact median frontier containment and finite relaxation obstructions.

The truth table is exhaustive, not random. The continuous regression uses seed
20261004. It does not validate a Gaussian strict-gain bound or pathwidth constant.
Run: python3 research/circuit-lower-bound-frontiers/nonlinear-layouts/data/check_median.py
Dependencies: Python 3 and NumPy.
"""

from itertools import product
import json
import math

import numpy as np


def binary_update(bits):
    root = sum(bits[:3])
    return tuple(int(root + sum(bits[3 + 2 * i:5 + 2 * i]) >= 3)
                 for i in range(3))


def mixed(values):
    return min(values) != max(values)


counts = {"assignments": 0, "old_mixed": 0, "new_mixed": 0,
          "repaired": 0, "created": 0}
for bits in product((0, 1), repeat=9):
    old, new = mixed(bits[:3]), mixed(binary_update(bits))
    counts["assignments"] += 1
    counts["old_mixed"] += int(old)
    counts["new_mixed"] += int(new)
    counts["repaired"] += int(old and not new)
    counts["created"] += int(new and not old)
assert counts["created"] == 0

rng = np.random.default_rng(20261004)
samples = rng.normal(size=(100000, 9))
new = np.stack([np.median(np.concatenate(
    (samples[:, :3], samples[:, 3 + 2 * i:5 + 2 * i]), axis=1), axis=1)
    for i in range(3)], axis=1)
assert np.all(new.min(axis=1) >= samples[:, :3].min(axis=1))
assert np.all(new.max(axis=1) <= samples[:, :3].max(axis=1))

# K_{3,3}: all left vectors x0, right vectors rho*x0 + z_i/3.
# The three z_i are unit vectors at 120 degrees in the perpendicular plane.
rho = 2 * math.sqrt(2) / 3
x0 = np.array([1.0, 0.0, 0.0])
right = np.array([[rho, math.cos(2 * math.pi * i / 3) / 3,
                   math.sin(2 * math.pi * i / 3) / 3] for i in range(3)])
edge = right + x0
edge /= np.linalg.norm(edge, axis=1)[:, None]
star_corr = (1 + 2 * math.sqrt(2)) / 4
assert np.allclose(np.diag(right @ right.T), 1)
assert np.allclose(right @ x0, rho)
assert np.allclose((edge @ edge.T)[np.triu_indices(3, 1)], star_corr)
scores = rng.normal(size=(100000, 3)) @ edge.T
# Every line-graph neighborhood contains three copies of its own edge key.
for i in range(3):
    five = np.column_stack((scores, scores[:, i], scores[:, i]))
    assert np.array_equal(np.median(five, axis=1), scores[:, i])

# Unlike a median, a middle-three trimmed mean can create a mixed star.
trim_root = [-1, -1, -1]
trim_external = [[10, 10], [-10, -10], [-10, -10]]
trimmed = [sum(sorted(trim_root + ext)[1:4]) / 3 for ext in trim_external]
assert max(trim_root) < 0 and min(trimmed) < 0 < max(trimmed)

p = 3 * math.acos(star_corr) / (2 * math.pi)
print(json.dumps({
    "Validates": "finite exact median truth table; relaxation and trimmed-mean obstructions",
    "seed": 20261004,
    "binary_truth_table": counts,
    "continuous_interval_trials": 100000,
    "k33_relaxation": {
        "rho": rho, "star_correlation": star_corr,
        "left_vertex_frontier_probability": p,
        "graph_average_frontier_probability": p / 2,
        "median_update": "identically the identity; exact three-copy reason",
        "actual_distance_kernel": False},
    "trimmed_mean_counterexample": {
        "root": trim_root, "external_pairs": trim_external,
        "updated": trimmed, "threshold": 0},
    "conditional_targets": [{"delta": delta, "pathwidth_coefficient": p - delta,
                             "circuit_coefficient": 1 + 1 / (2 * (p - delta))}
                            for delta in [0, 0.001, 0.005]],
    "tiny_band_dependency_degrees": {str(r): 8 * 4 ** r - 3 for r in range(5)}
}, indent=2))

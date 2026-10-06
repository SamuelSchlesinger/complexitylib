#!/usr/bin/env python3
"""Validates: finite repeated-anchor slices, sparse NO cubes, singleton capacity,
and exact multiplicity cancellation in the displayed equality circuit.

These exhaustive small cases test the stated identities and counterexamples;
they do not prove general MCSP lower bounds or replace the paper arguments.
Only Python's standard library is needed. Run with python3 -B check_routes.py.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json


def cost_at_most_one(n):
    """Enumerate De Morgan functions with at most one charged AND/OR gate.

    NOT, identity, and constants are free, so all remaining wires are signed
    inputs or the signed output of the sole charged gate.
    """
    length = 1 << n
    mask = (1 << length) - 1
    zero_cost = {0, mask}
    for j in range(n):
        value = sum(((i >> (n - 1 - j)) & 1) << i for i in range(length))
        zero_cost.update((value, value ^ mask))
    one_cost = set(zero_cost)
    for a, b in product(zero_cost, repeat=2):
        for value in (a & b, a | b):
            one_cost.update((value, value ^ mask))
    return zero_cost, one_cost


def repeated_anchors():
    base_n = 2
    base_len = 1 << base_n
    zero, one = cost_at_most_one(base_n)
    anchors = sorted(one - zero)
    checked = 0
    summary = []
    for selectors in (1, 2):
        blocks = 1 << selectors
        length = blocks * base_len
        _, accepted = cost_at_most_one(base_n + selectors)
        for anchor in anchors:
            repeated = sum(anchor << (base_len * block) for block in range(blocks))
            assert repeated in accepted
            for block in range(blocks):
                fixed_start = block * base_len
                free = [i for i in range(length)
                        if not fixed_start <= i < fixed_start + base_len]
                for filling in range(1 << len(free)):
                    table = anchor << fixed_start
                    for j, position in enumerate(free):
                        table |= ((filling >> j) & 1) << position
                    assert (table in accepted) == (table == repeated)
                    checked += 1
        # Khrapchenko witness using all repeated exact-cost-one anchors.
        diagonals = {sum(a << (base_len * b) for b in range(blocks)) for a in anchors}
        neighbors = Counter(a ^ (1 << i) for a in diagonals for i in range(length))
        assert all(b not in accepted for b in neighbors)
        edges = length * len(diagonals)
        measure = Fraction(edges * edges, len(diagonals) * len(neighbors))
        if blocks == 2:
            assert max(neighbors.values()) <= 2 and length <= measure <= 2 * length
        else:
            assert max(neighbors.values()) == 1 and measure == length
        summary.append({"arity": base_n + selectors, "blocks": blocks,
                        "N": length, "anchors": len(anchors),
                        "khrapchenko_witness_measure": str(measure)})
    # Positive cost is indispensable: the selector itself has zero binary cost.
    zero2, _ = cost_at_most_one(2)
    selector = 0b1100  # first selector bit, under the leading-bit block order
    assert selector in zero2 and selector & 0b11 == 0 and selector != 0
    return {"cofactor_assignments": checked, "cases": summary,
            "zero_cost_counterexample": "selector, with zero anchor on its false cofactor"}


def sparse_no_cubes():
    dimension = 6
    checked = 0
    cube_points = 0
    for cardinality in (1, 2):
        fixed_count = cardinality.bit_length()  # floor(log2 |YES|) + 1
        fixed_mask = (1 << fixed_count) - 1
        for yes_tuple in combinations(range(1 << dimension), cardinality):
            yes = set(yes_tuple)
            observed = {x & fixed_mask for x in yes}
            absent = next(a for a in range(1 << fixed_count) if a not in observed)
            cube = {absent | (tail << fixed_count)
                    for tail in range(1 << (dimension - fixed_count))}
            assert not cube & yes
            assert len(cube) == 1 << (dimension - fixed_count)
            checked += 1
            cube_points += len(cube)
    return {"outer_dimension": dimension, "sparse_sets": checked,
            "NO_cube_points_checked": cube_points}


def singleton_capacity():
    checked = 0
    max_singletons = 0
    for mapping in product(range(4), repeat=8):
        labels = Counter(mapping)
        singletons = sum(value == 1 for value in labels.values())
        assert singletons <= 3
        max_singletons = max(max_singletons, singletons)
        checked += 1
    assert max_singletons == 3
    singleton_sets = []
    for mapping in product(range(2), repeat=4):
        counts = Counter(mapping)
        singleton_sets.append({i for i, label in enumerate(mapping) if counts[label] == 1})
    for contexts in product(singleton_sets, repeat=2):
        assert len(contexts[0] | contexts[1]) <= 2 * (2 - 1)
    return {"maps_8_to_4": checked, "max_singleton_fibers": max_singletons,
            "pairs_of_context_maps_4_to_2": len(singleton_sets) ** 2}


def nested_equality():
    rows = []
    for levels in range(1, 9):
        m = 1 << levels
        loads = [Fraction(0)] * m
        demand = Fraction(0)
        for j in range(1, levels + 1):
            size = 1 << j
            weight = Fraction(1, j)  # deterministic nonuniform scale weights
            for first in range(0, m, size):
                demand += weight * size
                for a in range(first, first + size):
                    loads[a] += weight
        assert demand == sum(loads)
        assert demand / max(loads) == m
        unit_demand = m * levels
        unit_load = levels
        internal_demand = 2 * m * levels - m + 1
        assert Fraction(internal_demand, levels) <= 2 * m - 1
        rows.append({"m": m, "gates": 3 * m - 1,
                     "unit_demand": unit_demand, "unit_max_load": unit_load,
                     "weighted_ratio": str(demand / max(loads))})
    return rows


if __name__ == "__main__":
    result = {"repeated_anchors": repeated_anchors(), "sparse_NO_cubes": sparse_no_cubes(),
              "singleton_capacity": singleton_capacity(), "nested_equality": nested_equality()}
    print(json.dumps(result, indent=2, sort_keys=True))

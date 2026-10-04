#!/usr/bin/env python3
"""Validates: finite cycle-deletion identities, cubic orientation, and entropy examples.

Deterministic exhaustive checks, with no random seed or external dependencies.
These checks do not validate a universal circuit compiler or a new lower bound.
"""

from itertools import combinations, permutations
import json
from math import acos, e, log2, pi, sqrt


def components(n, edges, deleted=()):
    todo = set(range(n)) - set(deleted)
    adjacency = [set() for _ in range(n)]
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    count = 0
    while todo:
        count += 1
        stack = [todo.pop()]
        while stack:
            for other in adjacency[stack.pop()] & todo:
                todo.remove(other)
                stack.append(other)
    return count


def cubic_graphs(n):
    """Enumerate all labeled simple cubic graphs, filtering connectivity."""
    for edges in combinations(combinations(range(n), 2), 3 * n // 2):
        degrees = [0] * n
        for a, b in edges:
            degrees[a] += 1
            degrees[b] += 1
        if all(d == 3 for d in degrees) and components(n, edges) == 1:
            yield edges


def has_bipolar_order(n, edges):
    adjacency = [set() for _ in range(n)]
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    # Fix the source at zero and try each adjacent sink, as in st-numbering.
    for sink in sorted(adjacency[0]):
        middle = [v for v in range(n) if v not in (0, sink)]
        for order in permutations(middle):
            order = (0,) + order + (sink,)
            rank = {v: i for i, v in enumerate(order)}
            if all(any(rank[u] < rank[v] for u in adjacency[v])
                   and any(rank[u] > rank[v] for u in adjacency[v])
                   for v in middle):
                return True
    return False


def main():
    graphs = [(n, edges) for n in (4, 6) for edges in cubic_graphs(n)]
    atlas_counts = {str(n): sum(m == n for m, _ in graphs) for n in (4, 6)}
    assert atlas_counts == {"4": 1, "6": 70}
    cube = tuple((i, j) for i in range(8) for j in range(i + 1, 8)
                 if (i ^ j).bit_count() == 1)
    petersen = tuple(sorted({tuple(sorted(edge)) for i in range(5)
                            for edge in ((i, (i + 1) % 5),
                                         (i, i + 5),
                                         (i + 5, (i + 2) % 5 + 5))}))
    graphs += [(8, cube), (10, petersen)]
    vertex_checks = edge_checks = orientation_checks = 0
    strict_component_examples = 0
    max_vertex_drop = {}
    for n, edges in graphs:
        mu = len(edges) - n + 1
        assert all(components(n, edges, (v,)) == 1 for v in range(n))
        assert has_bipolar_order(n, edges)
        orientation_checks += 1
        for mask in range(1, (1 << n) - 1):
            chosen = {i for i in range(n) if mask >> i & 1}
            kept = tuple((a, b) for a, b in edges if a not in chosen and b not in chosen)
            internal = sum(a in chosen and b in chosen for a, b in edges)
            count = components(n, kept, chosen)
            after = len(kept) - (n - len(chosen)) + count
            drop = mu - after
            assert drop == 2 * len(chosen) - internal - count + 1
            assert drop <= 2 * len(chosen)
            max_vertex_drop[len(chosen)] = max(max_vertex_drop.get(len(chosen), 0), drop)
            strict_component_examples += count > 1
            vertex_checks += 1
        for mask in range(1 << len(edges)):
            kept = tuple(e for i, e in enumerate(edges) if not (mask >> i & 1))
            count = components(n, kept)
            after = len(kept) - n + count
            assert mu - after == mask.bit_count() - count + 1
            assert mu - after <= mask.bit_count()
            edge_checks += 1

    entropy = []
    for k in (2, 4, 16, 256, 65536):
        b = 2 * (k.bit_length() - 1)
        p = 2.0 ** (-b)
        h = k * (-p * log2(p) - (1 - p) * log2(1 - p))
        bound = (b + log2(e)) / k
        assert h <= bound + 1e-10
        entropy.append({"signals": k, "block_length": b,
                        "support_log2": k, "shannon_bits": round(h, 9),
                        "proved_upper_bound": round(bound, 9)})
    alpha0 = 3 / pi * acos((1 + 2 * sqrt(2)) / 4)
    parity_checks = 0
    for width in (2, 3, 4):
        n = 2 * width
        for mask in range(1 << n):
            first = (mask & ((1 << width) - 1)).bit_count() % 2
            second = (mask >> width).bit_count() % 2
            # Each block parity is exactly a width-CNF: one clause excludes
            # each block assignment having the wrong specified parity.
            def block_cnf(bits, desired):
                return all(bits != forbidden for forbidden in range(1 << width)
                           if forbidden.bit_count() % 2 != desired)
            covered = any(block_cnf(mask & ((1 << width) - 1), desired)
                          and block_cnf(mask >> width, 1 - desired)
                          for desired in (0, 1))
            assert covered == (first != second) == (mask.bit_count() % 2 == 1)
            parity_checks += 1
    report = {
        "Validates": "Finite cycle-deletion identities, cubic orientation, and entropy examples",
        "scope": "Finite obstructions only; no universal compiler established",
        "labeled_connected_cubic_graphs": atlas_counts,
        "extra_graphs": ["cube", "Petersen"],
        "bipolar_orientation_checks": orientation_checks,
        "vertex_deletion_identity_checks": vertex_checks,
        "edge_deletion_identity_checks": edge_checks,
        "vertex_deletions_with_multiple_components": strict_component_examples,
        "max_cycle_drop_by_deleted_vertices": max_vertex_drop,
        "entropy_examples": entropy,
        "block_parity_cnf_cover_truth_table_checks": parity_checks,
        "current_alpha": round(alpha0, 12),
        "target_alpha": 0.25,
        "balanced_separator_sufficient_bits_per_cycle": round(0.25 - alpha0 / 2, 12),
        "pure_vertex_branch_factor_lower_bound_alpha_quarter": round(sqrt(2), 12),
        "depth_reduction_coefficient_if_alpha_s_one_fifth_rho_one": 5,
        "depth_reduction_coefficient_if_alpha_offset_one_quarter_rho_one": 5,
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

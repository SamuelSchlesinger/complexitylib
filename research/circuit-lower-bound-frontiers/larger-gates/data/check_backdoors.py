#!/usr/bin/env python3
"""Validates: finite exact output guessing, component rectangle covers, and residual
wiring excess for mixed binary/sum gates; also tests threshold-state obstructions.

Standard library only. Fixed seed 20261004. No asymptotic or novelty certification.
"""

from collections import defaultdict
from itertools import product
from math import acos, pi, sqrt
import random


def bits(n):
    return product((0, 1), repeat=n)


def aggregate_result(gate, total):
    kind, _, parameter = gate
    if kind == "sym":
        return parameter[total]
    if kind == "mod":
        modulus, accepted = parameter
        return int(total % modulus in accepted)
    return int(total >= parameter)


def gate_value(gate, values):
    kind, incoming, parameter = gate
    if kind == "bin":
        return (parameter >> (2 * values[incoming[0]] + values[incoming[1]])) & 1
    total = sum(weight * values[wire] for wire, weight in incoming)
    return aggregate_result(gate, total)


def evaluate(n, gates, assignment, guessed=None):
    values = list(assignment)
    special_index = 0
    for gate in gates:
        if gate[0] != "bin" and guessed is not None:
            values.append(guessed[special_index])
            special_index += 1
        else:
            values.append(gate_value(gate, values))
    return values


def residual(n, gates):
    vertices = list(range(n)) + [n + j for j, g in enumerate(gates) if g[0] == "bin"]
    parent = {v: v for v in vertices}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    edges = []
    fixed_slots = 0
    for j, gate in enumerate(gates):
        if gate[0] != "bin":
            continue
        for wire in gate[1]:
            if wire in parent:
                edges.append((wire, n + j))
                parent[find(wire)] = find(n + j)
            else:
                fixed_slots += 1
    components = defaultdict(set)
    for v in vertices:
        components[find(v)].add(v)
    components = list(components.values())
    # Actual fanout splitting: f slots require f-1 copy vertices and f-1 extra edges.
    slots = defaultdict(list)
    for source, target in edges:
        slots[source].append(target)
    expanded_edges = []
    next_vertex = n + len(gates)
    expanded_vertices = set(vertices)
    for source, targets in slots.items():
        if len(targets) == 1:
            expanded_edges.append((source, targets[0]))
            continue
        copies = list(range(next_vertex, next_vertex + len(targets) - 1))
        next_vertex += len(copies)
        expanded_vertices.update(copies)
        expanded_edges.extend(zip([source] + copies[:-1], copies))
        for j, target in enumerate(targets):
            expanded_edges.append((copies[min(j, len(copies) - 1)], target))
    degree = defaultdict(int)
    for a, b in expanded_edges:
        assert a != b
        degree[a] += 1
        degree[b] += 1
    s = sum(g[0] == "bin" for g in gates)
    assert max(degree.values(), default=0) <= 3
    assert len(expanded_edges) - len(expanded_vertices) == s - n - fixed_slots
    assert len(expanded_vertices) <= n + 3 * s
    return components


def check_circuit(n, gates):
    special = [(n + j, g) for j, g in enumerate(gates) if g[0] != "bin"]
    special_set = {wire for wire, _ in special}
    assignments = list(bits(n))
    q = len(special)
    ranges = [g[2][0] if g[0] == "mod" else 1 + sum(abs(w) for _, w in g[1])
              for _, g in special]
    cover_bound = (2 ** q)
    for cardinality in ranges:
        cover_bound *= cardinality
    output_wire = n + len(gates) - 1
    oracle = {x: evaluate(n, gates, x)[output_wire] for x in assignments}
    # Validate guessing against a separate direct evaluator, including uniqueness.
    for x in assignments:
        consistent = []
        for a in bits(q):
            values = evaluate(n, gates, x, a)
            if all(values[w] == gate_value(g, values) for w, g in special):
                consistent.append(values[output_wire])
        assert consistent == [oracle[x]]
    components = residual(n, gates)
    covers = 0
    for selected in bits(len(components)):
        left_vertices = set().union(*(c for c, take in zip(components, selected) if take))
        left_inputs = [j for j in range(n) if j in left_vertices]
        right_inputs = [j for j in range(n) if j not in left_vertices]
        rectangles = {}
        accepted_pairs = set()
        for a in bits(q):
            groups = defaultdict(set)
            for lx in bits(len(left_inputs)):
                x = [0] * n
                for j, value in zip(left_inputs, lx):
                    x[j] = value
                values = evaluate(n, gates, x, a)
                if output_wire in left_vertices and not values[output_wire]:
                    continue
                left_sums = []
                for _, g in special:
                    total = sum(weight * values[wire] for wire, weight in g[1]
                                if wire in left_vertices)
                    left_sums.append(total % g[2][0] if g[0] == "mod" else total)
                left_sums = tuple(left_sums)
                groups[left_sums].add(lx)
            for left_sums, left_values in groups.items():
                right_values = set()
                for rx in bits(len(right_inputs)):
                    x = [0] * n
                    for j, value in zip(right_inputs, rx):
                        x[j] = value
                    values = evaluate(n, gates, x, a)
                    if output_wire not in left_vertices and not values[output_wire]:
                        continue
                    totals = [left_sums[j] + sum(weight * values[wire]
                              for wire, weight in g[1] if wire not in left_vertices)
                              for j, (_, g) in enumerate(special)]
                    checks = [aggregate_result(g, total) == a[j] for j, ((_, g), total)
                              in enumerate(zip(special, totals))]
                    if all(checks):
                        right_values.add(rx)
                if right_values:
                    rectangles[(a, left_sums)] = (left_values, right_values)
                    accepted_pairs.update(product(left_values, right_values))
        assert len(rectangles) <= cover_bound
        for x in assignments:
            pair = (tuple(x[j] for j in left_inputs), tuple(x[j] for j in right_inputs))
            assert (pair in accepted_pairs) == bool(oracle[x])
        # All rectangle cross-products really accept; sharing and special-to-special
        # wires are included in this same check, not assumed independent.
        for left_values, right_values in rectangles.values():
            for lx, rx in product(left_values, right_values):
                x = [0] * n
                for j, value in zip(left_inputs, lx):
                    x[j] = value
                for j, value in zip(right_inputs, rx):
                    x[j] = value
                assert oracle[tuple(x)]
        covers += 1
    assert special_set.isdisjoint(set().union(*components))
    return covers


def random_circuit(rng, n, number):
    gates = []
    q = 0
    for j in range(number):
        kind = rng.choice(["bin", "bin", "sym", "thr", "mod"]) if q < 3 else "bin"
        if kind == "bin":
            gates.append((kind, [rng.randrange(n + j) for _ in range(2)], rng.randrange(16)))
        else:
            q += 1
            incoming = [(rng.randrange(n + j), 1 if kind == "sym" else rng.randint(-4, 4))
                        for _ in range(rng.randint(1, 6))]
            if kind == "sym":
                parameter = [rng.randrange(2) for _ in range(len(incoming) + 1)]
            elif kind == "mod":
                modulus = rng.randint(2, 5)
                parameter = (modulus, tuple(j for j in range(modulus) if rng.randrange(2)))
            else:
                parameter = rng.randint(-5, 5)
            gates.append((kind, incoming, parameter))
    return gates


def compositions(n):
    if n == 0:
        yield ()
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            yield (first,) + rest


def check_giant_component():
    checked = 0
    for n in range(3, 15):
        for r in range(1, n // 3 + 1):
            for sizes in compositions(n):
                possible = {0}
                for size in sizes:
                    possible |= {t + size for t in possible}
                if all(min(t, n - t) < r for t in possible):
                    assert max(sizes) > n - r
                checked += 1
    return checked


def main():
    rng = random.Random(20261004)
    cases = [(4, [("sym", [(j, 1) for j in range(4)], [0, 1, 0, 1, 0])])]
    cases.append((5, [("mod", [(j, 1) for j in range(5)], (2, (1,)))]))
    # Multiplexing, repeated slots, a symmetric gate used by a threshold gate,
    # observed sinks, and an output at a deleted gate all occur explicitly.
    cases.append((3, [("bin", [0, 1], 8), ("bin", [0, 2], 4),
                      ("sym", [(3, 1), (4, 1), (0, 1)], [0, 1, 0, 1]),
                      ("thr", [(5, 3), (3, -2), (5, 1)], 2)]))
    for _ in range(120):
        n = rng.randint(2, 5)
        cases.append((n, random_circuit(rng, n, rng.randint(1, 7))))
    covers = sum(check_circuit(n, gates) for n, gates in cases)
    print("seed=20261004")
    print(f"mixed circuits checked={len(cases)}; component-union covers checked={covers}")
    print("exact guessed semantics, one-sided sum covers, degree<=3, excess=s-n-t: PASS")
    print(f"giant-component composition cases={check_giant_component()}: PASS")
    for m in range(1, 9):
        # One LTF on 2m bits with weights +/-2^i has distinct X>=Y rows.
        rows = {tuple(int(x >= y) for y in range(2 ** m)) for x in range(2 ** m)}
        assert len(rows) == 2 ** m
        print(f"comparison threshold: half_bits={m}, distinct residuals={len(rows)}")
    n = 8
    even = sum(sum(x) % 2 == 0 for x in bits(n // 2))
    print(f"one-gate parity n={n}: balanced one-rectangle sides={even}x{even}")
    A = 3 / pi * acos((1 + 2 * sqrt(2)) / 4)
    print(f"A={A:.9f}; target coefficient 1+1/A={1 + 1 / A:.9f}")
    print(f"leading D-loss coefficient 1+2/A={1 + 2 / A:.9f}")
    print("Limits: finite semantics/accounting checks only; no asymptotic proof or priority claim.")


if __name__ == "__main__":
    main()

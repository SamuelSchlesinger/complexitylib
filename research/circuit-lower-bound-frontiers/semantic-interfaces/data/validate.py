#!/usr/bin/env python3
"""Validates: finite smooth-compiler semantics and interface-compression obstructions.

Stdlib only. Exhaustive truth-table checks and fixed-seed small circuit tests;
these do not prove a universal semantic-width improvement.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, log2
from random import Random


def bit(table, a, b):
    return (table >> (2 * a + b)) & 1


def entropy(counts):
    total = sum(counts)
    return -sum((c / total) * log2(c / total) for c in counts if c)


def h2(p):
    return entropy([p, 1 - p])


def network(n, gates):
    """Degree-three wiring; input vertices remain even for unused inputs."""
    vertices = [("input", i) for i in range(n)]
    vertices += [("gate", j) for j in range(len(gates))]
    edges, incidence, ins, outs = [], {}, {}, {}
    uses = [[] for _ in range(n + len(gates))]
    for j, (_, a, b) in enumerate(gates):
        uses[a].append((n + j, 0))
        uses[b].append((n + j, 1))

    def edge(u, v, signal):
        e = len(edges)
        edges.append((u, v, signal))
        incidence.setdefault(u, []).append(e)
        incidence.setdefault(v, []).append(e)
        return e

    for signal, slots in enumerate(uses):
        if not slots:
            continue
        source = signal
        if len(slots) == 1:
            target, slot = slots[0]
            e = edge(source, target, signal)
            outs[source] = e
            ins[target, slot] = e
            continue
        copies = list(range(len(vertices), len(vertices) + len(slots) - 1))
        vertices.extend(("copy", None) for _ in copies)
        outs[source] = edge(source, copies[0], signal)
        for j, copy in enumerate(copies):
            target, slot = slots[j]
            ins[target, slot] = edge(copy, target, signal)
            if j + 1 < len(copies):
                edge(copy, copies[j + 1], signal)
            else:
                target, slot = slots[-1]
                ins[target, slot] = edge(copy, target, signal)

    def check(v, assignment, x):
        kind, i = vertices[v]
        if kind == "input":
            return v not in outs or assignment[outs[v]] == x[i]
        if kind == "copy":
            return len({assignment[e] for e in incidence[v]}) <= 1
        value = bit(gates[i][0], assignment[ins[v, 0]], assignment[ins[v, 1]])
        if i == len(gates) - 1:
            return value == 1
        return v not in outs or assignment[outs[v]] == value

    assert max(map(len, incidence.values()), default=0) <= 3
    return vertices, edges, incidence, check


def compiler_checks():
    rng = Random(20261004)
    circuits, runs, inputs_checked = 0, 0, 0
    for table in range(16):
        # Repeated slots and shared signals are deliberate.
        for shape in range(4):
            n = 3
            a, b = [(0, 1), (0, 0), (1, 2), (0, 2)][shape]
            gates = [(table, a, b), (rng.randrange(16), 3, shape % 3)]
            vertices, edges, incidence, check = network(n, gates)
            circuits += 1
            for _ in range(3):
                order = list(range(len(vertices)))
                rng.shuffle(order)
                pos = {v: i for i, v in enumerate(order)}
                cuts = [tuple(e for e, (u, v, _) in enumerate(edges)
                              if (pos[u] < i) != (pos[v] < i))
                        for i in range(len(vertices) + 1)]
                for restricted in (False, True):
                    allowed = []
                    for cut in cuts:
                        states = list(product((0, 1), repeat=len(cut)))
                        allowed.append({s for s in states
                                        if not restricted or not s or rng.randrange(4) != 0})
                    runs += 1
                    for x in product((0, 1), repeat=n):
                        values = list(x)
                        for t, a, b in gates:
                            values.append(bit(t, values[a], values[b]))
                        trace = [values[signal] for _, _, signal in edges]
                        expected = values[-1] == 1 and all(
                            tuple(trace[e] for e in cut) in permitted
                            for cut, permitted in zip(cuts, allowed))
                        paths = {(): 1}
                        for i, v in enumerate(order):
                            after = cuts[i + 1]
                            old = cuts[i]
                            new_edges = [e for e in incidence.get(v, []) if e not in old]
                            next_paths = Counter()
                            for state, multiplicity in paths.items():
                                for guessed in product((0, 1), repeat=len(new_edges)):
                                    assignment = dict(zip(old, state))
                                    assignment.update(zip(new_edges, guessed))
                                    target = tuple(assignment[e] for e in after)
                                    if target in allowed[i + 1] and check(v, assignment, x):
                                        next_paths[target] += multiplicity
                            paths = next_paths
                        assert paths.get((), 0) == int(expected)
                        inputs_checked += 1
    return circuits, runs, inputs_checked


def maximal_rectangles(matrix):
    rows, cols = len(matrix), len(matrix[0])
    rectangles = set()
    for subset in range(1, 1 << rows):
        selected = [i for i in range(rows) if subset >> i & 1]
        common = [j for j in range(cols) if all(matrix[i][j] for i in selected)]
        mask = sum(1 << (i * cols + j) for i in selected for j in common)
        if mask:
            rectangles.add(mask)
    return rectangles


def cover_number(matrix):
    cols = len(matrix[0])
    full = sum(1 << (i * cols + j) for i, row in enumerate(matrix)
               for j, value in enumerate(row) if value)
    rectangles = maximal_rectangles(matrix)
    reached = {0}
    for count in range(len(matrix) + 1):
        if full in reached:
            return count
        reached = {mask | rectangle for mask in reached for rectangle in rectangles}
    raise AssertionError("row cover must exist")


def rank(matrix, modulus=None):
    a = [[Fraction(x) for x in row] for row in matrix]
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        lead = a[r][c]
        a[r] = [v / lead for v in a[r]]
        for i in range(len(a)):
            if i != r:
                multiple = a[i][c]
                a[i] = [x - multiple * y for x, y in zip(a[i], a[r])]
                if modulus:
                    a[i] = [Fraction(int(x) % modulus) for x in a[i]]
        r += 1
    return r


def main():
    nonlinear = [t for t in range(16) if t.bit_count() % 2]
    assert len(nonlinear) == 8
    combinations_checked = 0
    for tables in product(nonlinear, repeat=3):
        counts = Counter()
        for x in product((0, 1), repeat=6):
            y = tuple(bit(t, x[2 * i], x[2 * i + 1]) ^ (t.bit_count() == 3)
                      for i, t in enumerate(tables))
            counts[y] += 1
        assert all(counts[y] == 3 ** (3 - sum(y)) for y in product((0, 1), repeat=3))
        combinations_checked += 1
    print(f"nonlinear tables: {len(nonlinear)}; disjoint triples checked: {combinations_checked}")
    circuits, runs, inputs_checked = compiler_checks()
    print(f"smooth compiler: {circuits} circuits, {runs} layouts/filter runs, {inputs_checked} inputs")
    print("smooth compiler: exact retained-input semantics and unique accepting paths passed")
    print(f"asymptotic saving per exposed nonlinear output: {1-h2(0.25):.9f} bits")
    k, q = 64, Fraction(5, 16)
    radius = int(k * q)
    support = sum(comb(k, j) for j in range(radius + 1))
    mass = sum(Fraction(comb(k, j) * 3 ** (k - j), 4 ** k)
               for j in range(radius + 1))
    assert log2(support) <= k * h2(float(q))
    print(f"finite k=64, q=5/16: log2 typical support={log2(support):.9f}, mass={float(mass):.9f}")
    k = 8
    shared_zero = Fraction(1, 2) + Fraction(1, 2 ** (k + 1))
    independent_zero = Fraction(3, 4) ** k
    assert shared_zero != independent_zero
    print(f"shared operand k=8: all-zero mass={float(shared_zero):.9f}, iid prediction={float(independent_zero):.9f}")
    mux = [[(x >> j) & 1 for j in range(4)] for x in range(16)]
    assert sum(any(row) for row in mux) == 15
    assert len({tuple(row) for row in mux}) == 16
    # Singleton rows and columns form an identity fooling set of size 4.
    assert all(mux[1 << i][j] == (i == j) for i in range(4) for j in range(4))
    print("multiplexer m=4: accepting data support=15, distinct residuals=16, rectangle cover=4")
    ip = [[(x & y).bit_count() % 2 for y in range(4)] for x in range(4)]
    assert rank(ip, 2) == 2 and cover_number(ip) == 3
    cycle = [[int(j in (i, (i + 1) % 4)) for j in range(4)] for i in range(4)]
    assert rank(cycle) == 3 and cover_number(cycle) == 4
    print("rank obstructions: inner-product GF(2) rank=2, cover=3; cycle real rank=3, cover=4")
    m, k = 16, 8
    counts = [m * 2 ** k - (2 ** k - 1)] + [1] * (2 ** k - 1)
    fixed_entropy = entropy(counts)
    assert fixed_entropy < k / 8
    print(f"adaptive entropy: max fixed-cut H={fixed_entropy:.9f}, H(T_I|I)={k:.9f}")
    print("status: all finite checks passed; no universal layout or coefficient theorem tested")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact small-instance checks and obstructions for transition compression.

This enumerates circuit inputs, not random samples of their distribution. The
results check finite identities; they do not establish a universal compiler gain.
Run with python3 frontier-method/data/check_communication.py; it imports check_algorithms.py
from its own directory.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import ceil, log2, sqrt
from random import Random
import sys

sys.dont_write_bytecode = True
from check_algorithms import Gate, Network


def traces(n, gates, out, net, order):
    """Joint output/transition labels of the exact compiled trace on every input."""
    cuts, past = [set()], set()
    for vertex in order:
        past.add(vertex)
        cuts.append({e for e, (u, v, _) in enumerate(net.edges)
                     if (u in past) != (v in past)})
    signals = [sorted({net.edges[e][2] for e in before | after})
               for before, after in zip(cuts, cuts[1:])]
    unread = sorted(set(range(n)) - {v[1] for v in net.vertices
                                    if v[0] == "wire" and v[1] < n})
    rows = []
    for x in product(range(2), repeat=n):
        values = list(x)
        for gate in gates:
            values.append(gate.evaluate(values))
        row = [(values[out], tuple(values[w] for w in ws)) for ws in signals]
        # A read site's input equals the value on its head edge, which is in
        # the adjacent-frontier union. Unreachable inputs need a final step.
        row.append((values[out], tuple(x[i] for i in unread)))
        rows.append(row)
    return rows


def check_circuit_codebooks():
    rng = Random(20261005)
    checked = strict = 0
    for _ in range(64):
        n = rng.randrange(2, 8)
        gates = [Gate(rng.randrange(16), tuple(rng.randrange(n + i) for _ in range(2)))
                 for i in range(rng.randrange(1, 4 * n + 1))]
        out = n + len(gates) - 1
        net = Network(n, gates, [(out, False)])
        for reverse in (False, True):
            order = list(net.vertices)
            if reverse:
                order.reverse()
            else:
                rng.shuffle(order)
            rows = traces(n, gates, out, net, order)
            histograms = [Counter(row[t] for row in rows) for t in range(len(rows[0]))]
            for cap in (1, 4, 9, 25):
                keep = [{e for e, mass in h.items() if mass >= cap} for h in histograms]
                discarded = sum(any(e not in good for e, good in zip(row, keep))
                                for row in rows)
                union_bound = sum(mass for h, good in zip(histograms, keep)
                                  for e, mass in h.items() if e not in good)
                retained_cost = cap * sum(map(len, keep))
                capped = sum(min(cap, mass) for h in histograms for mass in h.values())
                assert retained_cost + union_bound == capped
                assert retained_cost + discarded <= capped
                original = cap * sum(map(len, histograms))
                assert capped <= original
                strict += capped < original
                moment = sqrt(cap) * sum(sqrt(mass) for h in histograms
                                         for mass in h.values())
                assert capped <= moment + 1e-9
                checked += 1
    print(f"Compiled traces: {checked} exact cap/pruning/moment checks; "
          f"{strict} strict savings over the unpruned budget (no asymptotic claim).")


def check_optimal_separable_pruning():
    """Enumerate every codebook as an independent oracle for the cap identity."""
    checked = 0
    for masses in product(range(1, 5), repeat=4):
        for cap in range(1, 6):
            optimal = min(cap * sum(keep) + sum(m for m, k in zip(masses, keep) if not k)
                          for keep in product((0, 1), repeat=4))
            assert optimal == sum(min(cap, m) for m in masses)
            checked += 1
    print(f"Codebook optimization: {checked} exhaustive comparisons passed.")


def check_conditional_moments():
    """Verify the escort-measure identity on dependent, sometimes sparse sources."""
    rng = Random(1138)
    dimension = 6
    words = list(product((0, 1), repeat=dimension))
    for _ in range(80):
        weights = [rng.randrange(8) for _ in words]
        distribution = {x: Fraction(w, sum(weights)) for x, w in zip(words, weights) if w}
        prefix = Counter()
        for x, p in distribution.items():
            for i in range(dimension + 1):
                prefix[x[:i]] += p
        escort_total = identity = 0.0
        largest = 0.0
        for x in distribution:
            escort = multiplier = 1.0
            for i, bit in enumerate(x):
                history = x[:i]
                conditional = [prefix[history + (b,)] / prefix[history] for b in (0, 1)]
                local = sum(sqrt(p) for p in conditional)
                escort *= sqrt(conditional[bit]) / local
                multiplier *= local
            escort_total += escort
            identity += escort * multiplier
            largest = max(largest, multiplier)
        moment = sum(sqrt(p) for p in distribution.values())
        assert abs(escort_total - 1) < 1e-12
        assert abs(identity - moment) < 1e-12
        assert moment <= largest + 1e-12
    print("Conditional moments: 80 dependent-source escort identities and path budgets passed.")


def check_shared_selector():
    """Biased AND outputs need almost full support when they share a selector."""
    k = 12
    histogram = Counter()
    for x in product((0, 1), repeat=k + 1):
        histogram[tuple(x[0] & bit for bit in x[1:])] += 1
    total = 2 ** (k + 1)
    assert histogram[(0,) * k] == 2**k + 1
    assert set(histogram.values()) == {1, 2**k + 1}
    delta = Fraction(1, 100)
    mass = size = 0
    for count in sorted(histogram.values(), reverse=True):
        if mass >= (1 - delta) * total:
            break
        mass += count
        size += 1
    assert size == ceil((1 - 2 * delta) * 2**k)
    shannon = -sum((m / total) * log2(m / total) for m in histogram.values())
    renyi_half = 2 * log2(sum(sqrt(m / total) for m in histogram.values()))
    marginal_half = 2 * log2(sqrt(Fraction(1, 4)) + sqrt(Fraction(3, 4)))
    assert renyi_half > k * marginal_half  # Marginal Renyi costs are not additive.
    assert log2(size) > shannon + 4
    independent_half = k * marginal_half
    # Separate fair input pairs do tensorize, unlike the shared-selector circuit.
    p = {x: Fraction(1, 4)**sum(x) * Fraction(3, 4)**(k - sum(x))
         for x in product((0, 1), repeat=k)}
    assert abs(2 * log2(sum(sqrt(m) for m in p.values())) - independent_half) < 1e-10
    print(f"Shared selector, k={k}: Shannon={shannon:.4f} bits, "
          f"Renyi(1/2)={renyi_half:.4f}, 99%-support={size}/{2**k}; "
          f"independent AND outputs have Renyi(1/2)={independent_half:.4f}.")


if __name__ == "__main__":
    check_circuit_codebooks()
    check_optimal_separable_pruning()
    check_conditional_moments()
    check_shared_selector()

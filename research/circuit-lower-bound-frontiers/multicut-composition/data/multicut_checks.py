#!/usr/bin/env python3
"""Validates: finite entropy, conditional-information, and gate-reuse counterexamples.

Standard-library only; exhaustive uniform truth tables for named examples.
The additional B2 transcript audit uses seed 20261004 and 200 fixed trials.
This does not check the conjectured excess-token compiler or any new lower bound.
Run: python3 research/circuit-lower-bound-frontiers/multicut-composition/data/multicut_checks.py
"""

from collections import Counter
from itertools import product
from math import acos, log2, pi, sqrt
from random import Random


def entropy(values):
    counts = Counter(values)
    total = sum(counts.values())
    return -sum((count / total) * log2(count / total) for count in counts.values())


def joint(*columns):
    return list(zip(*columns))


def conditional_entropy(column, given):
    return entropy(joint(column, given)) - entropy(given)


def close(actual, expected):
    assert abs(actual - expected) < 1e-9, (actual, expected)


def parity_chain(n):
    accepted = [x for x in product((0, 1), repeat=n) if sum(x) % 2 == 0]
    transcripts = [tuple(sum(x[:i]) % 2 for i in range(2, n)) for x in accepted]
    # Exact binary-circuit graph, in an ordering that exposes one prefix parity.
    gates = [f"p{i}" for i in range(2, n + 1)]
    edges = [("x1", "p2"), ("x2", "p2")]
    edges += [(f"p{i-1}", f"p{i}") for i in range(3, n + 1)]
    edges += [(f"x{i}", f"p{i}") for i in range(3, n + 1)]
    order = ["x1", "x2", "p2"]
    for i in range(3, n + 1):
        order.extend((f"x{i}", f"p{i}"))
    for i in range(2, n):
        prefix = set(order[:order.index(f"p{i}") + 1])
        crossing = [(a, b) for a, b in edges if (a in prefix) != (b in prefix)]
        assert crossing == [(f"p{i}", f"p{i+1}")]
    excess = len(edges) - len(order)
    close(entropy(transcripts), n - 2)
    assert excess == -1
    return n, len(gates), excess, n - 2, entropy(transcripts)


def repeated_parity(n):
    inputs = list(product((0, 1), repeat=n))
    parity = [sum(x) % 2 for x in inputs]
    leave_one_out = sum(
        conditional_entropy(parity, [x[:i] + x[i + 1:] for x in inputs])
        for i in range(n)
    )
    ordered = []
    for i in range(n):
        before = [x[:i] for x in inputs]
        after = [x[:i + 1] for x in inputs]
        ordered.append(conditional_entropy(parity, before)
                       - conditional_entropy(parity, after))
    close(leave_one_out, n)
    close(sum(ordered), 1)
    close(entropy([(p,) * n for p in parity]), 1)
    return leave_one_out, sum(ordered)


def multiplexer(q):
    width = 2**q
    rows = list(product((0, 1), repeat=q + width))
    selector = [tuple(x[:q]) for x in rows]
    output = [x[q + sum(x[j] << j for j in range(q))] for x in rows]
    close(entropy(output), 1)
    close(entropy(joint(selector, output)), q + 1)
    # These are mutually exclusive tasks after selector restriction, not direct sum.
    restricted_demands = 0
    for address in range(width):
        selected = [y for x, y in zip(rows, output)
                    if sum(x[j] << j for j in range(q)) == address]
        close(entropy(selected), 1)
        restricted_demands += entropy(selected)
    return width, restricted_demands, entropy(output), entropy(joint(selector, output))


def shared_outputs(m, k):
    # P = XOR of m shared inputs; y_j = P XOR z_j. All gates are useful.
    inputs = list(product((0, 1), repeat=m + k))
    parity = [sum(x[:m]) % 2 for x in inputs]
    outputs = [tuple(p ^ x[m + j] for j in range(k))
               for x, p in zip(inputs, parity)]
    close(entropy(outputs), k)
    size = (m - 1) + k
    cone_sum = k * m
    reuse = (k - 1) * (m - 1)
    assert cone_sum == size + reuse
    return size, cone_sum, reuse, entropy(outputs)


def disjoint_outputs(m, k):
    inputs = list(product((0, 1), repeat=m * k))
    outputs = [tuple(sum(x[m * j:m * (j + 1)]) % 2 for j in range(k)) for x in inputs]
    close(entropy(outputs), k)
    return m * k, k * (m - 1), entropy(outputs)


def random_transcript_audit():
    rng = Random(20261004)
    inputs = list(product((0, 1), repeat=4))
    observed_tables = set()
    repeated_slots = 0
    for _ in range(200):
        columns = [[x[i] for x in inputs] for i in range(4)]
        for _ in range(7):
            a, b = rng.randrange(len(columns)), rng.randrange(len(columns))
            table = rng.randrange(16)
            observed_tables.add(table)
            repeated_slots += a == b
            columns.append([(table >> (2 * x + y)) & 1
                            for x, y in zip(columns[a], columns[b])])
        seen = set()
        history = [() for _ in inputs]
        entropy_sum = 0.0
        for _ in range(8):
            interface = set(rng.sample(range(len(columns)), rng.randrange(1, 5)))
            signal = [tuple(columns[i][row] for i in sorted(interface))
                      for row in range(len(inputs))]
            innovation = conditional_entropy(signal, history)
            assert -1e-9 <= innovation <= len(interface - seen) + 1e-9
            entropy_sum += innovation
            history = joint(history, signal)
            seen |= interface
        close(entropy_sum, entropy(history))
        assert entropy_sum <= min(4, len(seen)) + 1e-9
    assert observed_tables == set(range(16))
    assert repeated_slots > 0
    return 200


def main():
    print("Finite multicut audit; exhaustive named cases, random audit seed=20261004")
    print("parity_chain: n gates excess selected_cuts joint_entropy_on_acceptance")
    for n in (4, 6, 8, 10, 12):
        print(" ", *parity_chain(n))
    print("repeated_parity: n sum_leave_one_out_information chain_information")
    for n in (2, 4, 8, 12):
        print(" ", n, *repeated_parity(n))
    print("multiplexer: q branches sum_restricted_demands H(output) H(selector,output)")
    for q in (1, 2, 3):
        print(" ", q, *multiplexer(q))
    print("shared_XOR_outputs: m=5 k=4; gates cone_sum reuse_penalty H(outputs)")
    print(" ", *shared_outputs(5, 4))
    print("disjoint_parity_outputs: m=3 k=4; input_bits gates H(outputs)")
    print(" ", *disjoint_outputs(3, 4))
    print("B2 transcript chain audits passed:", random_transcript_audit())
    alpha = 3 * acos((1 + 2 * sqrt(2)) / 4) / pi
    print(f"baseline: alpha={alpha:.12f}, coefficient={1 + 1 / alpha:.12f}")
    print("conditional coefficient-5 target: alpha=0.25, rho=1, offset=s-n")
    print("ALL ASSERTIONS PASSED; no compiler or asymptotic hardness claim checked")


if __name__ == "__main__":
    main()

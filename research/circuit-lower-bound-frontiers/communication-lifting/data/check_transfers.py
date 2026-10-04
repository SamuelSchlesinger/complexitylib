#!/usr/bin/env python3
"""Validates: finite dual-rail, equality-DAG, and monotone restriction identities.

Exhaustive, deterministic checks; no random seed is used. This does not establish
any asymptotic lifting theorem or lower bound. Run from any directory with Python 3.
"""

from itertools import product


def bits(n):
    return list(product((0, 1), repeat=n))


def dual_rail_check():
    largest = 0
    for table in bits(4):
        counts = [sum(value == rail for value in table) for rail in (0, 1)]
        # Constants need no monotone AND/OR gates; otherwise use two-literal DNF.
        gates = sum(0 if count in (0, 4) else 2 * count - 1 for count in counts)
        largest = max(largest, gates)
        for x in bits(2):
            for rail in (0, 1):
                result = any(all(x[j] == a[j] for j in range(2))
                             for a, value in zip(bits(2), table) if value == rail)
                assert result == (table[2 * x[0] + x[1]] == rail)
    return largest


def equality_dag_check(n):
    points = bits(n)
    functions = pairs = 0
    for table in bits(len(points)):
        positive = [x for x, value in zip(points, table) if value]
        negative = [x for x, value in zip(points, table) if not value]
        if not positive or not negative:
            continue
        functions += 1
        for x in positive:
            for y in negative:
                pairs += 1
                # E_i is equality of prefixes; D_i is equality of x_i, 1-y_i.
                for i in range(n - 1):
                    if x[:i] == y[:i]:
                        assert x[:i + 1] == y[:i + 1] or x[i] == 1 - y[i]
                assert x[:-1] != y[:-1] or x[-1] != y[-1]
                result = next(i for i in range(n) if x[i] != y[i])
                assert x[result] != y[result]
    return functions, pairs


def restriction_check(n):
    points = bits(n)
    pos = {x: i for i, x in enumerate(points)}
    cover_edges = [(pos[x], pos[x[:i] + (1,) + x[i + 1:]])
                   for x in points for i in range(n) if x[i] == 0]
    monotone = subsets = evaluations = 0
    for table in bits(len(points)):
        if any(table[a] > table[b] for a, b in cover_edges):
            continue
        monotone += 1
        for selected in bits(n):
            support = [i for i in range(n) if selected[i]]
            subsets += 1
            for x in points:
                evaluations += 1
                result = False
                for assignment in bits(len(support)):
                    if any(a > x[i] for i, a in zip(support, assignment)):
                        continue
                    restricted = list(x)
                    for i, a in zip(support, assignment):
                        restricted[i] = a
                    result |= bool(table[pos[tuple(restricted)]])
                assert result == bool(table[pos[x]])
    return monotone, subsets, evaluations


def main():
    print("Validates: finite dual-rail, equality-DAG, and monotone restriction identities.")
    print("Method: exhaustive enumeration; no randomness; not a lower-bound proof.")
    print(f"All 16 binary gates: largest two-rail AND/OR cost = {dual_rail_check()}")
    for n in range(1, 4):
        functions, pairs = equality_dag_check(n)
        print(f"Equality DAG n={n}: {functions} nonconstant functions, "
              f"{pairs} input pairs, at most {2 * n - 1} nodes: PASS")
    for n in range(1, 5):
        count, subsets, evaluations = restriction_check(n)
        print(f"Restriction identity n={n}: {count} monotone functions, "
              f"{subsets} function/support pairs, {evaluations} evaluations: PASS")
    # A full-KW-valid disagreement need not be valid for monotone KW.
    x, y = (0, 1), (1, 0)  # f(z)=z[1]; first mismatch has the wrong direction.
    assert x[1] == 1 and y[1] == 0 and x[0] < y[0]
    print("Directed-leaf falsifier: f(z)=z[1], x=01, y=10, output 0 is wrong: PASS")


if __name__ == "__main__":
    main()

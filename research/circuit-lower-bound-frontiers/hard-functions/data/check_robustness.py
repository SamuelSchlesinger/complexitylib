#!/usr/bin/env python3
"""Validates: finite affine transport, quadratic fibers, and scalarization obstructions.

Standard library only; exhaustive finite checks, with no random choices.
Does not validate an asymptotic extractor or a circuit compiler.
Run from any directory; stdout is the saved check_robustness.txt artifact.
"""

from collections import Counter
from itertools import combinations, product


def parity(x):
    return x.bit_count() & 1


def linear(rows, x):
    return sum(parity(row & x) << i for i, row in enumerate(rows))


def affine_transport():
    n = 3
    points = range(1 << n)
    sets = list(combinations(points, 3))
    sumsets = {
        sum(1 << z for z in {a ^ b for a in left for b in right})
        for left in sets for right in sets
    }
    dispersers = [
        f for f in range(1 << (1 << n))
        if all((f & s) not in (0, s) for s in sumsets)
    ]
    matrices = [rows for rows in product(points, repeat=n)
                if len({linear(rows, x) for x in points}) == 1 << n]
    checks = 0
    for rows in matrices:
        for b in points:
            mapping = [linear(rows, x) ^ b for x in points]
            for f in dispersers:
                g = sum(((f >> mapping[x]) & 1) << x for x in points)
                assert all((g & s) not in (0, s) for s in sumsets)
                assert g.bit_count() == f.bit_count()
                checks += 1
    assert len(dispersers) == 56 and len(matrices) == 168
    print(f"Affine: n=3 K=3; {len(sumsets)} distinct exact-K sumsets;")
    print(f"  {len(dispersers)} dispersers x {len(matrices)} invertible matrices x 8 shifts")
    print(f"  = {checks} transported disperser/density checks passed.")


def padded_derivative():
    n = 3
    checks = 0
    for f in range(1 << (1 << n)):
        def padded(x):
            return ((f >> (x & 7)) & 1) ^ (x >> n)
        assert sum(padded(x) for x in range(16)) == 8
        for x in range(16):
            assert padded(x) ^ padded(x ^ 8) == 1
            checks += 1
    print(f"Padding: all 256 three-bit functions balanced; {checks} derivatives equal 1.")


def quadratic_fibers():
    n = 3
    monomials = [0, 1, 2, 4, 3, 5, 6]
    tables = []
    for coefficients in range(1 << len(monomials)):
        table = []
        for x in range(1 << n):
            value = 0
            for i, monomial in enumerate(monomials):
                if (coefficients >> i) & 1:
                    value ^= (x & monomial) == monomial
            table.append(value)
        tables.append(table)
    sizes = Counter()
    for first, second in product(tables, repeat=2):
        for a in range(1, 1 << n):
            zeros = [x for x in range(1 << n)
                     if first[x] == first[x ^ a] and second[x] == second[x ^ a]]
            sizes[len(zeros)] += 1
            if zeros:
                assert len(zeros) >= 1 << (n - 2)
                translated = {x ^ zeros[0] for x in zeros}
                assert all(x ^ y in translated for x in translated for y in translated)
    print("Quadratic: all 16384 ordered two-output maps on 3 bits, all 7 directions;")
    print(f"  derivative-zero fiber sizes: {dict(sorted(sizes.items()))}; affine dimension >=1.")


def graph_scalarization():
    n = m = 2
    checks = 0
    for outputs in product(range(1 << m), repeat=1 << n):
        # Split (x,z0) | (z1,t). Force z0 != F_0(x), t=1.
        left = [(x, 1 ^ (outputs[x] & 1)) for x in range(1 << n)]
        right = [(z1, 1) for z1 in range(2)]
        for (x, z0), (z1, t) in product(left, right):
            z = z0 | (z1 << 1)
            accepted = int(z == outputs[x]) ^ t
            assert accepted == 1
            checks += 1
    print("Graph scalarization: all 256 maps F:{0,1}^2->{0,1}^2;")
    print(f"  each balanced graph predicate has a 4 x 2 one-rectangle; {checks} points checked.")


def accounting():
    # Multiplexer uses a XOR (s AND (a XOR b)): three B2 gates.
    for a, b, s in product(range(2), repeat=3):
        assert a ^ (s & (a ^ b)) == (b if s else a)
    # Linear code: Hx=(x0 XOR x2, x1 XOR x3), rank 2.
    accepted = [x for x in range(16) if parity(x & 5) == parity(x & 10) == 0]
    assert len(accepted) == 4
    rows = (5, 10, 4, 8)
    assert len({linear(rows, x) for x in range(16)}) == 16
    for x in range(16):
        y = linear(rows, x) ^ 3
        assert int(x in accepted) == ((y & 1) & ((y >> 1) & 1))
    print("Accounting: 3-gate multiplexer checked on all 8 inputs;")
    print("  rank-2 four-bit code indicator: density 1/4, one AND after free affine basis.")
    print("Scope: finite identities only; no asymptotic hardness or compiler assertion tested.")


if __name__ == "__main__":
    print("Validates: finite affine transport, quadratic fibers, and scalarization obstructions.")
    affine_transport()
    padded_derivative()
    quadratic_fibers()
    graph_scalarization()
    accounting()

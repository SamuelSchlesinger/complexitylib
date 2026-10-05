#!/usr/bin/env python3
"""Finite audits of the MOD3 affine-block lemma; not an asymptotic proof.

Enumerate every affine flat through dimension six, independently evaluate its
Hamming residues, and construct the claimed disjoint-block cube when nonempty.
Seeded higher-dimensional cases exercise cubes with several independent blocks.
No floating-point arithmetic or external packages are used.
"""

from itertools import combinations, product
from random import Random


def span(basis):
    result = [0]
    for row in basis:
        result += [value ^ row for value in result]
    return result


def subspaces(n):
    """All binary subspaces, represented by unique reduced row-echelon bases."""
    for dimension in range(n + 1):
        for pivots in combinations(range(n), dimension):
            free = [j for j in range(n) if j not in pivots]
            positions = [(i, j) for i, p in enumerate(pivots) for j in free if j > p]
            for bits in range(1 << len(positions)):
                basis = [1 << p for p in pivots]
                for k, (i, j) in enumerate(positions):
                    if (bits >> k) & 1:
                        basis[i] |= 1 << j
                yield basis, free


def block_cube(n, q, base, in_kernel):
    """Search each coordinate block directly; return directions and residue changes."""
    width = 2 * q + 1
    directions = []
    changes = []
    for start in range(0, n - width + 1, width):
        for local in range(1, 1 << width):
            direction = local << start
            if not in_kernel(direction):
                continue
            change = ((base ^ direction).bit_count() - base.bit_count()) % 3
            if change:
                directions.append(direction)
                changes.append(change)
                break
        else:
            raise AssertionError((n, q, base, start, "no residue-changing direction"))
    assert len(directions) == n // width
    return directions, changes


def check_cube(base, directions, changes, in_kernel):
    for i, direction in enumerate(directions):
        assert direction != 0 and in_kernel(direction)
        assert all(direction & earlier == 0 for earlier in directions[:i])
    for choice in product((0, 1), repeat=len(directions)):
        point = base
        expected = base.bit_count()
        for bit, direction, change in zip(choice, directions, changes):
            if bit:
                point ^= direction
                expected += change
        assert in_kernel(point ^ base)
        assert point.bit_count() % 3 == expected % 3
        # Complement precisely the coordinates with coefficient -1 mod 3.
        transformed = sum(bit if change == 1 else 1 - bit
                          for bit, change in zip(choice, changes))
        offset = base.bit_count() + 2 * changes.count(2)
        assert point.bit_count() % 3 == (offset + transformed) % 3


def exhaustive_flats():
    # Independent known affine-subspace counts, including points and the whole cube.
    expected_counts = [3, 11, 51, 307, 2451, 26387]
    total_cubes = 0
    for n, expected_count in enumerate(expected_counts, start=1):
        flat_count = 0
        residue_constant = 0
        for basis, free in subspaces(n):
            kernel = frozenset(span(basis))
            q = n - len(basis)
            for base in span([1 << j for j in free]):
                flat_count += 1
                residues = {(base ^ vector).bit_count() % 3 for vector in kernel}
                if len(residues) == 1:
                    residue_constant += 1
                    assert 2 * len(basis) <= n
                directions, changes = block_cube(n, q, base, kernel.__contains__)
                check_cube(base, directions, changes, kernel.__contains__)
                total_cubes += bool(directions)
        assert flat_count == expected_count, (n, flat_count, expected_count)
        print(f"n={n}: {flat_count} affine flats, {residue_constant} constant-residue flats; PASS")
    print(f"Exhaustive nonempty block cubes: {total_cubes}; PASS")


def larger_cubes():
    rng = Random(20261004)
    count = 0
    largest = 0
    for n in (12, 18, 21):
        for q in (1, 2, 3):
            for _ in range(32):
                # Identity pivot columns ensure the constraints have rank exactly q.
                rows = [(1 << i) | (rng.getrandbits(n - q) << q) for i in range(q)]
                base = rng.getrandbits(n)

                def in_kernel(vector):
                    return all((row & vector).bit_count() % 2 == 0 for row in rows)

                directions, changes = block_cube(n, q, base, in_kernel)
                check_cube(base, directions, changes, in_kernel)
                largest = max(largest, len(directions))
                count += 1
    print(f"Seeded larger flats: {count}, largest cube dimension {largest}; PASS")


def arithmetic_readout():
    count = 0
    for n in range(3, 13):
        scale = 1 << (n + 1)
        multiplier = (scale + 2) // 3
        odd_mask = sum(1 << i for i in range(1, n, 2))
        assert multiplier < 1 << n
        for operand in range(1 << n):
            quotient = operand // 3
            product_bits = operand * multiplier
            assert product_bits // scale == quotient
            q0 = (product_bits >> (n + 1)) & 1
            q1 = (product_bits >> (n + 2)) & 1
            a0, a1 = operand & 1, (operand >> 1) & 1
            readout = (1 ^ a0 ^ q0) & (1 ^ a1 ^ a0 ^ q1)
            assert readout == (operand % 3 == 0)
            z = operand ^ odd_mask
            assert operand % 3 == (z.bit_count() - n // 2) % 3
            count += 1
    print(f"Exact reciprocal and quadratic MOD3 readout: {count} operands; PASS")


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def quadratic_projection_obstruction():
    """Evaluate sparse inputs of a parity-conjunction, then recover its ANF quadratic part.

    The evaluator and the predicted complement-permutation matrix are separate.
    This checks a counterexample to projection-based rank charging, not a circuit
    lower bound or an exhaustive search over possible invariants.
    """
    for k in range(2, 9):
        n = 1 << k
        all_ones = n - 1

        def evaluate(support):
            parities = [sum((a >> j) & 1 for a in support) % 2 for j in range(k)]
            return int(all(parities))

        rows = []
        for a in range(n):
            row = 0
            for b in range(n):
                coefficient = 0 if a == b else (
                    evaluate((a, b)) ^ evaluate((a,)) ^ evaluate((b,)))
                predicted = int(a ^ b == all_ones) ^ int(a == all_ones) ^ int(b == all_ones)
                assert coefficient == predicted
                row |= coefficient << b
            rows.append(row)
        rank = binary_rank(rows)
        assert rank == n - 2
        assert all(row.bit_count() % 2 == 0 and row & 1 == 0 for row in rows)
        print(f"Quadratic projection: k={k}, inputs={n}, rank={rank}, "
              f"free-XOR binary ANDs={k-1}, unbounded gates={k+1}; PASS")


if __name__ == "__main__":
    exhaustive_flats()
    larger_cubes()
    arithmetic_readout()
    quadratic_projection_obstruction()

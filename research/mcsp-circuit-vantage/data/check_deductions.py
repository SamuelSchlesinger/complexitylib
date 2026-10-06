#!/usr/bin/env python3
"""Validates: absent-pattern cubes, counting scales, and repeated gate charges.

Finite exhaustive checks support the paper arguments; they do not establish
an asymptotic circuit lower bound. Uses only the Python standard library.
"""

from itertools import combinations
from fractions import Fraction


def project(word, coordinates):
    return sum(((word >> position) & 1) << j for j, position in enumerate(coordinates))


def check_absent_patterns():
    cases = 0
    for dimension in range(1, 4):
        words = range(1 << dimension)
        for family_mask in range(1 << (1 << dimension)):
            family = {word for word in words if family_mask >> word & 1}
            for fixed in range(1, dimension + 1):
                if len(family) >= 1 << fixed:
                    continue
                for coordinates in combinations(range(dimension), fixed):
                    patterns = {project(word, coordinates) for word in family}
                    absent = set(range(1 << fixed)) - patterns
                    assert len(absent) >= (1 << fixed) - len(family)
                    for pattern in absent:
                        cube = {word for word in words if project(word, coordinates) == pattern}
                        assert len(cube) == 1 << (dimension - fixed)
                        assert cube.isdisjoint(family)
                    cases += 1
    print(f"Absent-pattern lemma: {cases} exhaustive family/coordinate cases passed (N <= 3).")


def check_counting_scales():
    print("B2 count bound B=(s+1)(n+s)[16(n+s)^2]^s; d=floor(log2 B)+1, s=n^2:")
    for arity in (16, 32, 64, 128):
        threshold = arity * arity
        budget = (threshold + 1) * (arity + threshold) * (
            16 * (arity + threshold) ** 2
        ) ** threshold
        fixed = budget.bit_length()
        dimension = 1 << arity
        assert budget < 1 << fixed
        assert fixed <= dimension
        print(f"  n={arity}: N=2^{arity}, d={fixed}, NO-cube dimension=2^{arity}-{fixed}")


def check_nested_charges():
    print("Nested AND regions: Q=sum of contained gate counts, M=max gate multiplicity:")
    for height in range(1, 9):
        leaves = 1 << height
        # A complete binary AND tree. Region roots are all internal vertices.
        # Each region demands one charge from each gate in its subtree.
        loads = {gate: 0 for gate in range(1, leaves)}
        total = 0
        for region in range(1, leaves):
            frontier = [region]
            while frontier:
                gate = frontier.pop()
                loads[gate] += 1
                total += 1
                if 2 * gate < leaves:
                    frontier.extend((2 * gate, 2 * gate + 1))
        multiplicity = max(loads.values())
        size = leaves - 1
        assert multiplicity == height
        assert total == (height - 1) * leaves + 1
        assert total <= multiplicity * size
        print(f"  leaves={leaves}: S={size}, Q={total}, M={multiplicity}, Q/M<=S")


def check_repeated_anchor_neighbors():
    cases = 0
    for width in range(1, 4):
        for family_mask in range(1, 1 << (1 << width)):
            anchors = [word for word in range(1 << width) if family_mask >> word & 1]
            for repetitions in (2, 4):
                dimension = width * repetitions
                repeated = [
                    sum(word << (block * width) for block in range(repetitions))
                    for word in anchors
                ]
                degrees = {}
                for word in repeated:
                    for coordinate in range(dimension):
                        neighbor = word ^ (1 << coordinate)
                        degrees[neighbor] = degrees.get(neighbor, 0) + 1
                edges = dimension * len(anchors)
                assert sum(degrees.values()) == edges
                if repetitions == 2:
                    assert max(degrees.values()) <= 2
                    assert edges * edges <= 2 * dimension * len(anchors) * len(degrees)
                else:
                    assert max(degrees.values()) == 1
                    assert edges * edges == dimension * len(anchors) * len(degrees)
                cases += 1
    print(f"Repeated-anchor neighbor measure: {cases} cases passed (block width <= 3).")


def check_refuter_samples():
    # Once the raw-family agreement error term is at most 1/144, the
    # probability that one independent sample misses an error is at most 143/144.
    for accuracy_bits in range(1, 17):
        failure = Fraction(143, 144) ** (144 * accuracy_bits)
        assert failure <= Fraction(1, 1 << accuracy_bits)
    print("Refuter sampling: (143/144)^(144k) <= 2^(-k) for k=1,...,16.")


if __name__ == "__main__":
    check_absent_patterns()
    check_counting_scales()
    check_nested_charges()
    check_repeated_anchor_neighbors()
    check_refuter_samples()

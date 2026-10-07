#!/usr/bin/env python3
"""Validates: affine-line pair laws, covariance, and wrap identities at P=2,3.

These exhaustive finite checks accompany the analytic deductions in ../index.md.
The channel is the H=4, h_0=2 specialization of OpenAI, Exact Derandomization
of Logarithmic Space: L = RL = BPL (2026), Lemmas 3.1 and 6.3, pinned at:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
The exact pair law and C_var=4 improvement are deductions in this exposition.
This script does not verify a spectral gap or a derandomization theorem.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product


def add(left, right, prime):
    return tuple((a + b) % prime for a, b in zip(left, right))


def scale(scalar, vector, prime):
    return tuple(scalar * a % prime for a in vector)


def evaluate(channel, identifier, prime):
    intercept, slope = channel
    return add(intercept, scale(identifier, slope, prime), prime)


def retained(vector, side):
    return all(coordinate < side for coordinate in vector)


def linear(vector, shear):
    """The identity or a signed elementary matrix acting on coordinates 0,1."""
    return (vector[0] + shear * vector[1], *vector[1:])


def variant(channel, prime, side, shear, translation, wrap):
    intercept, slope = channel
    moved = list(linear(intercept, shear))
    moved[0] += translation + side * wrap
    return (
        tuple(a % prime for a in moved),
        tuple(a % prime for a in linear(slope, shear)),
    )


def validate(prime):
    vectors = tuple(product(range(prime), repeat=4))
    nonzero = tuple(vector for vector in vectors if any(vector))
    channels = tuple(product(vectors, nonzero))
    universe = prime**4
    total = len(channels)
    assert total == universe * (universe - 1)

    # Every distinct identifier pair realizes each ordered distinct value pair once.
    for x, y in combinations(range(prime), 2):
        pairs = Counter(
            (evaluate(channel, x, prime), evaluate(channel, y, prime))
            for channel in channels
        )
        assert len(pairs) == total
        assert set(pairs.values()) == {1}
        assert all(left != right for left, right in pairs)

        for side_x, side_y in product(range(1, prime + 1), repeat=2):
            hits = sum(
                retained(left, side_x) and retained(right, side_y)
                for left, right in pairs
            )
            assert hits == side_x**4 * side_y**4 - min(side_x, side_y) ** 4

    # Exact covariance and count variance for every nonempty identifier subset.
    values = tuple(
        tuple(evaluate(channel, y, prime) for y in range(prime))
        for channel in channels
    )
    for side in range(1, prime + 1):
        marginal = Fraction(side**4, universe)
        pair_probability = Fraction(side**4 * (side**4 - 1), total)
        covariance = pair_probability - marginal**2
        assert covariance == -marginal * (1 - marginal) / (universe - 1)
        for count in range(1, prime + 1):
            for identifiers in combinations(range(prime), count):
                counts = [
                    sum(retained(row[y], side) for y in identifiers)
                    for row in values
                ]
                mean = Fraction(sum(counts), total)
                variance = Fraction(sum(z * z for z in counts), total) - mean**2
                assert mean == count * marginal
                assert variance <= mean
                lower_tail = Fraction(sum(2 * z < mean for z in counts), total)
                assert lower_tail <= 4 / mean

    # All nonconstant affine identifier substitutions biject the coefficient space.
    for alpha, beta in product(range(1, prime), range(prime)):
        transformed = {
            (add(u, scale(beta, v, prime), prime), scale(alpha, v, prime))
            for u, v in channels
        }
        assert transformed == set(channels)
        for channel in channels:
            u, v = channel
            changed = (add(u, scale(beta, v, prime), prime), scale(alpha, v, prime))
            for y in range(prime):
                assert evaluate(changed, y, prime) == evaluate(
                    channel, (alpha * y + beta) % prime, prime
                )

    # Representative shears/translations: each fixed wrap is a full-space bijection;
    # on a slice exactly one wrap realizes the conditional torus operation.
    generators = ((1, 0), (-1, 0), (0, 1), (0, -1))
    for side, (shear, translation) in product(range(1, prime + 1), generators):
        for wrap in range(-2, 3):
            images = {
                variant(channel, prime, side, shear, translation, wrap)
                for channel in channels
            }
            assert images == set(channels)
        for channel in channels:
            for y in range(prime):
                w = evaluate(channel, y, prime)
                if not retained(w, side):
                    continue
                raw = list(linear(w, shear))
                raw[0] += translation
                wraps = [z for z in range(-2, 3) if 0 <= raw[0] + side * z < side]
                assert len(wraps) == 1
                z = wraps[0]
                expected = (raw[0] + side * z, *raw[1:])
                changed = variant(channel, prime, side, shear, translation, z)
                assert evaluate(changed, y, prime) == expected
                assert expected == tuple(a % side for a in raw)

    print(f"P={prime}: {total} channels; pair, variance, affine, and wrap checks passed")


if __name__ == "__main__":
    for field_prime in (2, 3):
        validate(field_prime)

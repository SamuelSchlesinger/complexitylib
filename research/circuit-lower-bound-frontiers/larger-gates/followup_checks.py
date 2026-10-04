#!/usr/bin/env python3
"""Reproduce the finite checks in followup-audit.md; not a lower-bound proof."""

from itertools import product
from math import log2


def check_u2_interface():
    codes = []
    for a, b in product(range(2), repeat=2):
        code = (a * (1 - b), (1 - a) * b, a * b)
        assert (code[0] | code[2], code[1] | code[2]) == (a, b)
        codes.append(code)
    assert len(set(codes)) == 4
    assert all(tuple(1 - bit for bit in code) not in codes for code in codes)
    print("U2 interface: 4 distinct codewords, 0 complementary pairs, decoding exact")


def check_mod3_hyperplanes():
    for dimension in range(4, 9):
        points = list(product(range(2), repeat=dimension))
        checked = 0
        for normal in points[1:]:
            for offset in range(2):
                cell = [
                    point for point in points
                    if sum(a * x for a, x in zip(normal, point)) % 2 == offset
                ]
                assert len(cell) == 2 ** (dimension - 1)
                assert {sum(point) % 3 == 0 for point in cell} == {False, True}
                checked += 1
        print(f"MOD3 dimension {dimension}: {checked} hyperplanes, all bichromatic")


def check_mod3_observations():
    for rank in range(1, 5):
        group = list(product(range(3), repeat=rank))
        states = {
            tuple((bits[2 * i] + bits[2 * i + 1]) % 3 for i in range(rank))
            for bits in product(range(2), repeat=2 * rank)
        }
        assert states == set(group)

        def translate(left, right):
            return tuple((x + y) % 3 for x, y in zip(left, right))

        def stabilizer(observe):
            return [
                shift for shift in group
                if all(observe(translate(state, shift)) == observe(state) for state in group)
            ]

        sum_invariants = stabilizer(lambda state: sum(state) % 3 == 0)
        zero_invariants = stabilizer(lambda state: all(x == 0 for x in state))
        assert len(sum_invariants) == 3 ** (rank - 1)
        assert len(zero_invariants) == 1
        print(
            f"MOD3 rank {rank}: {len(states)} reachable states; "
            f"sum quotient 3, singleton quotient {len(states)}"
        )


def main():
    check_u2_interface()
    check_mod3_hyperplanes()
    check_mod3_observations()
    entropy = -0.25 * log2(0.25) - 0.75 * log2(0.75)
    deficit = 1 - entropy
    print(f"Entropy deficit: {deficit:.14f}")
    print(f"Pairing/entropy coefficient: {(1 + 2 * deficit) / (1 + deficit):.14f}")


if __name__ == "__main__":
    main()

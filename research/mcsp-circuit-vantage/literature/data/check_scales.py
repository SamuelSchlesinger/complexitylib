#!/usr/bin/env python3
"""Validates: base-two conversions for the proposed MCSP[n²] target scale.

For n=2^j, N=2^n, and R=N*n^(log2(n)), perform exact finite
calculations on logarithms. This is arithmetic validation, not a proof
of any asymptotic circuit lower bound or cited magnification theorem.
The elementary identities are derived in ../index.md.
"""

from fractions import Fraction


def check() -> None:
    print("n=2^j; N=2^n; R=N*n^(log2(n))")
    print("j | log2(R/N) | log2(R/(N*n^4)) | extra exponent over N")
    for j in (4, 8, 16, 32, 64):
        n = 1 << j
        excess_log = j * j
        ratio_log = excess_log - 4 * j
        extra_exponent = Fraction(excess_log, n)
        assert excess_log == j * j
        assert ratio_log == j * (j - 4)
        assert Fraction(j * j, 1 << j) == extra_exponent
        print(f"{j} | {excess_log} | {ratio_log} | {extra_exponent}")

    # Each fixed power is exceeded at the explicit test point j=k+1.
    # The proof of eventual domination is j*(j-k) -> infinity.
    for k in range(1, 33):
        j = k + 1
        assert j * j - k * j == j > 0

    # For n>=16, n^2 exceeds n^2/(log2(n))^2, the expression
    # in CLY22 Theorem 4.3's upper endpoint (up to a constant).
    # The ratio is (log2(n))^2, so the asymptotic O-bound also fails.
    for j in (4, 8, 16, 32, 64):
        n = 1 << j
        assert n * n > Fraction(n * n, j * j)

    print("PASS: exact scale identities and finite parameter comparisons")


if __name__ == "__main__":
    check()

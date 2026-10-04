# Quantitative requirements for a stronger lower bound

This ledger separates improvement in a proof ingredient from improvement in the final circuit
theorem. The starting point is the repository's [cutwidth guide](../../docs/algebraic/cutwidth-lower-bound.md),
not a claim about publication priority. All asymptotic parameters below use the full input length.

## The current scalar transfer

The present rectangle-counting proof compares at least `2^(n-2)` accepted inputs with
`N * 2^(w+3) * K^2`, where `log K = o(n)`, and bounds the cutwidth by
`w <= (A + eta)(s-n+o(n)) + O(log n)` in the candidate linear-size regime.
Consequently its leading circuit coefficient is `L = 1 + 1/A`.
Compression transports a universal cubic pathwidth coefficient `p` to `A = 2p`.

These are deductions from the displayed transfer, not new graph theorems:

| Desired circuit coefficient | Sufficient cubic coefficient p |
| --- | --- |
| 4 | 1/6 |
| Current Gaussian value, about 4.5625 | About 0.14035 |
| 23/5 = 4.6 | 5/36 |
| 5 | 1/8 |
| 6 | 1/10 |
| 10 | 1/18 |

The target must control every prefix of one ordering on every sufficiently large graph in the
actual compiler's image, with arbitrarily small positive slack. A bisection, a random-graph
statement, or an improvement at a single threshold does not supply this contract.

## Changing the compiler and hardness measure

Suppose an exact representation compiler has size at most
`2^(alpha*(s-n) + o(n))`, and the same hard family requires representations of size at least
`2^(rho*n - o(n))` in precisely that target model. Taking logarithms yields
`s >= (1 + rho/alpha)n - o(n)` for `alpha > 0`.
The deduction assumes the stated error terms are uniform in the candidate linear-size range.
If a compiler instead costs `2^(alpha*s + beta*n + o(n))`, its coefficient is
`(rho-beta)/alpha`; the `+1` cannot be carried over without the `s-n` offset.

Every route must account for:

- Whether the representation is Boolean, nonnegative arithmetic, or signed arithmetic.
- Whether it represents the whole function, a count, an approximation, or one witness.
- Whether variable partitions may change between gates or rectangles.
- Whether its size counts states, edges, bits, gates, wires, or real-number parameters.
- The input blow-up, explicitness class, uniformity, and any circuit-description overhead.
- Whether finding a good representation is necessary for the proposed consequence.

## Gains that do not automatically compose

Improving `log K = o(n)` to `O(log n)` changes a lower-order loss in the current proof.
An alternative compiler with the same leading exponent does not add another copy of `n`
to the hardness inequality. Two cuts can transmit the same state, and two hard outputs can
reuse the same gates. A claimed gain from combining methods requires one inequality that
charges all shared resources at most once.

Likewise, a faster algorithm on linear-size circuits does not by itself satisfy a theorem
requiring a SAT algorithm on every polynomial-size circuit. A lower bound for NEXP is a
different outcome from a stronger explicit-P linear coefficient. Both can be valuable,
but their function classes and quantifiers must remain visible.

## Validation

[transfer_coefficients.py](data/transfer_coefficients.py) computes the numerical conversion;
[its output](data/transfer_coefficients.txt) contains arithmetic only. It does not validate
any candidate graph inequality or circuit compiler.

# Top-down parity lower bounds

Source: Oliver Korten, [*Top-Down Lower Bounds for All Depths*, ECCC TR26-221](https://eccc.weizmann.ac.il/report/2026/221/),
30 September 2026. The target is **Theorem 3**, with communication cost
`Omega_d(n^(1/(d-1)))` and the resulting exponential wire lower bound.

## Checked layer

The public APIs are `Complexitylib.BooleanAnalysis.HarmonicMean`,
`Complexitylib.BooleanAnalysis.Bernoulli`, and
`Complexitylib.BooleanAnalysis.LightPatterns`, under `Complexity.BooleanAnalysis`.

| Paper | Lean declaration | Status |
| --- | --- | --- |
| Definition 5 | `harmonicTransform`, `coordinateMarginal` | Defined, with representation equivalence proved |
| Lemma 11 | `harmonicTransform_variational`, `harmonicMean_variational` | Proved, including zero entries |
| Corollary 1 | `harmonicTransform_concave`, `harmonicTransform_antitone`, `harmonicTransform_le_expect` | Proved |
| Lemma 12 | `expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform` | Proved for every dimension |
| Intermediate estimate in Lemma 10 | `harmonicTransform_good_probability` | Proved for normalized densities bounded by `B` |
| Reciprocal-density Markov step | `coordinateMarginal_light_fraction_le` | Proved on actual projected patterns |
| Downward-family transference | `bernoulliAverage_lowerSet_transfer`, `bernoulliAverage_lowerSet_pow_le` | Proved, including rate zero |
| Lemma 10, sparse-sampling conclusion | `harmonicTransform_sparse_good_probability`, `improved_light_patterns_density` | Proved with the exact constants |
| Lemma 10, probability masses and pattern counts | `improved_light_patterns`, `coordinateMarginal_normalize` | Proved for every real `k >= 1` |
| Improved mirror-set argument and Theorem 3 | — | Not yet formalized |

A coordinate set is a Boolean membership function. Expectations use finite
Mathlib sums. `projectionAverage` represents a marginal on the full cube;
`projectionAverage_eq_coordinateMarginal` and
`harmonicTransform_eq_harmonicMean_coordinateMarginal` prove agreement with
the actual selected-coordinate cube. `expect_coordinateMarginal` preserves
normalization. The harmonic mean is zero when any entry is zero, implementing
the paper's extended-real convention. No strict-positivity hypothesis is added.

`improved_light_patterns` represents a distribution by nonnegative real masses
summing to one. Its bound `mass x <= 2^(k-n)` is exactly min-entropy deficit at
most `k`. `coordinateMass` sums the masses of all completions of a projected
pattern; its total mass is preserved. `coordinateMarginal_normalize` proves
that normalizing input masses by `2^n` normalizes each marginal by `2^|R|`.
The theorem counts actual projected patterns with mass at most
`2^(-|R|-2*k-2)`, obtaining the paper's bound `2^(|R|-k)` with probability at
least `63/64` whenever `0 <= r <= 1/(512*k)`. No positivity or nonempty-support
restriction excludes zero masses, dimension zero, or rate zero.

The transfer argument is credited by Korten to Yufei Zhao's
[*Probabilistic Methods in Combinatorics*](https://yufeizhao.com/pm/probmethod_notes.pdf),
Lemma 4.3.7. The checked proof first establishes the law of a union of
independent masks and monotonicity in the sampling rate, then iterates the
union argument. This gives `P_r(A) >= P_(1/4)(A)^(5*r)` for nonempty downward
families and `0 <= r <= 1/20`.

## Remaining proof layers

1. Formalize conditional fibers and their average entropy-deficit bound
   (Lemma 4), then the guiding distributions and the mirror-set argument.
   Derive the `O(kp)` version from Lemma 10, tracking the changed deficit
   constants rather than copying the `65k` parameter from Lemma 5 unchanged.
2. Add general, bounded-round KW protocols with bounded message alphabets,
   subrectangle restriction, and their adversary theorem. The existing
   `Complexity.KarchmerWigderson.Protocol` is monotone and sends one bit per
   node; it is not the protocol model needed here.
3. Instantiate the parity adversary, solve the parameter recurrence, and
   connect the protocol obstruction to unbounded-fan-in De Morgan circuits,
   with explicit wire accounting, before deriving the asymptotic bound.

This track does not use the existing random-restriction parity lower bound
to stand in for the report's top-down argument. Lemma 10 is proved; Theorem 3
remains unformalized and is not assumed as an axiom or hypothesis.

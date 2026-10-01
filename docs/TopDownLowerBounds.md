# Top-down parity lower bounds

Source: Oliver Korten, [*Top-Down Lower Bounds for All Depths*, ECCC TR26-221](https://eccc.weizmann.ac.il/report/2026/221/),
30 September 2026. The target is **Theorem 3**, with communication cost
`Omega_d(n^(1/(d-1)))` and the resulting exponential wire lower bound.

## Checked layer

The public API is `Complexitylib.BooleanAnalysis.HarmonicMean`, under
`Complexity.BooleanAnalysis`.

| Paper | Lean declaration | Status |
| --- | --- | --- |
| Definition 5 | `harmonicTransform`, `coordinateMarginal` | Defined, with representation equivalence proved |
| Lemma 11 | `harmonicTransform_variational`, `harmonicMean_variational` | Proved, including zero entries |
| Corollary 1 | `harmonicTransform_concave`, `harmonicTransform_antitone`, `harmonicTransform_le_expect` | Proved |
| Lemma 12 | `expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform` | Proved for every dimension |
| Intermediate estimate in Lemma 10 | `harmonicTransform_good_probability` | Proved for normalized densities bounded by `B` |
| Reciprocal-density Markov step | `coordinateMarginal_light_fraction_le` | Proved on actual projected patterns |
| Lemma 10, sparse-sampling conclusion | — | Not yet formalized |
| Improved mirror-set argument and Theorem 3 | — | Not yet formalized |

A coordinate set is a Boolean membership function. Expectations use finite
Mathlib sums. `projectionAverage` represents a marginal on the full cube;
`projectionAverage_eq_coordinateMarginal` and
`harmonicTransform_eq_harmonicMean_coordinateMarginal` prove agreement with
the actual selected-coordinate cube. `expect_coordinateMarginal` preserves
normalization. The harmonic mean is zero when any entry is zero, implementing
the paper's extended-real convention. No strict-positivity hypothesis is added.

## Remaining proof layers

1. Prove the downward-closed-family transference inequality, credited in the
   report to Yufei Zhao's *Probabilistic Methods in Combinatorics*, Lemma 4.3.7.
   Apply it to the good-coordinate sets, combine the proved probability and
   light-pattern estimates, and prove Lemma 10 with its constants.
2. Formalize conditional fibers and their average entropy-deficit bound
   (Lemma 4), then the guiding distributions and the mirror-set argument.
   Derive the `O(kp)` version from Lemma 10, tracking the changed deficit
   constants rather than copying the `65k` parameter from Lemma 5 unchanged.
3. Add general, bounded-round KW protocols with bounded message alphabets,
   subrectangle restriction, and their adversary theorem. The existing
   `Complexity.KarchmerWigderson.Protocol` is monotone and sends one bit per
   node; it is not the protocol model needed here.
4. Instantiate the parity adversary, solve the parameter recurrence, and
   connect the protocol obstruction to unbounded-fan-in De Morgan circuits,
   with explicit wire accounting, before deriving the asymptotic bound.

This track does not use the existing random-restriction parity lower bound
to stand in for the report's top-down argument. Neither Lemma 10 nor Theorem 3
is assumed as an axiom or hypothesis in the checked layer.

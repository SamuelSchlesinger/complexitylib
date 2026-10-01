# Top-down parity and majority lower bounds

Source: Oliver Korten, [*Top-Down Lower Bounds for All Depths*, ECCC TR26-221](https://eccc.weizmann.ac.il/report/2026/221/),
30 September 2026. **Theorem 3 is formalized**, with communication cost
`Omega_d(n^(1/(d-1)))` and the resulting exponential wire lower bound.
The argument is also extended to strict majority with the same exponent,
using the two Hamming layers on either side of its threshold. This extension
is proved here; Korten's Theorem 3 states the parity result.

## Checked layer

The public APIs are `Complexitylib.BooleanAnalysis.HarmonicMean`,
`Complexitylib.BooleanAnalysis.Bernoulli`, and
`Complexitylib.BooleanAnalysis.LightPatterns`, under `Complexity.BooleanAnalysis`.
`Complexitylib.BooleanAnalysis.Fibers` supplies the conditional-fiber layer.
`Complexitylib.BooleanAnalysis.CoordinateSampling` and
`Complexitylib.BooleanAnalysis.MirrorSets` complete the improved mirror-set lemma.
`Complexitylib.Circuits.KarchmerWigderson.TopDown` exports both parts of
Theorem 3, using the general protocol model in `KarchmerWigderson.Rounds`
and the circuit translation in `KarchmerWigderson.Circuit`.
`Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority` exports the
majority extension, including its initialization lemmas.

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
| Lemma 10, probability masses and pattern counts | `improved_light_patterns`, `coordinateMarginal_normalize` | Proved for real `k >= 1` and arbitrary finite coordinate types |
| Lemma 4, conditional-fiber entropy | `expect_uniformDeficit_coordinateFiber` | Proved for arbitrary finite coordinate types |
| Good fibers in the mirror-set proof | `coordinateFiber_good_probability` | Proved with the exact `64*k` and `63/64` constants |
| Conditional coordinate law | `bernoulliAverage_union_difference_subtype`, `conditionalSamplingRate_bounds` | Proved, including the dependent selected-coordinate type |
| Definition 2, density limits | `IsDensityLimit` | Defined using actual fiber density |
| Completion estimate in the improved mirror argument | `mirror_bad_modifications_probability` | Proved with probability `31/32` |
| Improved mirror-set lemma | `improved_mirror_set` | Proved with constants `32768` and `194` |
| General bounded-round KW protocols | `KarchmerWigderson.RoundProtocol`, `RoundProtocol.SolvesKW` | Defined with arbitrary finite message alphabets |
| Rectangle invariant | `KarchmerWigderson.DensityRectangle` | Defined with an actual sampling rate below the rate cap |
| Bounded-round adversary | `RoundProtocol.not_solves_density`, `RoundProtocol.not_solves_bounded_density` | Proved for adaptive speakers and early termination |
| Bilateral initialization | `RoundProtocol.not_solves_bilateral_density`, `RoundProtocol.not_solves_bilateral_density_with_deficit` | Proved, saving the first mirror step, including arbitrary initial deficit at least one |
| Explicit parity bound | `RoundProtocol.not_solves_parity_finite` | Proved with the finite inequality below |
| Theorem 3, communication | `KarchmerWigderson.parity_communication_lower_bound` | Proved for every fixed number of rounds at least two |
| Lemma 1, circuit-to-protocol direction | `Circuit.exists_roundProtocol` | Proved for unbounded AND/OR circuits with free input negations |
| Theorem 3, wires | `Circuit.parity_wire_lower_bound` | Proved for the library's circuit depth and total input-wire count |

Analytic declarations above are in `Complexity.BooleanAnalysis`. The other
names are under `Complexity`; `RoundProtocol` abbreviates
`Complexity.KarchmerWigderson.RoundProtocol` in the table.

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

`coordinateFiber X S x` contains patterns on `S` whose completions, using `x`
outside `S`, lie in `X`. Its entropy deficit is therefore measured in the
`|S|`-dimensional cube. `card_coordinateFiber` identifies its size with the
full-cube conditional fiber. A finite log-sum inequality proves that the
average deficit, for a uniform point of nonempty `X`, is at most that of `X`.
Markov then gives deficit at most `64*k` with probability at least `63/64`.
`uniformMass_le_rpow` connects this deficit bound to Lemma 10's mass bound.
All entropy interpretations require nonempty sets; the real-valued deficit
definition documents its finite extension at the empty set.

For independent `P` and `Q`, the joint sampling theorem identifies
`S = P union Q` and `R = P \ Q`: conditional on `S`, the coordinates of `R`
inside `S` are independent with rate `p*(1-q)/(p+q-p*q) <= p/q`. This is an
identity of finite expectations, including tests depending on the subtype `S`.
Applying Lemma 10 with deficit parameter `64*k` gives a completion density of
at least `2^(-194*k)` for all but a `2^(-k-6)` fraction of first modifications,
with probability at least `31/32`, when `q = 32768*k*p <= 1/2`.

The checked guiding distribution samples uniformly from `Y` within a dense
fiber, and from the entire fiber otherwise. Its density is at most `2^k`.
This replaces the paper's fixed-size guiding sets with uniform conditional
sampling and avoids rounding cardinalities. It lands in `Y`
with probability at least `3/4`, and has subsequent completion failure
probability at most `1/16`. Consequently `improved_mirror_set` gives a nonempty
`Y' subset Y` of deficit at most `2*k+2`, every point of which is a
`(q,194*k)`-limit of `X`. The constants are explicit choices for Korten's
Section 3 argument with the improved Section 4 lemma.

## Protocol model and adversary

`RoundProtocol I M d` is a deterministic tree of at most `d` messages from
`M`. A node's speaker is determined by the transcript; the sent message
depends only on that speaker's input. A leaf specifies a coordinate where
the inputs must differ. Alice holds a zero-input and Bob a one-input of the
function. The alphabet bound `card M <= 2^m` represents per-message cost.
The protocol may terminate early, and the coordinate difference can have
either orientation. This is the general KW game from Korten's Section 1.1.

`DensityRectangle X Y p k` says both sets are nonempty and have deficit at
most `k`, and one side consists of `(r,k)`-limits of the other for some
`0 < r <= p`. Keeping the actual rate is essential: a density-limit
condition is not assumed monotone in its sampling rate. Selecting a message
cell adds at most `m` to the deficit. If the limit condition faces the wrong
speaker, the improved mirror lemma first restricts that speaker's set.
The next deficit and rate caps may be any values satisfying

```
k_(i+1) >= 194*k_i
k_(i+1) >= 2*k_i + 2 + m
p_(i+1) >= 32768*k_i*p_i.
```

While all rate caps stay at most `1/4`, no coordinate separates the entire
rectangle. Induction on the remaining messages rules out a solving protocol.
Both parity classes initially have deficit one and bilateral density limits
at rate `4/n`; this saves the first mirror step.
The generalized bilateral theorem allows any initial deficit `k >= 1` and
limits with parameters `(p,k)`. After selecting the first message cell,
the remaining adversary starts with deficit at most `m+k`.

## Theorem 3 and explicit constants

For `d` messages, put `t = d-1`. The checked finite obstruction is

```
16 * (32768 * 194^t * (m+1))^t <= n.
```

Under this condition, no protocol with `card M <= 2^m` and `m >= 0` solves
the parity KW game. For every `d >= 2`, the asymptotic proof uses

```
C_d = 32768 * 194^(d-1)
epsilon_d = 1 / (32*C_d)
N_d = (32*C_d)^(d-1).
```

If `n >= N_d` and `m <= epsilon_d*n^(1/(d-1))`, the finite obstruction
applies. The public communication theorem quantifies over every finite
message alphabet, so its constant and threshold depend only on `d`.

The circuit translation is the circuit-to-protocol direction of the
[Karchmer--Wigderson correspondence](https://doi.org/10.1137/0403021), as
stated in Korten's Lemma 1. For each output of a depth-at-most-`d` circuit,
`Circuit.exists_roundProtocol` constructs a solving protocol with at most
`d` messages from an alphabet of size `totalFanIn`. Each gate chooses an
input edge; negated edges swap the players without adding a round.
Applying the communication theorem with cost
`epsilon_d*n^(1/(d-1))` rules out `totalFanIn <= 2^cost`.

The wire theorem uses `Circuit Basis.unboundedAndOr n 1 g`, with arbitrary
internal gate count `g` and free negation flags on gate inputs.
`totalFanIn` counts gate-input occurrences, including output gates, repeated
wires, and unused internal gates. The circuit model requires a nonzero
input count, which is automatic in the sufficiently-large-`n` regime.

The proof follows the paper's harmonic-mean, light-pattern, mirror-set,
and top-down adversary route. It does not invoke the existing
random-restriction parity lower bound. All statements are proved in Lean
without proof placeholders or additional axioms.

## Majority extension

The predicate is the existing `Complexity.majority`: an input is true exactly
when more than half its bits are true. Ties are false, and the theorems cover
both even and odd input lengths. The initialization uses

```
X = weightLayer n (n/2)
Y = weightLayer n (n/2 + 1)
K(n) = majorityDeficitBound n = 128 + log_2(2*(n+1)).
```

Both layers have at least `2^n/(2*(n+1))` elements for `n >= 2`: the middle
binomial coefficient is at least the average, and the next one is at least
half as large. Their entropy deficits are therefore logarithmic.

Every point of either layer has at least half its coordinates leading to the
other layer by a single-bit flip. Sampling coordinates independently at rate
`16/n` hits such a neighbor with probability at least `8/9`. The expected
mask size is `16`, so the chance it exceeds `128` is at most `1/8`. With
probability at least `55/72 >= 3/4`, the mask thus contains a valid flip and
has at most `128` coordinates. That one completion already gives fiber density
at least `2^(-128)`. This proves bilateral density limits with parameters
`(16/n,K(n))` for `n >= 16`.

| Extension | Lean declaration |
| --- | --- |
| Sparse density limit from many single-bit neighbors | `BooleanAnalysis.isDensityLimit_of_many_neighbors` |
| Logarithmic deficits of the majority layers | `BooleanAnalysis.majority_layers_deficit` |
| Bilateral majority initialization | `BooleanAnalysis.majority_layers_limits` |
| Finite protocol obstruction | `KarchmerWigderson.RoundProtocol.not_solves_majority_finite` |
| Communication lower bound | `KarchmerWigderson.majority_communication_lower_bound` |
| Wire lower bound | `Circuit.majority_wire_lower_bound` |

All names in this table are under `Complexity`. For `d >= 2` messages, put
`t = d-1` and `C_d = 32768*194^t`. The finite obstruction is

```
64 * (C_d * (m + K(n)))^t <= n.
```

The asymptotic proof takes `epsilon_d = 1/(128*C_d)` and uses the checked
fact that `K(n) = o(n^(1/t))`. For sufficiently large `n`, both the initial
deficit and any cost `m <= epsilon_d*n^(1/t)` fit the finite budget.
The threshold is proved to exist; this argument does not give a closed-form
numeric threshold. The resulting communication lower bound is
`Omega_d(n^(1/(d-1)))`, and the wire lower bound is
`2^(Omega_d(n^(1/(d-1))))` in the same circuit model as the parity theorem.

This extension uses Korten's harmonic-mean and mirror-set machinery with
the adjacent-layer initialization proved here. No claim of a new asymptotic
lower bound is made.

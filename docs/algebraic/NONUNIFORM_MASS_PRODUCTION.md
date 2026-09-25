# Nonuniform mass production: proof status

Both variants are fully proved. The explicit recursive theorem is
`BlockInduction.exponentialMassProduction`. The nonuniform route culminates in
`Nonuniform.realSharpMassProduction`, which proves the sharper coefficient
with the manuscript's real-rate and additive-error quantifiers.

The added modules prove, without new axioms or proof placeholders:

- An exact exponential collision bound, using a two-coloring of a spanning
  forest to justify conditional independence. Repeated targets are allowed.
- One fixed phase menu covering all occupied states and target tuples under
  `512 * capacity * |K| <= number of projective directions`.
- At most `capacity * (2 + 3 * addressBits)` candidate lines per menu and
  acceptance of exactly `ceil(active/2)` clean requests.
- A concrete shared propagation circuit costing exactly two charged gates
  per record, and record payload broadcast costing at most
  `records * (6 * keyWidth + 4)` per payload bit.
- A complete two-sort batched table lookup, including repeated queries,
  metadata preservation, and fixed output wires. For
  `T = 2^keyWidth + requests`, the charged cost is at most
  `256 * T * (ceil(log2 T) + keyWidth + valueWidth + 2)^5`.
- A complete candidate-selection circuit: sort requests by clean flags,
  sort whole candidate blocks by their success bit, and select a clean
  prefix from one successful candidate by fixed output wires.
- Computed-key sorting and exact collision marking, with preserved distinct
  identifiers returning every record and duplicate flag to its original
  position. Their bounds are linear in record count with polynomial width
  and sorting-depth factors.
- A duplicate-flag circuit that adds its own fixed ordering identifiers, and
  a shared batched OR circuit accepting repeated source keys, repeated
  queries, and absent keys. Their charged costs are bounded respectively by
  `256 * records * (depth + keyWidth + 1)^5` and
  `256 * (sources + queries + 1) * (depth + keyWidth + valueWidth + 2)^5`.
- An assembled enumerated-menu evaluator: shared occupancy lookup, point
  collisions within each candidate, aggregation into exact clean-request
  flags, and selection of one candidate's clean prefix. Request payloads
  survive as a permutation, and the complete circuit has an explicit bound
  linear in point count up to polynomial width and sorting-depth factors.
- A fixed-direction point generator using precomputed field offsets. Its
  `2^width` scalar slots represent precisely a punctured line after marking
  the zero scalar invalid, with at most one gate per output bit.
- A complete universal geometric phase circuit under the packing budget.
  One fixed power-of-two menu works for every encoded occupied state and
  target tuple; its successful-candidate premise is discharged by counting.
  It accepts the rounded-up half prefix, preserves original request data
  and complete line-point lists, and has an explicit total phase cost bound.
- A complete near-linear scheduler for power-of-two batches. Fixed wiring
  adds request identifiers, compacts each phase's accepted prefix, and
  preserves every original request exactly once. Iterating to the singleton
  phase yields disjoint recovery lines for all requests, even with repeated
  targets and payloads. `Nonuniform.Scheduler.existsCircuit` constructs one
  circuit that works for all encoded inputs under the direction budget.
  With `g` requests, `q = 2^width`, `a = dimension * width`,
  `D = ceil(log2 g)`, and tagged request width `W`, its charged cost is at most
  `g * q * 10000 * (D + 1) * (14 + 18*a) * (5*D + 4*a + 2*width + W + 10)^5`.
  The field-size factor occurs only once; the polynomial does not contain
  the full point-list width.
- Common-zero-block monomial line parity, independence of reduced monomial
  evaluations, and existence of a systematic information set of exact size
  `A^m - (A-1)^m` over `A^m` points. Here `A = 2^(dimension * blockWidth)`
  and the field width is `blockWidth * m`. This subsequence of field widths
  suffices for the intended asymptotic packing argument.
- A finite rate bound and packing bound with at most one codeword of
  rounding overhead, plus recovery of the original Boolean bit and
  injectivity of disjoint scheduled resource incidences.
- The complete scheduler/resource/recovery composition for requests supplied
  with encoded metadata. `Nonuniform.ScheduledRecovery.existsCircuit` scatters
  suffixes, evaluates each actual `(copy, point, basis bit)` function once,
  gathers point values, XORs each punctured line, and restores original
  request order using only identifiers and one-bit results. Invalid scalar
  slots contribute false. Its bound is the exact resource-bank cost plus
  explicit scheduler and routing overheads. Routing padding does not enlarge
  the leading bank-evaluation cost.
- The full finite Boolean mass-complexity theorem on raw prefix/suffix
  inputs, `Nonuniform.FiniteBound.booleanMassComplexity_le_explicit`. The
  shared lookup supplies all metadata; code existence, source-bit placement,
  canonical index widths, and synthesis of every resource function are
  discharged. Remaining hypotheses are numerical positivity, dimension,
  and projective-direction conditions. `LupanovRuntime.normalizedResourceBound`
  also supplies a uniform eventual resource bound of
  `floor((precision+1)*2^suffixWidth/(precision*suffixWidth))` for the parametric
  version of the finite theorem.

The menu construction, information set, and source-bit placement are
nonuniform choices made offline. Their existence is proved, not assumed.

The asymptotic modules choose all field/code/split parameters, bound the
runtime overhead by `2^prefixWidth` times a fixed degree-seven polynomial,
and absorb that overhead and the last partial codeword using exponential
slack. The leading resource bank preserves the rate-one constant.

`Nonuniform.sharpExponentialMassProduction` proves, for every natural
`u < v` and positive precision `P`, an eventual bound uniform over all
functions and positive `t <= 2^floor(u*n/v)`:

```text
P * (v-u) * n * booleanMassComplexity f t <= (P+1) * v * 2^n.
```

`Nonuniform.realSharpMassProduction` additionally proves, for every real
`0 <= gamma < 1` and `epsilon > 0`, a cutoff uniform over all functions and
positive integer `t <= 2^(gamma*n)`. It supplies a finite natural bound `B`
with `booleanMassComplexity f t <= B` and
`B <= (1/(1-gamma) + epsilon) * 2^n/n`. Rational approximation, integer
precision selection, and upward exponent rounding are machine checked.

The now-proved batched lookup can include code number, information point,
and bit selector together in its offline table. This avoids runtime division.

The standard De Morgan cost charges NOT, AND, and OR gates; constants,
structural identity, fan-out, and output designations are free. The formal
theorems prove circuit existence and gate cost. They make no efficient uniform
construction claim for the offline menus, information set, or placement.

Validation commands:

```sh
lake build Algebraic AlgebraicTests --wfail
lake test
lake lint
git diff --check
```

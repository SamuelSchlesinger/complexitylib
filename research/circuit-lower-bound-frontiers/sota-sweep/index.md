# A sweep for new lower bounds in other models (October 2026)

[Research index](../index.md)

This note records a parallel research sweep run on 6 October 2026. Each lane took one circuit
model or target that the rest of this corpus does not treat, pinned down the published state of
the art, and tried to beat it with an argument short enough to formalize. Every claimed result is
for an explicit family at every input length, not a single instance.

Status labels used below:

- **Lean** — formalized and checked in this repository (the declarations are named).
- **In progress** — a formalization is under way.
- **Paper** — a complete written proof checked on small cases by computer, not yet formalized.
- **Conjecture** — numerical or heuristic evidence only.
- **Barrier** — a proved limit of a method, not of circuits.

Prior-art statements were checked against primary sources where the lane could reach them;
novelty is still a judgment, and none of these results has had an expert literature review.
Several rely on the Gaussian layout coefficient `A = 2p ≈ 0.2807` of this corpus
(`κ = 1/A ≈ 3.5625`), which is where much of their gain comes from.

## Results

| Model and target | New bound | Previous best | Status |
| --- | --- | --- | --- |
| B2 (any fan-in-2 basis), correlation with an explicit quadratic-form family | `2^{-Ω(n)}` below `(1 + 1/(2A))n ≈ 2.781n` gates | `2.5n` ([Chen–Kabanets, COCOON 2015](https://www2.cs.sfu.ca/~kabanets/papers/linsize-COCOON.pdf)), `2.6n` non-explicit (Golovnev–Kulikov–Smal–Tamaki, MFCS 2016) | Lean: `Complexity.Correlation.eventually_correlation_hardForm_le` |
| De Morgan circuits with at most `k` gates of fan-out ≥ 2, parity | `n² ≤ (k+1)(size + k + 1)`, tight up to a constant | `L(f)/2^k` by unfolding | Lean: `Algebraic.KW.parity_sq_le_cost` and the `Sharing` modules |
| Arbitrary fan-in-2 gates over a finite field (B2 over GF(2)), `n×n` matrix product | `(2 + 1/(4κ_E) − ε)n² ≈ 3.78n²` | about `2n²` | Lean: `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_matMul`, `eventually_lt_size_matMul_zmod_two` |
| Arithmetic circuits, `n×n` matrix product (all operations) | `≈ 4.227n²` | about `3.5n²` (Bläser's `5/2·n²` multiplications plus the outputs) | Lean: `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_matMul_formal`, `eventually_lt_arithmeticCost_of_matMul` |
| Arithmetic circuits, product of two length-`n` polynomials | `≈ 5.5625n` | about `4n` (large fields), `5n` (small fields, Kaminski–Bshouty plus outputs) | Lean: `Algebraic.Cutwidth.MultiOutput.eventually_lt_size_of_polyMul` (any field, via the jet cut lemma `MultiOutput.Taylor`) |
| `(n, n/2)`-concentrators (edges) | `≈ 3.28n` (beats `2n − 2` once `m ≥ 0.22n`) | `2n − 2` (Pinsker, 1973) | Lean: `Algebraic.Cutwidth.Multigraph.Concentrator.eventually_le_card_edges_half` |
| Hyperconcentrators (edges / fan-in-2 nodes) | `≈ 3.78N` / `≈ 2.78N` | `2N` (implied) | Lean: `Algebraic.Cutwidth.Multigraph.Hyperconcentrator.eventually_le_card_edges` |
| Fan-in-2 linear circuits for the `N`-point DFT, any `N` (including the FFT matrix) | `≈ 2.78N` | none for composite `N` (Lokam 2009; [Ailon](https://arxiv.org/abs/1403.1307)) | Lean: `Algebraic.Cutwidth.MultiOutput.Linear.eventually_lt_size_fft` |
| `ε`-halver comparator networks | `(1 + κ(1−2ε)/2 − δ)n` | `n − 1` | Lean: `Algebraic.Cutwidth.ComparatorNetwork.eventually_le_size_of_isHalver` |
| Signed unbounded AND/OR/XOR, Gold map `x³` (odd `n`), all outputs | `≈ 1.7716n − 0.86` total gates; `(3n−3)/2` AND/OR gates | (new target; inversion `1.5659n` in the same model) | Lean: `Algebraic.Aggregate.Geometry.Gold.gateCoefficient_mul_sub_constantPenalty_le_size` |
| Unbounded-fan-in AND gates with XOR free, an explicit `(n,n)` map | `(3n−3)/2` (Gold), `2n − 1` (field multiplication, `2n` inputs) | rank bound `n` | Lean: `Gold.three_mul_input_le_two_mul_conjunctionCount_add_three`, `Algebraic.Aggregate.Geometry.FieldMul.two_mul_input_le_conjunctionCount_add_one` |
| Signed unbounded AND/OR/XOR, field inversion | `1.6954n − 1.11` (elementary), `1.7716n` with the Weil bound | `1.5659n` (this corpus) | Paper |
| `{AND, OR, NOT}` circuits with at most `t` NOT gates, Boolean matrix product | `n⌊n/2^t⌋²` AND gates | trivial | Lean: `Algebraic.Monotone.MatrixProduct.NegationLimited.mul_div_sq_le_andCost` |
| OR of `k`-CNFs (`Σ3^k`), affine or sumset dispersers (including this corpus's family) | `2^{(1/k − o(1))n}`; `2^{(μ_k/(k−1) − o(1))n}` with PPSZ trees (`2^{0.6137n}` at `k = 3`) | `2^{0.064n}` at `k = 3`, `2^{n/(10k)}` (Frankl–Gryaznov–Talebanfard, ITCS 2022) | Lean (`1/k` version, with sparsification): `Complexity.sourceReductionHardFamily_two_rpow_le_sigmaThreeSize`; PPSZ version Paper |
| Threshold circuits, arbitrary depth and weights | `(1/2 − o(1))n` gates; `n − o(n)` for few input-direction switches; `2^{n−o(n)}` levels for multilevel threshold representations | `n/4` for inner product (Gröger–Turán; Roychowdhury–Orlitsky–Siu 1994) | Lean: `Algebraic.Threshold.sourceReductionHardFamily_lt_inputGates` and its direction-run and multilevel variants |
| Linear (parity-query) branching programs, Gold map | `T·(S+1) ≥ n(n−4)/8` | (no multi-output result found) | Paper |

### Notes on individual results

- **Correlation.** The layout cut at the prefix that reads half the inputs splits the inputs
  into at most `2^{w+1}` rectangles on which the circuit is constant. Lindsey's lemma bounds the
  bias of a quadratic form on each rectangle by its cut rank. The family is a bilinear form whose
  `m × m` matrix has every square submatrix of rank at least its size minus `O(√m)`; such matrices
  exist by counting, and the lexicographically first one gives a family in `E^NP` (argued on paper
  only). A polynomial-time version needs explicit graphs of bisection cut rank `(1/2 − τ)n` with
  `τ < 0.06`; the best explicit construction found has rank about `n/105`.
- **Shared gates.** Each shared gate's formula contributes Khrapchenko rectangles on the pairs it
  separates; a downward cover argument routes every Hamming edge to a literal rectangle, and two
  Cauchy–Schwarz steps give the bound. Andreev-type and Nechiporuk-type formula measures decay
  like `2^{-k}` under sharing (tight examples exist), so edge counting is the measure that
  survives.
- **Matrix and polynomial multiplication.** A new jet (dual-number) cut lemma runs this corpus's
  cut-and-paste lemma over `L[s]/(s²)` and `L[s,t]/(s²,t²)`, bounding a cut by both Jacobian ranks
  and the Hessian cross rank of any output combination. Matrix multiplication then uses three
  vertex measures on the tripartite index graph and a heavy/light charging argument at a
  threshold prefix.
- **Networks.** A two-routing directed cut: one routing forces `h − b` edges out of a prefix and
  a different routing forces `b` edges into it, so the counts add. The DFT bound uses only that
  every `k × k` block of rows `0..k−1` is a nonsingular Vandermonde matrix.
- **Restriction–rank.** Killing conjunctions one affine equation at a time down to a flat of
  dimension `D(F)` leaves the outputs independent modulo affine functions, so a circuit has at
  least `m + n − D(F)` conjunctions, where `D(F) − 1` is the largest flat on which some nonzero
  output component is affine. For the Gold map this dimension is `(n+1)/2`, from the radical of its
  trace form.
- **Depth three.** In a sparse `k`-CNF, a solution with many non-isolated directions contains
  pairwise separated moves, hence a large subcube or affine flat; sparsification
  (Impagliazzo–Paturi–Zane) plus PPZ coding then bounds the solution sets of dispersers.

## Barriers and negative results

- **U2 past `5n`.** Controlling values let a cut carrying both `a` and `AND(a, ·)` realize only
  three patterns ("links"), and any layout coefficient below `1/4` for link-charged cuts would
  give a new U2 record. A tree-limit computation predicts about `5.09n` (Conjecture). But links are
  provably invisible to pairwise Gaussian certificates (the linear-programming optimum equals the
  baseline `0.2807`), vertex-local controlling-value savings are dominated by flipping a vertex
  across the cut, and forcing a gate and its argument to cross together costs more than it saves.
  A proof needs lower bounds on joint events of four to six Gaussian scores.
- **Single-cut correlation.** One cut of width at least `n/2` lets the circuit send all of one
  side's input, so `(1 + 1/(2A))n` is the limit of the single-cut correlation method.
- **Concentrators, hyperconcentrators, DFT, halvers.** For each object the forced cut width of
  these arguments is exactly the value used (for example `min(m, n−m)` for concentrators), so
  further gains need several cuts or semantic arguments.
- **Multiplicative complexity.** Degree arguments are capped at `n + m − 3`; every known
  single-output technique is capped at `n − 1`, and any proof of `MC ≥ n` must use at least six
  variables (every function on five variables has `MC ≤ n − 1`). Exact search finds
  `MC(GF(32) inversion) = 9`, above the `2n − 3` degree bound.
- **Depth three.** Large `k`-CNF solution sets need not contain linear-dimension affine flats
  (`b`-factors of high-girth regular bipartite graphs), which caps one route of
  Frankl–Gryaznov–Talebanfard.
- **Threshold circuits.** A fresh anti-diagonal gate costs any rectangle argument two bits, so
  the `n/2` barrier sits in circuits that switch input direction linearly often.
- **Negation-limited circuits.** Restricting to product sub-instances cannot lose less than a
  factor four per NOT gate. Separately, the `6n` and `8n` negation-limited bounds of
  Iwama–Morizumi–Tarui rest on Long's unpublished `4n` majority bound; without it they become
  `5.5n − O(log n)` and `7.5n − O(log n)`.
- **Planar and restricted superlinear models.** Semilective planar `Ω(n²)` and treewidth versions
  of Nechiporuk are known; for multilective planar circuits a single separator argument is capped
  near `2n log₂ n`, and subfunction counting gives at most `O(n)` for an indirect-access function
  with `4.2n`-gate planar circuits.

## The 3SUM algorithm: no transfer found

Alman and Vassilevska Williams ([arXiv:2610.06783](https://arxiv.org/abs/2610.06783), October 2026)
give truly subquadratic 3SUM and subcubic APSP through a thin, sparse matrix product: for an
`N × D` by `D × N` product with `D ≤ N^{1/18}` and a set `W` of at most `N²/√D` wanted entries,
`O(N²/D^{0.063})` operations. A lane read the paper for lower-bound ideas and found none:

- **Algorithms to lower bounds.** Splitting `n` variables into three blocks turns one integer
  quadratic into an exact-weight triangle problem with `2^{n/3}` vertices per part, so deciding
  whether a single degree-two threshold function is satisfiable takes `2^{(1−0.00057)n}` time
  (Paper; a short corollary, earlier savings were about `√n`). Every circuit class this reaches
  already has satisfiability algorithms and lower bounds (Limaye–Srinivasan–Srinivasan, MFCS 2025;
  Williams' ACC∘THR), and the open depth-two threshold targets need the top gate's value on every
  assignment rather than a count over a third block.
- **Sparse products.** Cut-rank methods, including the matrix-multiplication argument above, are
  capped by the number of inputs, which the outputs exceed polynomially in the thin regime; an
  `ω(|W|)` bound would give a superlinear bound for an explicit cubic polynomial by Baur–Strassen.
- **Sanity test.** For fixed `W` the algorithm is a bilinear circuit with coefficients in
  `{0, ±1}`, so any method proving `|W| · D^{0.44}` for sparse thin products in a model containing
  such circuits is unsound. Nothing in this corpus is refuted.

## Future work

Concrete next steps left open by this sweep, roughly in order of expected payoff.

- **Correlation in P.** The `2.781n` family is uniform only in `E^NP`. A polynomial-time version
  needs explicit graphs whose bisection cut rank is `(1/2 − τ)n` with `τ < 0.06` (equivalently,
  binary `[2m, m]` codes in which every `m` columns have rank `(1 − τ)m`); the best explicit
  construction known has rank about `n/105`. Beyond `2.781n` needs several cuts or bias bounds
  for rectangles of size between `2^{n/3}` and `2^{n/2}`.
- **U2 past `5n`.** Two routes were tried.
  - *Layouts.* Links need a lower bound on co-straddling (joint events of four to six Gaussian
    scores); merging each copy with one consumer and placing the block at its information median
    gives a deterministic `≈ 4.68n` only. A dichotomy (cyclic, correlated regions already have cheap
    cuts; tree-like regions admit tree-value link bounds) is unexplored.
  - *Gate elimination.* The right target property is a one-sided directional affine disperser
    (`f(x) ⊕ f(x+a)` not identically zero on any large affine flat): it is exactly the class on which
    the hypotheses of the Iwama–Lachish–Morizumi–Raz `5n − o(n)` proof survive affine
    substitutions, so Li–Zhong's explicit directional dispersers (CCC 2024) get `5n − o(n)`. The
    Amano–Tarui `5n + o(n)` barrier does not apply to such functions (their function is constant on
    an affine flat of codimension `O(n/log² n)`). Sumset dispersion alone does not imply the
    hypothesis (a sumset disperser may ignore a variable). A *parity link* (a variable fed with an
    affine node into an XOR gadget whose output feeds another) allows a substitution removing six
    gates, so circuits built from XOR chains, like Amano–Tarui's, need about `5.5n` for these
    functions (Paper). What remains is one local configuration — a degree-three variable whose
    killed gates' successors pass constants through — where every single affine substitution removes
    at most five gates nearby; a proof of `(5 + δ)n` must exclude circuits dominated by it
    semantically (Conjecture: a gadget dichotomy). No function-level barrier is known: one would need
    a linear-size directional disperser of sublinear dimension, which Golovnev–Hirsch–Knop–Kulikov
    list as open.
- **Matrix and polynomial multiplication.** For arithmetic matrix multiplication, the full jet
  measure (Jacobian plus restricted Hessian rank) appears to reach `(1 − o(1))n²` on every chain
  tried, which would give the `5.5625n²` ceiling of cut methods (Conjecture); an arbitrary-gate
  analogue of the Jacobian bounds over finite fields is open. For polynomial multiplication the full
  measure gives `1.5n` on the degree chain, suggesting about `7.3n` (Conjecture).
- **Depth three.** The PPSZ-level bound `2^{(μ_k/(k−1) − o(1))n}` for dispersers needs localized
  critical-clause trees and resolution closure; unbounded bottom fan-in remains open.
- **Inversion and power maps.** The elementary fourth-moment route gives `1.6954n` for inversion in
  the signed model; the Weil bound gives `1.7716n`; Ben-Sasson–Kopparty's subspace-polynomial
  dispersers would give `1.8477n` for `x^{15}`; the Gold map's `n(n−4)/8` time–space tradeoff for
  linear branching programs is unformalized.
- **Multiplicative complexity.** If `MC(y·f) = MC(f) + 1` for the six-variable functions of
  multiplicative complexity six, then an explicit family has `MC ≥ n`, beating `n − 1`. Exact
  search gives `MC(GF(32) inversion) = 9`, above `2n − 3`.
- **Threshold circuits.** Conjecture: with `t` input directions interleaved arbitrarily, at least
  `n − 2k − O(t log t)` input-reading gates; it would interpolate between the `n/2` and `n` bounds.
- **Shared gates.** The B2 version with `r` XOR gates (factor `1 + k + 2r`) is proved on paper.
- **Negation-limited circuits.** Conjecture: `t` NOT gates save only `Θ(2^t n)` AND gates for
  Boolean matrix product; restriction methods are capped at a factor four per NOT gate.
- **Parked work.** A formula-restriction calculus and Subbotovskaya's shrinkage step (toward
  Andreev's `n^{5/2−o(1)}`) sit on the local branch `wip/shrinkage`. The MOD3 freezing tradeoff of
  the [MOD3 note](../larger-gates/mod3-barrier.md) needs a `GF(4)` analogue of the Razborov–Smolensky
  counting that is now formalized over `ZMod 3`.

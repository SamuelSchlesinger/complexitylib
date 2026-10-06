# The formal toolkit and its exact MCSP contract

[Back to the research plan](../index.md)

At commit `b030149cd09f755bfead55f473d670f0880eedb0`, the MCSP-specific circuit
development proves essentiality, an `N - 1` gate lower bound, exact-cost
repetition/equality, and communication, formula, and bounded-sharing inequalities.
The stronger explicit hard-family results are separate theorems with separate
semantic premises. This inventory records the statements and conventions; it
does not claim a new MCSP lower bound or priority. [complexitylib26][complexitylib26]

Throughout, `n` is the arity of the represented Boolean function, `N = 2^n`
is the number of bits supplied to the outer MCSP function, and `s` is an
inner complexity threshold. Write `C_D` for De Morgan binary-cost complexity,
`C_B` for full-binary gate complexity, and `C_A` for canonical
`Basis.andOr2` size. These are distinct measures.

## Three inner circuit conventions

| Convention and exact definition | Charged operations | Wires, outputs, and boundary cases |
|---|---|---|
| [`Algebraic.Binary.signature`](../../../Complexitylib/Algebraic/Basis/Binary.lean#L33), with `Circuit.gateComplexity` | Every gate costs one; all 16 binary Boolean operations are available. | Both input slots may use the same wire; fanout is unrestricted; outputs are free wire selections. A positive literal can have size zero. |
| [`Algebraic.DeMorgan.binaryCost`](../../../Complexitylib/Algebraic/Basis/DeMorgan.lean#L72), with `Circuit.costComplexity` | AND and OR cost one; constants, identity, and NOT cost zero. | Free output wires; constants and literals have cost zero. This is not `DeMorgan.standardCost`, which also charges NOT. |
| [`Complexity.Basis.andOr2`](../../../Complexitylib/Circuits/AndOrNot/Defs.lean#L73), with `Circuit.sizeComplexity` | Every AND/OR gate has exactly two arguments, with free input-negation flags. | Typed circuits count internal and output gates: size `G + M`, hence `G + 1` for one output. Primary inputs are free; outputs must be gates. Positive arity is required by the circuit type. |

The algebraic model reuses `Cslib.Circuits.Circuit`; its minimum costs live
in extended naturals, allowing infinity for an unrealizable target. The typed
`Complexity.Circuit` has a different interface and output convention.
The canonical MCSP wrapper assigns both zero-arity functions size zero;
at positive arity, its minimum is positive.
[Definitions](../../../Complexitylib/Metacomplexity/MCSP/Defs.lean),
[typed size](../../../Complexitylib/Circuits/Typed/Defs.lean#L171), and
[minimum-size interface](../../../Complexitylib/Circuits/Basic.lean) make these
choices explicit. [complexitylib26][complexitylib26]

There are useful checked translations, but they should be named precisely.
[`Complexity.Circuit.eval_toStraightLine`](../../../Complexitylib/Circuits/StraightLine.lean#L154)
and [`size_toStraightLine`](../../../Complexitylib/Circuits/StraightLine.lean#L166)
preserve semantics and size over the basis's own CSLib signature.
[`Complexity.SchnorrDeMorgan.translate`](../../../Complexitylib/Circuits/Internal/SchnorrDeMorgan.lean#L64)
then translates an `andOr2` program to the algebraic De Morgan basis,
preserving every source wire and making binary cost equal the source gate
count (`Translation.trace_eq`, `Translation.cost_eq`). These are sufficient
to transport suitable lower bounds on a fixed target in that direction.
They do not identify the two minimum-size functions or their exact-cost
layers: free wire outputs and constants remain different conventions.
[complexitylib26][complexitylib26]

## Fixed functions, raw languages, and encoded languages

| Exact interface / local declaration | Inner basis and cost | Outer object and semantics |
|---|---|---|
| [`Algebraic.MCSP.mcspScalar`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Defs.lean#L313), `mcspTarget` | Arbitrary interpretation; unit gate count | A single Boolean function on `N` table bits at fixed `n,s`: accepts iff the represented target has gate complexity at most `s`. No arity or threshold bits are input. |
| [`Algebraic.MCSP.mcspCostScalar`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Defs.lean#L342), `mcspCostTarget` | Arbitrary interpretation and operation cost | Same fixed-length outer object, with the chosen cost instead of unit gate count. The repetition results instantiate `C_D`. |
| [`Complexity.MCSP.mem_encode_iff_sizeComplexity_le`](../../../Complexitylib/Metacomplexity/MCSP.lean#L184) | `C_A`, for `n > 0` | Total language of canonical codes `(n,s,T)`; membership iff `C_A(T) ≤ s`. Malformed strings are rejected. |
| [`Complexity.MCSP.mem_atThreshold_encode_iff`](../../../Complexitylib/Metacomplexity/MCSP/Threshold.lean#L65) | `C_A` | Encoded slice for a function `s(n)`; membership additionally requires the stored threshold to equal `s(n)`. |
| [`Complexity.MCSP.mem_rawAtThreshold_tableBits_iff`](../../../Complexitylib/Metacomplexity/MCSP/Raw.lean#L96) | `C_A`, with the total zero-arity convention | Bare truth-table language with external threshold `s(n)`. Valid inputs have length exactly `2^n`; no metadata is present. |
| [`Complexity.GapMCSP.rawSliceProblem`](../../../Complexitylib/Metacomplexity/MCSP/Raw.lean#L152) | `C_A` | Promise problem: YES if `C_A(T) ≤ s_yes(n)`, NO if `s_no(n) < C_A(T)`; the middle region is outside the promise. Non-power-of-two lengths are outside both sides. |

The algebraic indexing is big-endian: input coordinate zero selects the first
or second half of the table. Canonical `MCSP.Instance.inputIndex` is
little-endian: variable `j` is bit `j` of the index. The convention is stated
in the [algebraic definitions](../../../Complexitylib/Algebraic/LowerBound/MCSP/Defs.lean#L39).
An exact comparison must account for this coordinate permutation as well as
the cost model. [complexitylib26][complexitylib26]

[`Complexity.MCSP.Instance.length_encode`](../../../Complexitylib/Metacomplexity/MCSP.lean#L114)
gives the exact encoded input length
`N + 2 * bitlength(n) + 2 * bitlength(s) + 4`.
Thus a theorem measured in raw length `N` is not literally a theorem measured
in encoded length. The raw/canonical maps have checked round trips and
promise-side preservation
([`rawSliceProblem_mapReducesVia_rawToCanonical`](../../../Complexitylib/Metacomplexity/MCSP/Raw.lean#L180)
and [`sliceProblem_mapReducesVia_canonicalToRaw`](../../../Complexitylib/Metacomplexity/MCSP/Raw.lean#L189)).
Their contracts are semantic `MapReducesVia` statements; polynomial-time
machine realizations are explicitly left separate. [complexitylib26][complexitylib26]

The canonical layer also supplies executable witness checking, threshold
normalization, and a polynomially balanced characterizing witness relation
([`rawWitnessRelation_polyBalanced`](../../../Complexitylib/Metacomplexity/MCSP/Normalization.lean#L94),
[`mem_MCSP_iff_exists_rawWitnessRelation`](../../../Complexitylib/Metacomplexity/MCSP/Normalization.lean#L100)).
The [blueprint](../../../blueprint/src/chapters/metacomplexity.tex#L478)
still lists the machine-level `MCSP ∈ NP` theorem as planned; finite semantic
verification alone is not that theorem. [complexitylib26][complexitylib26]

## What symmetry already proves

XOR translation of the represented input permutes truth-table coordinates
transitively. De Morgan input negations have zero binary cost, so `C_D`
is exactly invariant. For the full-binary model, the proved threshold
invariance requires `s ≥ 1`: a free output input wire may need one gate
after negation. This distinction matters at threshold zero.
[complexitylib26][complexitylib26]

| Exact declaration, in namespace `Algebraic.MCSP` | Inner predicate | Outer model and hypotheses | Conclusion in `N = 2^n` |
|---|---|---|---|
| [`costComplexity_deMorgan_xorTranslate`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Symmetry.lean#L188) | `C_D` | Any target and any input XOR mask | Translated target has the same `C_D`. |
| [`mcspScalar_binary_comp_tableTranslate`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Symmetry.lean#L313) | `C_B ≤ s` | `s ≥ 1` | The threshold predicate is invariant under every such table permutation. |
| [`mcspCostScalar_deMorgan_essentialAt`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Symmetry.lean#L422) | `C_D ≤ s` | Two table inputs have different answers | Every one of the `N` coordinates is essential. |
| [`mcspScalar_binary_essentialAt`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Symmetry.lean#L483) | `C_B ≤ s` | `s ≥ 1`, and two inputs have different answers | Every one of the `N` coordinates is essential. |
| [`mcspCostTarget_deMorgan_size_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Symmetry.lean#L466) | `C_D ≤ s` | Any Boolean outer basis, fan-in at most two, exact computation; predicate nonconstant | `N ≤ outer.size + 1`. |
| [`mcspTarget_binary_size_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Symmetry.lean#L509) | `C_B ≤ s` | Same outer model; `s ≥ 1`; predicate nonconstant | `outer.size ≥ N - 1`. |
| [`mcspCostTarget_deMorgan_binaryCost_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Symmetry.lean#L449) | `C_D ≤ s` | Outer De Morgan circuit with free NOT/constants; predicate nonconstant | `outer.binaryCost ≥ N - 1`. |

The nonconstancy assumption is substantive. For example, the canonical
[`Complexity.MCSP.shannon_threshold_window`](../../../Complexitylib/Metacomplexity/MCSP/Shannon.lean#L77)
states that for `n ≥ 16` some table is rejected at `floor(N/(5n))`, while
every table is accepted at `floor(18N/n)`; the lower statement already holds
for `n ≥ 6`. This is an inner-complexity existence/saturation result, not
an outer decision lower bound or an exact-cost-layer counting theorem.
[complexitylib26][complexitylib26]

The algebraic [`card_yesSet_le_orderedBudget`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Defs.lean#L451)
and [`card_yesSet_le_sharpBudget`](../../../Complexitylib/Algebraic/LowerBound/MCSP/Defs.lean#L458)
bound gate-count YES sets for finite operation alphabets. The latter uses
the sharper circuit-counting budget. Neither declaration counts the
zero-cost-gate `costYesSet` or supplies a lower bound on `exactCostSet`.

## Exact-cost repetition and its consequences

For this section, let `n = m + 1`, so each half-table has `N/2 = 2^m`
entries. Write `E[m,s] = {T : C_D(T) = s}`. This reindexes the source
theorems' parameter `n` as `m`, keeping `n` here equal to the final
represented arity. Every outer predicate below is `M_D[n,s]`.

[`costComplexity_muxTarget_self`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L164)
proves `C_D(mux(u,u)) = C_D(u)`.
[`costComplexity_muxTarget_ge_add_one`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L303)
proves that when `u != v` and at least one has positive cost,
`C_D(mux(u,v)) ≥ C_D(u)+1` and `≥ C_D(v)+1`.
The proof finds an influential AND/OR gate and deletes at least one charged
gate on either restriction of the selector. Free NOT/identity chains and
constant outputs are treated explicitly. [complexitylib26][complexitylib26]

Consequently, for **an attained exact threshold** `T ∈ E[m,s]`, `s ≥ 1`,
`M_D[n,s](T',T) = 1` iff `T' = T`, and likewise for `(T,T')`.
The other half `T'` is arbitrary, not restricted to `E[m,s]`.
These are [`mcspCostScalar_pairTruthTable_left_eq_true_iff`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L322)
and [`mcspCostScalar_pairTruthTable_right_eq_true_iff`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L351).
Replacing `C_D(T) = s` with `C_D(T) ≤ s` would lose the strict rejection
step. No full-binary or canonical exact-threshold analogue is asserted by
these declarations. [complexitylib26][complexitylib26]

| Exact declaration, in namespace `Algebraic.MCSP` | Additional hypotheses | Outer model and checked conclusion |
|---|---|---|
| [`sensitiveCoordinates_mcsp_pairTruthTable_eq_univ`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L516) | `s ≥ 1`, `T ∈ E[m,s]` | At the accepted input `(T,T)`, every one of the `N` single-bit changes is rejected. |
| [`khrapchenkoBound_mcsp_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L544) | Same exact-cost witness; `KW.KhrapchenkoBound M_D B` | `N ≤ B`. The proof uses one accepted diagonal input and its `N` neighbors. |
| [`mcsp_formula_leaves_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L593) | Same witness; formula computes the predicate | De Morgan `KW.Formula`: at least `N` leaves, counting literals and constants. |
| [`mcsp_sharedGateCount_cost_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L605) | Same witness; `sharedGateCount c ≤ k`; circuit computes the predicate | De Morgan outer circuit: `N ≤ (k+1) * (outer.binaryCost + k+1)`. |
| [`mcsp_singleCut_card_exactCostSet_le`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L398) | `s ≥ 1`; exact computation; cut contains every left-half input and no right-half input | Arbitrary Boolean outer basis: `card(E[m,s]) ≤ 2^(forwardSignals + backwardSignals)`. No fan-in assumption. |
| [`mcsp_card_image_restrictTo_le_subfunctions_leftBlock`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L662) | `s ≥ 1`; any half-table coordinate set `Y` | The number of distinct restrictions `restrict(T,Y)`, `T ∈ E[m,s]`, is at most the number of outer subfunctions on the left copy of `Y`. |
| [`mcsp_binaryFormula_leavesIn_leftBlock_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L766) | `s ≥ 1`; full-binary formula `F` computes the predicate | `card({restrict(T,Y) : T ∈ E[m,s]}) ≤ 2 * 16^(F.leavesIn(leftBlock Y))`. |
| [`mcsp_binaryFormula_leavesIn_leftHalf_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/SubcubeRepetition.lean#L786) | `s ≥ 1`; full-binary formula `F` computes the predicate | `card(E[m,s]) ≤ 2 * 16^(F.leavesIn(leftHalf))`. |

Here [`KW.sharedGateCount`](../../../Complexitylib/Algebraic/LowerBound/KarchmerWigderson/Sharing/Circuit.lean#L68)
counts gates of fanout at least two, including repeated argument slots and
designated-output uses. It does not count primary inputs. The sharing
inequality therefore carries a real restriction on the outer circuit;
its displayed MCSP bound is linear in `N`, not the quadratic sensitivity
bound available for other targets such as parity.

The communication theorem counts distinct crossing **wire signals**, once
per wire, in both directions. Equality on the exact-cost layer makes boundary
keys injective on accepted diagonal inputs. For a nonempty layer this gives a
single-cut lower bound of `log2 |E[m,s]|`; the theorem neither sums across
cuts nor supplies the size of that layer. The subfunction inequalities
likewise leave their projection cardinalities explicit.
[complexitylib26][complexitylib26]

Non-vacuity is instantiated at cost one:
[`exactCostSet_deMorgan_one_nonempty`](../../../Complexitylib/Algebraic/LowerBound/MCSP/NonVacuity.lean#L117)
uses the conjunction of two variables, with any number of unused variables.
Thus for final represented arity `n ≥ 3`, threshold `s = 1` has unconditional
`N - 1` outer gate/binary-cost bounds and an `N`-leaf De Morgan formula bound
([`mcspCostTarget_deMorgan_one_size_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/NonVacuity.lean#L207),
[`mcsp_one_formula_leaves_lower_bound`](../../../Complexitylib/Algebraic/LowerBound/MCSP/NonVacuity.lean#L219)).
The general statements retain their supplied exact-cost witness. A
[new repeated-anchor companion](../data/RepeatedAnchor.lean), developed in
this research task after the snapshot, extends repetition to several selectors;
its argument and implications belong to the [directions section](../directions/index.md).

## Stronger hard-family results have different premises

[`Complexity.Frontier.lowerBound_gaussian`](../../../Complexitylib/Circuits/Frontier/Main.lean#L47)
applies to sets `S_N` of accepted outer inputs when, eventually:

- every rectangle contained in `S_N`, across **every** coordinate partition,
  has at least one side smaller than `K(N)` (`Frontier.RectangleFree`);
- `log K(N) = o(N)`;
- `N log 2 - log |S_N| = o(N)`.

It yields more than `(L - epsilon)N` positive-arity gates for every Boolean
basis of fan-in at most two, where
`L = 1 + pi / (3 arccos((1 + 2 sqrt(2))/4))`, approximately `4.5625`.
Nullary constants are free in `innerSize`; unary gates are counted.
The generic [`Frontier.lowerBound`](../../../Complexitylib/Circuits/Frontier/LowerBound.lean#L201)
retains the graph-layout premise `LayoutBound (r+1) A` and yields
`(r-1) * innerSize > (1 + 1/A - epsilon)N` for fan-in `r ≥ 2`.
[complexitylib26][complexitylib26]

[`Complexity.Frontier.sourceReductionHardFamily_lt_innerSize_gaussian`](../../../Complexitylib/Circuits/Frontier/Explicit.lean#L114)
discharges those semantic premises for the particular
`Algebraic.Cutwidth.Extractor.sourceReductionHardFamily`.
The [full-binary theorem](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Extractor/SourceReduction/Construction/Hardness.lean#L69)
also states its bound directly in gate size. Neither identifies that family
with MCSP, supplies an MCSP restriction/reduction from it, or instantiates
the rectangle and density hypotheses for MCSP. The
[roadmap](../../../ROADMAP.md#L354) discusses the coefficient and preserved
`log K = o(N)` condition; its stronger coefficient is not an MCSP theorem.

## The magnification formalization boundary

The selected canonical-basis **gap** interface has checked parameters
`s_yes(n) = floor(2^floor(beta*n)/(c*n))`,
`s_no(n) = 2^floor(beta*n)`, and outer circuit bound
`2^(n + ceil(epsilon*n))` at raw input length `N = 2^n`.
[`HasMagnificationLowerBoundHypothesis`](../../../Complexitylib/Metacomplexity/MCSP/Magnification/Frontier/Defs.lean#L60)
fixes `c`, then asks for one positive rational `epsilon` working for every
sufficiently small positive rational `beta`; each resulting problem is
outside `PromiseEventuallySIZE` at that bound. The quantifiers over `beta`
and input length are separate. This defines the antecedent; it does not
prove it. [complexitylib26][complexitylib26]

[`hasGenerators_of_hasApproximateCounterFamilies`](../../../Complexitylib/Metacomplexity/MCSP/Magnification/AntiChecker/Generator/Assembly.lean#L61)
is checked circuit assembly from approximate-counter families to anti-checker
generators. The [blueprint's magnification section](../../../blueprint/src/chapters/metacomplexity.tex#L582)
marks the full consequence `NP` not contained in `P/poly` as planned.
Remaining steps include the quantitative occupancy-query/counter construction
under `NP ⊆ P/poly`, the machine-level succinct verifier, and solver assembly.
These gap parameters cannot be substituted for the exact `C_D` repetition
predicate. Literature comparison belongs in the [literature section](../literature/index.md).

## Verification performed for this inventory

Source declarations, their load-bearing model definitions, the relevant
blueprint nodes, and `ROADMAP.md` were inspected at the recorded commit.
The [inventory script](data/check_inventory.py) runs a temporary Lean probe
against existing build artifacts, checking selected names and printing the
axioms of representative theorems; its [compiler output](data/check-output.txt)
records 32 successful declaration checks and nine reports using only
`propext`, `Classical.choice`, and `Quot.sound`. This is not a rebuild, a proof
of artifact freshness, or a run of the repository's full build/lint gates.
No production Lean file was changed by this audit.

[complexitylib26]: ../sources.md#complexitylib26

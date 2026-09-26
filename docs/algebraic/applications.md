# Applying the library

Choose a focused import for the result you need. `Algebraic` and
`Algebraic.Applications` are umbrellas and include substantial lower-bound
developments. `Algebraic.Core` contains the generic circuit operations without
the concrete bases or research developments.

## Entry points and mathematical models

| Task | Import | Endpoint and scope |
| --- | --- | --- |
| Compose or translate shared circuits | `Algebraic.Core` | `Circuit.comp`, `Circuit.parallel`, `Translation.compile_eval`, `Translation.compile_cost`; arbitrary signatures and interpretations, multiple free output wires |
| Represent a Boolean function | `Algebraic.Basis.DeMorgan.Completeness` | `DeMorgan.Expression.ofFunction`, `DeMorgan.functionallyComplete`; elementary truth-table synthesis, including zero inputs and zero outputs |
| Compare nearby Boolean functions | `Algebraic.Basis.DeMorgan.Complexity` | `DeMorgan.complexity_dist_le`; minimum internal gate count changes by at most `2*n` per changed truth-table entry |
| Fix a Boolean input | `Algebraic.Basis.DeMorgan.CircuitRestriction` | `DeMorgan.restrictCircuit`; exact semantics and binary-cost saving, with deleted gates indexed in the original source program |
| Binary exponentiation | `Algebraic.Basis.Arithmetic.Power` | `Arithmetic.Power.binaryPowerCircuit`; explicit circuit with separate addition and multiplication cost theorems |
| Parity in binary De Morgan circuits | `Algebraic.LowerBound.GateElimination.DeMorganXor` | `DeMorgan.xor_lowerBound`; at least `3*(n-1)` AND/OR gates, with negations and constants free |
| Parity versus AC0 | `Algebraic.LowerBound.AC0.ParitySeparation` | `AC0.parity_not_raw_computable`; shared unbounded-fan-in circuits, polynomial connective count, bounded logical depth, arbitrary internal NOT gates |
| `(4 - ε) n` gates over the full binary basis | `Algebraic.LowerBound.Cutwidth` | `Cutwidth.eventually_lt_size_of_pathwidthBound`; rectangle-free functions with polynomial threshold and `2 ^ (n - 2)` accepting inputs, assuming the `(1/6 + ξ) h` pathwidth bound for simple cubic graphs; see the [cutwidth guide](cutwidth-lower-bound.md) |
| `Ω(n² / log n)` formula leaves over the full binary basis | `Algebraic.LowerBound.Nechiporuk` | `Nechiporuk.eventually_sq_le_leaves`; rectangle-free functions with polynomial threshold and `2 ^ (n - 2)` accepting inputs, no graph-theoretic hypothesis; see the [Nechiporuk guide](nechiporuk-lower-bound.md) |
| Formula depth as communication complexity | `Algebraic.LowerBound.KarchmerWigderson` | `KW.formulaDepth_eq_protocolDepth`, `KW.formulaSize_eq_protocolSize`; De Morgan formulas and Karchmer–Wigderson protocols, composition bounds, and the KRW conjecture in depth and size forms (`KW.KRWDepth`, `KW.KRWSize`: some constant slack works for all non-constant `f` and `g`) as unproved propositions; see the [Karchmer–Wigderson guide](karchmer-wigderson.md) |
| Monotone Boolean CLIQUE | `Algebraic.LowerBound.Monotone.Clique.Exponential` | `Monotone.Clique.Exponential.powSelf_lt_circuitSize`; more than `w^w` gates for `w^4`-CLIQUE on `w^20` vertices when `w ≥ 16`, in the binary constant-free AND/OR basis |
| Hessian multiplication bound | `Algebraic.Applications.Hessian` | `Applications.hessianRank_lowerBound`; natural Hessian rank divided by two and rounded up, for formal polynomials over a field |
| Squarefree monomial as a sum of powers | `Algebraic.Applications.Waring` | `Applications.waringSum_lowerBound`; at least `choose (2*n) n` scaled powers of linear forms over a characteristic-zero field |
| Boolean mass production | `Algebraic.MassProduction.Nonuniform.RealTheorem` | `MassProduction.Nonuniform.realSharpMassProduction`; nonuniform circuit existence in the stated exponential copy range, charged with `DeMorgan.standardCost` |

The AC0 development has a separate [theory map](ac0-theory-map.md). The
[hierarchy guide](circuit-hierarchy.md) explains the truth-table interpolation
argument and its asymptotic endpoints.

## Cost conventions

All circuits have free fan-out and designated output wires. The number of
input coordinates and the number of outputs do not add to internal gate count.

| Expression | What it charges |
| --- | --- |
| `circuit.size` or `circuit.cost OperationCost.unit` | Every internal gate, including constants and identities when present in the basis |
| `DeMorgan.complexity f` | Minimum internal gate count for `f`, using the convention above |
| `circuit.cost DeMorgan.standardCost` | NOT, AND, OR; constants and identities are free |
| `circuit.cost DeMorgan.binaryCost` | AND and OR only |
| `circuit.cost Arithmetic.gateCost` | Addition and multiplication; named constants are free |
| `circuit.cost Arithmetic.multiplicationCost` | Every multiplication, including scalar multiplication; additions and named constants are free |
| `circuit.cost SumOfTerms.termCost` | Dictionary-term gates; additions are free |

The word `standardCost` refers to the local mass-production convention. It is
not CSLib's Boolean total gate count. `DeMorgan.withSharedConstants` compiles
a circuit with exactly `standardCost + 2` internal gates, and
`DeMorgan.complexity_le_standardCost_add_two` transfers the resulting bound
to the natural minimum. The two extra gates are shared false and true constants.

General `Circuit.gateComplexity` and `Circuit.costComplexity` take values in
extended naturals: an unrepresentable target has value `⊤`. De Morgan scalar
complexity is natural-valued because elementary completeness proves that every
Boolean function is representable. None of these minimum witnesses is an
efficient executable circuit optimizer.

## Checked examples

The regression files linked in this section are in the standalone
[algebraic-circuits repository](https://github.com/SamuelSchlesinger/algebraic-circuits),
where they were checked; they were not imported into Complexitylib, and
Complexitylib's build does not compile them or the snippets on this page. The
declarations they exercise are part of Complexitylib and are covered by its
build, linters, and axiom audit.

### Elementary synthesis

```lean
import Complexitylib.Algebraic.Basis.DeMorgan.Completeness

open Algebraic Algebraic.DeMorgan

example (input : Fin 2 → Bool) :
    (Expression.ofFunction (fun values : Fin 2 → Bool =>
      Bool.xor (values 0) (values 1))).eval input =
        Bool.xor (input 0) (input 1) := by
  simp
```

The [completeness regressions](https://github.com/SamuelSchlesinger/algebraic-circuits/blob/main/AlgebraicTests/Completeness.lean) also check
zero-input and zero-output targets. The module imports only
`Algebraic.Basis.DeMorgan.Expression` and `Algebraic.Semantics`, and its
transitive imports contain no minimum-complexity, lower-bound, or synthesis
module. The standalone repository's import checker enforced that boundary; it
was not imported, so in Complexitylib the boundary is not mechanically guarded.

### Translating away gates

The [Core-only translation example](https://github.com/SamuelSchlesinger/algebraic-circuits/blob/main/AlgebraicTests/CoreTranslation.lean)
constructs a two-gate unary circuit with two outputs: one original input and
the final gate. A translation replaces each unary gate by an identity wire.
The resulting circuit has zero gates, zero weighted cost for every operation
cost, and both original outputs. The same file checks semantics and costs of
compiling parallel circuits, importing only `Algebraic.Core`.

### Restricting an input

`DeMorgan.restrictCircuit circuit selected value` returns a circuit on the
remaining inputs and an exact cost certificate:

```text
deleted.card + result.cost binaryCost = circuit.cost binaryCost.
```

The deletion set contains indices of actual source gates. A residual output
that is already a wire is reused; a constant or negated wire may need one
additional gate, free under `binaryCost`. The
[restriction regressions](https://github.com/SamuelSchlesinger/algebraic-circuits/blob/main/AlgebraicTests/Restriction.lean) check these cases,
zero remaining inputs, and an output preceding unused gates.

### Hessian rank

The premise of `Applications.hessianRank_lowerBound` is

```lean
circuit.eval (Arithmetic.interpretation (MvPolynomial.C ∘ constant))
  MvPolynomial.X 0 = polynomial
```

The conclusion is the natural rank of the Hessian matrix at the supplied
point, divided by two and rounded up, bounded by multiplication cost. The
[Hessian example](https://github.com/SamuelSchlesinger/algebraic-circuits/blob/main/AlgebraicTests/Hessian.lean) computes the matrix
`[[0, 1], [1, 0]]` for `X₀ * X₁` and proves that a rational circuit computing
it needs at least one multiplication.

This premise is equality of formal polynomials. Agreement as functions on a
finite field is insufficient. The theorem permits cancellation and arbitrary
field constants; it does not assume monotonicity.

### Sums of powers

`Applications.waringSum_lowerBound` takes a finite set of term indices,
scalars, coefficient vectors, and a polynomial equality of the form

```text
sum_i scale_i * (sum_j coefficient_ij * X_j)^(2*n) = product_j X_j.
```

It returns `choose (2*n) n ≤ number of terms`. The
[Waring examples](https://github.com/SamuelSchlesinger/algebraic-circuits/blob/main/AlgebraicTests/Waring.lean) derive the four-variable
bound of six terms and check the zero-variable boundary. No circuit encoding
appears in their premises. The underlying method is the catalecticant rank
bound; see the [source module](../../Complexitylib/Algebraic/LowerBound/Fusion/SumOfTerms/Waring.lean)
for references and the precise correspondence. This is a restricted power-term
bound, not a bound on unrestricted multiplication count or a claim of exact
Waring rank.

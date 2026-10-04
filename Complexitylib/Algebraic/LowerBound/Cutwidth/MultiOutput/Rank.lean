/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Complexitylib.Algebraic.Circuit
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Rank.Internal

/-!
# The rank-cut bound

Split the wires of a multi-output circuit into `S` and its complement `T`, with forward signals
`A = forward c.program S` and backward signals `B = backward c.program S`. Let `X_S` and `X_T`
be the inputs placed in `S` and in `T`, and `Y_S` and `Y_T` the outputs whose wires lie in `S`
and in `T` (`outputsIn`); an output carried by an input wire is placed with that wire.

**The rank-cut bound** (`blockRank_add_blockRank_le`). If a circuit with values in a finite
field `F`, with any gates, computes the linear map `x ↦ M x`, then for every split
`rank M[Y_T, X_S] + rank M[Y_S, X_T] ≤ |A| + |B|`.

The proof uses the product fibres of `SingleCut`. The inputs with a fixed boundary key form a
product `L × R` of left and right parts. On such a fibre the outputs carried in `T` depend only
on the right part, so the left parts lie in a coset of the kernel of `M[Y_T, X_S]` and number at
most `|F| ^ (|X_S| - rank M[Y_T, X_S])`; symmetrically for the right parts. Since there are at
most `|F| ^ (|A| + |B|)` keys, `|F| ^ n ≤ |F| ^ (|A| + |B|) |F| ^ (n - r₁ - r₂)`.

The counting step holds for every function and every finite value type
(`card_pow_le_of_fibres`): if every *left fibre* (inputs varying only on `X_S` and keeping the
outputs in `Y_T`) has at most `DT` elements and every *right fibre* at most `DS`, then
`|U| ^ n ≤ |U| ^ (|A| + |B|) · DT · DS`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut Matrix

variable {σ : Signature} {n s m : Nat}

/-! ## The general fibre bound -/

section General

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The fibre bound for a program.** If the wires `out` of a program carry `f`, every left
fibre has at most `DT` elements and every right fibre at most `DS`, then
`|U| ^ n ≤ |U| ^ (|A| + |B|) · DT · DS`. -/
theorem card_pow_le_of_fibres_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) {DT DS : Nat}
    (hT : ∀ x, (leftFibre out f S x).card ≤ DT) (hS : ∀ x, (rightFibre out f S x).card ≤ DS) :
    Fintype.card U ^ n ≤
      Fintype.card U ^ ((forward p S).card + (backward p S).card) * (DT * DS) :=
  Internal.card_pow_le_of_fibres p I out f hf S hT hS

/-- **The fibre bound.** If a circuit computes `f`, every left fibre of a split has at most
`DT` elements and every right fibre at most `DS`, then
`|U| ^ n ≤ |U| ^ (|A| + |B|) · DT · DS`. -/
theorem card_pow_le_of_fibres {c : Circuit σ n m} {I : Interpretation σ U}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) (S : Finset (Wire n c.size))
    {DT DS : Nat} (hT : ∀ x, (leftFibre c.outputs f S x).card ≤ DT)
    (hS : ∀ x, (rightFibre c.outputs f S x).card ≤ DS) :
    Fintype.card U ^ n ≤
      Fintype.card U ^ ((forward c.program S).card + (backward c.program S).card) *
        (DT * DS) :=
  Internal.card_pow_le_of_fibres c.program I c.outputs f (fun x i => congrFun (hc x) i) S hT hS

end General

/-! ## Linear maps -/

section Linear

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Left fibres of a linear map** have at most `|F| ^ (|X_S| - rank M[Y_T, X_S])`
elements. -/
theorem card_leftFibre_le (out : Fin m → Wire n s) (M : Matrix (Fin m) (Fin n) F)
    (S : Finset (Wire n s)) (x : Fin n → F) :
    (leftFibre out (fun x => M *ᵥ x) S x).card ≤
      Fintype.card F ^ ((inputsIn S).card - blockRank M (outputsIn out S)ᶜ (inputsIn S)) :=
  Internal.card_leftFibre_le out M S x

/-- **Right fibres of a linear map** have at most `|F| ^ (|X_T| - rank M[Y_S, X_T])`
elements. -/
theorem card_rightFibre_le (out : Fin m → Wire n s) (M : Matrix (Fin m) (Fin n) F)
    (S : Finset (Wire n s)) (x : Fin n → F) :
    (rightFibre out (fun x => M *ᵥ x) S x).card ≤
      Fintype.card F ^ ((inputsIn S)ᶜ.card - blockRank M (outputsIn out S) (inputsIn S)ᶜ) :=
  Internal.card_rightFibre_le out M S x

/-- **The rank-cut bound for a program.** If the wires `out` of a program carry the linear map
`x ↦ M x`, every split `S` has `rank M[Y_T, X_S] + rank M[Y_S, X_T] ≤ |A| + |B|`. -/
theorem blockRank_add_blockRank_le_of_trace (p : Program σ n s) (I : Interpretation σ F)
    (out : Fin m → Wire n s) (M : Matrix (Fin m) (Fin n) F)
    (hf : ∀ x i, p.trace I x (out i) = (M *ᵥ x) i) (S : Finset (Wire n s)) :
    blockRank M (outputsIn out S)ᶜ (inputsIn S) + blockRank M (outputsIn out S) (inputsIn S)ᶜ ≤
      (forward p S).card + (backward p S).card :=
  Internal.blockRank_add_blockRank_le p I out M hf S

/-- **The rank-cut bound.** If a circuit with values in a finite field, over any signature,
computes the linear map `x ↦ M x`, then every set `S` of its wires has
`rank M[Y_T, X_S] + rank M[Y_S, X_T] ≤ |A| + |B|`, where `X_S` and `X_T` are the inputs in `S`
and outside `S`, `Y_S` and `Y_T` the outputs whose wires lie in `S` and outside `S`, and `A`
and `B` the forward and backward signals of `S`. -/
theorem blockRank_add_blockRank_le {c : Circuit σ n m} {I : Interpretation σ F}
    {M : Matrix (Fin m) (Fin n) F} (hc : c.Computes I fun x => M *ᵥ x)
    (S : Finset (Wire n c.size)) :
    blockRank M (outputsIn c.outputs S)ᶜ (inputsIn S) +
        blockRank M (outputsIn c.outputs S) (inputsIn S)ᶜ ≤
      (forward c.program S).card + (backward c.program S).card :=
  Internal.blockRank_add_blockRank_le c.program I c.outputs M (fun x i => congrFun (hc x) i) S

end Linear

end Algebraic.Cutwidth.MultiOutput

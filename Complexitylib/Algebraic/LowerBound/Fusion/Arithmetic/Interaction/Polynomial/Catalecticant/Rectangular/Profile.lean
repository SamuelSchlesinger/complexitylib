/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular

/-!
# Rectangular catalecticant rank profiles

A single arithmetic circuit can have very different local interaction ranks at
different catalecticant splits.  This module records those bounds as a profile
`rₖ` and packages the strongest lower bound certified by any split:

`maxₖ ceil(choose d k / rₖ) ≤ multiplication cost`.

Keeping the profile separate from any particular source of local rank bounds
lets decomposition, restriction, and future shifted-flattening arguments share
the same comparison layer.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Profile

noncomputable section

variable {K : Type} {C : Type}

/-- A split-indexed family of local interaction-rank bounds for one circuit. -/
def LocalRankAtMost
    [Field K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (localRank : Fin (degree + 1) → Nat) : Prop :=
  ∀ split,
    Rectangular.LocalRankAtMost constant degree split.1 degreeAtLeastTwo
      circuit (localRank split)

/-- The strongest cost lower bound supplied by a rectangular rank profile. -/
def certifiedLowerBound
    (degree : Nat)
    (localRank : Fin (degree + 1) → Nat) : Nat :=
  Finset.univ.sup fun split : Fin (degree + 1) ↦
    Nat.choose degree split.1 ⌈/⌉ localRank split

/-- Every individual split contributes a lower bound no larger than the best
profile bound. -/
theorem split_le_certifiedLowerBound
    (degree : Nat)
    (localRank : Fin (degree + 1) → Nat)
    (split : Fin (degree + 1)) :
    Nat.choose degree split.1 ⌈/⌉ localRank split ≤
      certifiedLowerBound degree localRank := by
  exact Finset.le_sup (f := fun index : Fin (degree + 1) ↦
    Nat.choose degree index.1 ⌈/⌉ localRank index) (Finset.mem_univ split)

/-- For a positive constant local-rank bound, optimizing over all rectangular
splits is exactly the middle-layer bound. -/
theorem certifiedLowerBound_const_eq_middle
    (degree interactionRank : Nat)
    (rankPositive : 0 < interactionRank) :
    certifiedLowerBound degree (fun _ ↦ interactionRank) =
      Nat.choose degree (degree / 2) ⌈/⌉ interactionRank := by
  apply le_antisymm
  · unfold certifiedLowerBound
    apply Finset.sup_le
    intro split _
    exact (gc_mul_ceilDiv rankPositive).monotone_l
      (SumOfTerms.Waring.Rectangular.targetRank_le_middle degree split.1)
  · let middle : Fin (degree + 1) := ⟨degree / 2, by omega⟩
    simpa [middle] using
      split_le_certifiedLowerBound degree (fun _ ↦ interactionRank) middle

/-- Rank-one profiles recover the raw middle binomial coefficient. -/
@[simp] theorem certifiedLowerBound_one
    (degree : Nat) :
    certifiedLowerBound degree (fun _ ↦ 1) =
      Nat.choose degree (degree / 2) := by
  simpa using certifiedLowerBound_const_eq_middle degree 1 (by simp)

/-- A profile hypothesis recovers the rectangular Fusion lower bound at each
chosen split. -/
theorem split_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (localRank : Fin (degree + 1) → Nat)
    (rankPositive : ∀ split, 0 < localRank split)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (profile : LocalRankAtMost constant degree degreeAtLeastTwo circuit
      localRank)
    (split : Fin (degree + 1)) :
    Nat.choose degree split.1 ⌈/⌉ localRank split ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  Rectangular.choose_ceilDiv_lowerBound constant degree split.1
    degreeAtLeastTwo (localRank split) (rankPositive split) circuit constructs
    (profile split)

/-- The maximum over all rectangular splits is a certified multiplication-cost
lower bound. -/
theorem certifiedLowerBound_le_multiplicationCost
    [Field K]
    [CharZero K]
    (constant : C → K)
    (degree : Nat)
    (degreeAtLeastTwo : 2 ≤ degree)
    (localRank : Fin (degree + 1) → Nat)
    (rankPositive : ∀ split, 0 < localRank split)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) degree g 1)
    (constructs : (problem K degree).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ MvPolynomial.C (constant scalar))))
    (profile : LocalRankAtMost constant degree degreeAtLeastTwo circuit
      localRank) :
    certifiedLowerBound degree localRank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Finset.sup_le
  intro split _
  exact split_lowerBound constant degree degreeAtLeastTwo localRank
    rankPositive circuit constructs profile split

end
end Profile
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic

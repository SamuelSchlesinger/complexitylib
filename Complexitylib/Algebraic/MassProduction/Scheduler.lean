/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Card
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Affine-line recovery scheduling

This file proves the combinatorial scheduler used in the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production).
A recovery direction is projective, so each previously used point forbids at
most one direction. Greedy counting therefore gives pairwise-disjoint
punctured affine lines whenever the used point budget is smaller than
projective direction space.

This is an existence theorem. It does not yet claim the manuscript's circuit
cost for computing the schedule; that requires a separate concrete routing
construction. Public scheduler data requires only `Finite` fields and states
cardinalities with `Nat.card`; concrete enumerations remain implementation
details.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators LinearAlgebra.Projectivization

/-- All non-center points on the affine line through `target` in a
projective direction. -/
noncomputable def puncturedLine
    {K V : Type*}
    [Field K] [Finite K]
    [AddCommGroup V] [Module K V]
    (target : V)
    (direction : ℙ K V) : Finset V := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  exact (Finset.univ.erase (0 : K)).image
    (fun scalar => target + scalar • direction.rep)

/-- Recovery sets obtained by pairing targets and directions in list order.
An unmatched suffix of either list is ignored. -/
noncomputable def recoverySets
    {K V : Type*}
    [Field K] [Finite K]
    [AddCommGroup V] [Module K V] :
    List V -> List (ℙ K V) -> List (Finset V)
  | target :: targets, direction :: directions =>
      puncturedLine target direction :: recoverySets targets directions
  | _, _ => []

/-- A schedule assigns one direction per target and uses pairwise-disjoint
recovery sets. -/
def ValidSchedule
    {K V : Type*}
    [Field K] [Finite K]
    [AddCommGroup V] [Module K V]
    (targets : List V)
    (directions : List (ℙ K V)) : Prop :=
  directions.length = targets.length ∧
    (recoverySets targets directions).Pairwise Disjoint

/-- Exact geometric-sum cardinality of projective direction space. -/
theorem card_projectiveDirections
    (K : Type*)
    [Field K] [Finite K]
    (dimension : Nat) :
    Nat.card (ℙ K (Fin dimension -> K)) =
      ∑ exponent ∈ Finset.range dimension, Nat.card K ^ exponent := by
  apply Projectivization.card_of_finrank K (Fin dimension -> K)
  simp

/-- Quotient form of the projective direction count. -/
theorem card_projectiveDirections_div
    (K : Type*)
    [Field K] [Finite K]
    (dimension : Nat) :
    Nat.card (ℙ K (Fin dimension -> K)) =
      (Nat.card K ^ dimension - 1) / (Nat.card K - 1) := by
  rw [Projectivization.card'']
  simp [Nat.card_fun]

section Lines

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Membership in a punctured line is witnessed by a nonzero scalar. -/
theorem memPuncturedLine_iff
    [Finite K] (target : V) (direction : ℙ K V) (point : V) :
    point ∈ puncturedLine target direction ↔
      ∃ scalar : K, scalar ≠ 0 ∧ target + scalar • direction.rep = point := by
  classical
  simp [puncturedLine]

private theorem pointMap_injective
    (target : V)
    (direction : ℙ K V) :
    Function.Injective
      (fun scalar : K => target + scalar • direction.rep) := by
  intro left right equalPoints
  have equalMultiples : left • direction.rep = right • direction.rep :=
    add_left_cancel equalPoints
  exact smul_left_injective K direction.rep_nonzero equalMultiples

/-- A punctured affine line has one point per nonzero field scalar. -/
theorem card_puncturedLine
    [Finite K]
    (target : V)
    (direction : ℙ K V) :
    (puncturedLine target direction).card = Nat.card K - 1 := by
  classical
  rw [puncturedLine, Finset.card_image_iff.mpr]
  · simp [← Nat.card_eq_fintype_card]
  · exact (pointMap_injective target direction).injOn

/-- The center is not in its punctured affine line. -/
theorem target_not_mem_puncturedLine
    [Finite K]
    (target : V)
    (direction : ℙ K V) :
    target ∉ puncturedLine target direction := by
  classical
  rw [puncturedLine, Finset.mem_image]
  rintro ⟨scalar, scalarNonzero, equalTarget⟩
  have nonzero : scalar ≠ 0 := by simpa using scalarNonzero
  have multipleZero : scalar • direction.rep = 0 := by
    exact add_left_cancel (equalTarget.trans (add_zero target).symm)
  exact (smul_ne_zero nonzero direction.rep_nonzero) multipleZero

/-- Summing over a punctured line is the same as summing over its nonzero
parameters. -/
theorem sum_puncturedLine
    [Fintype K] [DecidableEq K]
    {A : Type*} [AddCommMonoid A]
    (target : V)
    (direction : ℙ K V)
    (function : V -> A) :
    ∑ point ∈ puncturedLine target direction, function point =
      ∑ scalar ∈ Finset.univ.erase (0 : K),
        function (target + scalar • direction.rep) := by
  classical
  unfold puncturedLine
  rw [Finset.sum_image]
  · apply Finset.sum_congr
    · ext scalar
      simp
    · intro scalar _
      rfl
  · exact (pointMap_injective target direction).injOn

/-- A punctured projective line can be enumerated using any chosen nonzero
representative of its direction.  This removes any dependence on the
arbitrary representative selected by `Projectivization.rep`. -/
theorem puncturedLine_mk_eq_image
    [Fintype K] [DecidableEq K] [DecidableEq V]
    (target vector : V)
    (vectorNonzero : vector ≠ 0) :
    puncturedLine target
        (Projectivization.mk K vector vectorNonzero) =
      (Finset.univ.erase (0 : K)).image
        (fun scalar => target + scalar • vector) := by
  classical
  obtain ⟨scale, representativeEquality⟩ :=
    Projectivization.exists_smul_eq_mk_rep K vector vectorNonzero
  have representativeEqualityField :
      (scale : K) • vector =
        (Projectivization.mk K vector vectorNonzero).rep := by
    simpa only [Units.smul_def] using representativeEquality
  rw [puncturedLine]
  ext point
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ]
  constructor
  · rintro ⟨scalar, scalarNonzero, rfl⟩
    refine ⟨scalar * (scale : K),
      ⟨mul_ne_zero scalarNonzero.1 scale.ne_zero, trivial⟩, ?_⟩
    calc
      target + (scalar * (scale : K)) • vector =
          target + scalar • ((scale : K) • vector) := by
        exact congrArg (target + ·)
          (smul_smul scalar (scale : K) vector).symm
      _ = target + scalar •
          (Projectivization.mk K vector vectorNonzero).rep := by
        rw [representativeEqualityField]
  · rintro ⟨scalar, scalarNonzero, rfl⟩
    refine ⟨scalar * (scale : K)⁻¹,
      ⟨mul_ne_zero scalarNonzero.1 (inv_ne_zero scale.ne_zero), trivial⟩,
      ?_⟩
    calc
      target + (scalar * (scale : K)⁻¹) •
          (Projectivization.mk K vector vectorNonzero).rep =
          target + (scalar * (scale : K)⁻¹) •
            ((scale : K) • vector) := by
        rw [representativeEqualityField]
      _ = target + ((scalar * (scale : K)⁻¹) * (scale : K)) •
          vector := by
        exact congrArg (target + ·)
          (smul_smul (scalar * (scale : K)⁻¹) (scale : K) vector)
      _ = target + scalar • vector := by
        rw [mul_assoc, inv_mul_cancel₀ scale.ne_zero, mul_one]

private noncomputable def forbiddenDirections
    (target : V)
    (used : Finset V) : Finset (ℙ K V) := by
  classical
  exact (used.erase target).attach.image fun point =>
    Projectivization.mk K (point.1 - target) (sub_ne_zero.mpr <| by
      exact (Finset.mem_erase.mp point.2).1)

private theorem card_forbiddenDirections_le
    (target : V)
    (used : Finset V) :
    (forbiddenDirections (K := K) target used).card <= used.card := by
  classical
  calc
    (forbiddenDirections (K := K) target used).card <=
        (used.erase target).attach.card := by
      unfold forbiddenDirections
      exact Finset.card_image_le
    _ = (used.erase target).card := Finset.card_attach
    _ <= used.card := Finset.card_erase_le

private theorem direction_mem_forbiddenDirections
    (target point : V)
    (used : Finset V)
    (pointUsed : point ∈ used)
    (pointDifferent : point ≠ target) :
    Projectivization.mk K (point - target)
        (sub_ne_zero.mpr pointDifferent) ∈
      forbiddenDirections (K := K) target used := by
  classical
  unfold forbiddenDirections
  apply Finset.mem_image.mpr
  let attached : {value // value ∈ used.erase target} :=
    ⟨point, Finset.mem_erase.mpr ⟨pointDifferent, pointUsed⟩⟩
  refine ⟨attached, Finset.mem_attach _ attached, ?_⟩
  rfl

private theorem direction_eq_of_mem_puncturedLine
    [Finite K]
    (target point : V)
    (direction : ℙ K V)
    (pointOnLine : point ∈ puncturedLine target direction) :
    Projectivization.mk K (point - target) (sub_ne_zero.mpr <| by
      intro equalTarget
      subst point
      exact target_not_mem_puncturedLine target direction pointOnLine) =
        direction := by
  classical
  rw [puncturedLine, Finset.mem_image] at pointOnLine
  obtain ⟨scalar, _, equalPoint⟩ := pointOnLine
  calc
    Projectivization.mk K (point - target) _ =
        Projectivization.mk K direction.rep direction.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
      refine ⟨scalar, ?_⟩
      rw [← equalPoint]
      simp
    _ = direction := Projectivization.mk_rep direction

/-- A direction whose projective class differs from every nonzero
`point - target` direction yields a punctured line disjoint from the used
points.  This is the pointwise form consumed by the constructive scheduler
circuit. -/
theorem puncturedLine_disjoint_of_avoids_differences
    [Finite K]
    (target : V)
    (direction : ℙ K V)
    (used : Finset V)
    (avoids : ∀ (point : V), point ∈ used ->
      ∀ pointDifferent : point ≠ target,
      direction ≠ Projectivization.mk K (point - target)
        (sub_ne_zero.mpr pointDifferent)) :
    Disjoint (puncturedLine target direction) used := by
  classical
  rw [Finset.disjoint_left]
  intro point pointOnLine pointUsed
  have pointDifferent : point ≠ target := by
    intro equalTarget
    subst point
    exact target_not_mem_puncturedLine target direction pointOnLine
  have equalDirection := direction_eq_of_mem_puncturedLine
    target point direction pointOnLine
  exact (avoids point pointUsed pointDifferent) equalDirection.symm

/-- Each occupied point blocks at most one projective direction. This is
the counting form used when a direction is sampled uniformly. -/
theorem cardIntersectingDirections_le
    [Finite K] [Finite V]
    (target : V)
    (used : Finset V) :
    Nat.card {direction : ℙ K V //
      ¬ Disjoint (puncturedLine target direction) used} ≤ used.card := by
  classical
  let _ : Fintype (ℙ K V) := Fintype.ofFinite (ℙ K V)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply le_trans (Finset.card_le_card (t := forbiddenDirections target used) ?_)
    (card_forbiddenDirections_le target used)
  intro direction membership
  have intersects := (Finset.mem_filter.mp membership).2
  obtain ⟨point, pointOnLine, pointUsed⟩ := Finset.not_disjoint_iff.mp intersects
  have pointDifferent : point ≠ target := by
    intro equalTarget
    subst point
    exact target_not_mem_puncturedLine target direction pointOnLine
  have forbidden := direction_mem_forbiddenDirections (K := K)
    target point used pointUsed pointDifferent
  rwa [direction_eq_of_mem_puncturedLine target point direction pointOnLine]
    at forbidden

/-- If fewer points are used than there are projective directions, some
punctured line through a new target avoids the used set. -/
theorem exists_puncturedLine_disjoint
    [Finite K] [Finite V]
    (target : V)
    (used : Finset V)
    (cardBound : used.card < Nat.card (ℙ K V)) :
    ∃ direction : ℙ K V,
      Disjoint (puncturedLine target direction) used := by
  classical
  let _ : Fintype (ℙ K V) := Fintype.ofFinite (ℙ K V)
  let forbidden := forbiddenDirections (K := K) target used
  have forbiddenSmall : forbidden.card < Fintype.card (ℙ K V) := by
    apply (card_forbiddenDirections_le (K := K) target used).trans_lt
    simpa only [Fintype.card_eq_nat_card] using cardBound
  have notAll : forbidden ≠ Finset.univ := by
    intro equalAll
    apply Nat.ne_of_lt forbiddenSmall
    simpa only [Finset.card_univ] using congrArg Finset.card equalAll
  have proper : forbidden ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, notAll⟩
  obtain ⟨direction, directionNotForbidden, _⟩ :=
    Finset.ssubset_iff_exists_cons_subset.mp proper
  refine ⟨direction, ?_⟩
  rw [Finset.disjoint_left]
  intro point pointOnLine pointUsed
  have pointDifferent : point ≠ target := by
    intro equalTarget
    subst point
    exact target_not_mem_puncturedLine target direction pointOnLine
  have forbiddenMembership := direction_mem_forbiddenDirections
    (K := K) target point used pointUsed pointDifferent
  have equalDirection := direction_eq_of_mem_puncturedLine
    target point direction pointOnLine
  rw [equalDirection] at forbiddenMembership
  exact directionNotForbidden forbiddenMembership

end Lines

private noncomputable def recoveryUnion
    {V : Type*}
    (sets : List (Finset V)) : Finset V := by
  classical
  exact sets.foldr (fun left right => left ∪ right) ∅

private theorem subset_recoveryUnion_of_mem
    {V : Type*}
    (sets : List (Finset V))
    (set : Finset V)
    (setMember : set ∈ sets) :
    set ⊆ recoveryUnion sets := by
  classical
  induction sets with
  | nil => simp at setMember
  | cons head tail inductionHypothesis =>
      simp only [recoveryUnion, List.foldr_cons]
      rcases List.mem_cons.mp setMember with rfl | tailMember
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (inductionHypothesis tailMember)
          Finset.subset_union_right

private theorem card_recoveryUnion_le_sum_card
    {V : Type*}
    (sets : List (Finset V)) :
    (recoveryUnion sets).card <= (sets.map Finset.card).sum := by
  classical
  induction sets with
  | nil => simp [recoveryUnion]
  | cons head tail inductionHypothesis =>
      simp only [recoveryUnion, List.foldr_cons, List.map_cons,
        List.sum_cons]
      exact (Finset.card_union_le head (recoveryUnion tail)).trans
        (Nat.add_le_add_left inductionHypothesis head.card)

section Schedule

variable {K V : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V]

private theorem sum_card_recoverySets
    (targets : List V)
    (directions : List (ℙ K V)) :
    ((recoverySets targets directions).map Finset.card).sum =
      min targets.length directions.length * (Nat.card K - 1) := by
  induction targets generalizing directions with
  | nil => simp [recoverySets]
  | cons target targets inductionHypothesis =>
      cases directions with
      | nil => simp [recoverySets]
      | cons direction directions =>
          simp only [recoverySets, List.map_cons, List.sum_cons,
            card_puncturedLine, List.length_cons]
          rw [inductionHypothesis]
          have minSuccessor :
              min (targets.length + 1) (directions.length + 1) =
                min targets.length directions.length + 1 := by
            omega
          rw [minSuccessor, Nat.add_mul]
          omega

/-- Every request list has pairwise-disjoint punctured-line recovery sets
when its exact point budget is smaller than projective direction space. -/
theorem exists_validSchedule
    [Finite V]
    (targets : List V)
    (cardBound : targets.length * (Nat.card K - 1) <
      Nat.card (ℙ K V)) :
    ∃ directions : List (ℙ K V), ValidSchedule targets directions := by
  classical
  induction targets with
  | nil =>
      exact ⟨[], by simp [ValidSchedule, recoverySets]⟩
  | cons target targets inductionHypothesis =>
      have tailBound : targets.length * (Nat.card K - 1) <
          Nat.card (ℙ K V) := by
        apply lt_of_le_of_lt _ cardBound
        gcongr
        simp
      obtain ⟨directions, equalLength, pairwise⟩ :=
        inductionHypothesis tailBound
      let sets := recoverySets targets directions
      let used := recoveryUnion sets
      have usedSmall : used.card < Nat.card (ℙ K V) := by
        apply lt_of_le_of_lt (card_recoveryUnion_le_sum_card sets)
        dsimp only [sets]
        rw [sum_card_recoverySets, equalLength, min_self]
        exact tailBound
      obtain ⟨direction, lineDisjoint⟩ :=
        exists_puncturedLine_disjoint target used usedSmall
      refine ⟨direction :: directions, ?_, ?_⟩
      · simp [equalLength]
      · simp only [recoverySets, List.pairwise_cons]
        refine ⟨?_, pairwise⟩
        intro set setMember
        exact lineDisjoint.mono_right
          (subset_recoveryUnion_of_mem sets set setMember)

/-- The paper's simpler `requests * |K|` condition implies the exact
recovery-set budget condition. -/
theorem exists_validSchedule_of_mul_card_lt
    [Finite V]
    (targets : List V)
    (cardBound : targets.length * Nat.card K < Nat.card (ℙ K V)) :
    ∃ directions : List (ℙ K V), ValidSchedule targets directions := by
  apply exists_validSchedule targets
  apply lt_of_le_of_lt _ cardBound
  exact Nat.mul_le_mul_left targets.length (Nat.sub_le _ _)

end Schedule

end MassProduction
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CollisionCut
public import Complexitylib.Algebraic.MassProduction.Nonuniform.ConditionalCounting
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Ring

/-!
# Exponential collision tails for independently chosen recovery sets

The proof applies to any finite family of recovery sets in which a fixed
point blocks at most one choice. A collision cut selects requests whose
failures become independent after the complementary directions are fixed.
Counting all such cuts proves an exponential bound without assuming that
the individual collision edges are independent.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped BigOperators

variable {Index Choice Point : Type*} [Fintype Index] [Fintype Choice]
  [DecidableEq Index] [DecidableEq Point]

/-- A request is clean if its recovery set avoids the occupied set and all
other requests' recovery sets. -/
def Clean (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (assignment : Index → Choice) (index : Index) : Prop :=
  Disjoint (sets index (assignment index)) occupied ∧
    ∀ other, other ≠ index →
      Disjoint (sets index (assignment index)) (sets other (assignment other))

/-- Nonclean request indices, including requests colliding with occupancy. -/
noncomputable def badRequests (sets : Index → Choice → Finset Point)
    (occupied : Finset Point) (assignment : Index → Choice) : Finset Index := by
  classical
  exact Finset.univ.filter fun index => ¬ Clean sets occupied assignment index

omit [Fintype Choice] [DecidableEq Index] in
/-- A large set of nonclean requests has a cut witness of any requested
size at most the ceiling of half the number of nonclean requests. -/
theorem existsRequestCollisionCut
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (assignment : Index → Choice) (size : Nat)
    (enoughBad : 2 * size ≤ (badRequests sets occupied assignment).card + 1) :
    ∃ selected : Finset Index, selected.card = size ∧
      ∀ index ∈ selected,
        ¬ Disjoint (sets index (assignment index)) occupied ∨
          ∃ other, other ∉ selected ∧
            ¬ Disjoint (sets index (assignment index))
              (sets other (assignment other)) := by
  classical
  let vertexSet : Option Index → Finset Point :=
    fun vertex => vertex.elim occupied (fun index => sets index (assignment index))
  let graph : SimpleGraph (Option Index) := {
    Adj := fun left right => left ≠ right ∧
      ¬ Disjoint (vertexSet left) (vertexSet right)
    symm := ⟨fun _ _ adjacent =>
      ⟨adjacent.1.symm, fun disjoint => adjacent.2 disjoint.symm⟩⟩
    loopless := ⟨fun _ adjacent => adjacent.1 rfl⟩ }
  let bad := (badRequests sets occupied assignment).map Function.Embedding.some
  have supported : ∀ vertex ∈ bad, ∃ other, graph.Adj vertex other := by
    intro vertex membership
    obtain ⟨index, indexBad, rfl⟩ := Finset.mem_map.mp membership
    have notClean := (Finset.mem_filter.mp indexBad).2
    by_cases occupiedHit : ¬ Disjoint (sets index (assignment index)) occupied
    · exact ⟨none, by simpa [graph, vertexSet] using occupiedHit⟩
    · have someCollision : ∃ other, other ≠ index ∧
          ¬ Disjoint (sets index (assignment index))
            (sets other (assignment other)) := by
        have : ¬ ∀ other, other ≠ index →
            Disjoint (sets index (assignment index)) (sets other (assignment other)) :=
          fun disjoint => notClean ⟨not_not.mp occupiedHit, disjoint⟩
        simpa only [not_forall, exists_prop] using this
      obtain ⟨other, different, collision⟩ := someCollision
      exact ⟨some other, by simpa [graph, vertexSet] using ⟨different.symm, collision⟩⟩
  obtain ⟨cut, cutBad, cutLarge, cutWitness⟩ := existsCollisionCut graph bad supported
  have noneNotInCut : none ∉ cut := by
    intro membership
    have := cutBad membership
    simp [bad] at this
  have cutCard : cut.eraseNone.card = cut.card :=
    Finset.card_eraseNone_of_not_mem noneNotInCut
  have enoughCut : size ≤ cut.eraseNone.card := by
    have badCard : bad.card = (badRequests sets occupied assignment).card := by
      simp [bad]
    omega
  obtain ⟨selected, selectedCut, selectedCard⟩ := Finset.exists_subset_card_eq enoughCut
  refine ⟨selected, selectedCard, ?_⟩
  intro index indexSelected
  obtain ⟨other, otherOutside, adjacent⟩ :=
    cutWitness (some index) (Finset.mem_eraseNone.mp (selectedCut indexSelected))
  cases other with
  | none => exact Or.inl adjacent.2
  | some other =>
      apply Or.inr
      refine ⟨other, ?_, adjacent.2⟩
      intro otherSelected
      exact otherOutside (Finset.mem_eraseNone.mp (selectedCut otherSelected))

/-- The union of occupancy and the complementary requests, after their
directions have been fixed. -/
noncomputable def outsidePoints
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (selected : Finset Index) (outside : {index // index ∉ selected} → Choice) :
    Finset Point :=
  occupied ∪ Finset.univ.biUnion fun index => sets index.val (outside index)

omit [Fintype Choice] in
/-- Occupancy and the complementary recovery sets use at most the sum of
their individual point budgets. -/
theorem cardOutsidePoints_le
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (selected : Finset Index) (outside : {index // index ∉ selected} → Choice)
    (setSize : Nat) (setsSmall : ∀ index choice, (sets index choice).card ≤ setSize) :
    (outsidePoints sets occupied selected outside).card ≤
      occupied.card + Fintype.card Index * setSize := by
  classical
  calc
    _ ≤ occupied.card +
        (Finset.univ.biUnion fun index => sets index.val (outside index)).card :=
      Finset.card_union_le _ _
    _ ≤ occupied.card + ∑ index : {index // index ∉ selected},
        (sets index.val (outside index)).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ occupied.card + ∑ _index : {index // index ∉ selected}, setSize := by
      gcongr with index
      exact setsSmall _ _
    _ ≤ occupied.card + Fintype.card Index * setSize := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      gcongr
      exact Fintype.card_subtype_le _

/-- For each fixed cut, the choices on its selected side are independent
once the complementary choices have been fixed. -/
theorem cardCutFailures_le
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (setSize : Nat) (setsSmall : ∀ index choice, (sets index choice).card ≤ setSize)
    (blocking : ∀ (index : Index) (used : Finset Point),
      Nat.card {choice : Choice // ¬ Disjoint (sets index choice) used} ≤ used.card)
    (selected : Finset Index) :
    Nat.card {assignment : Index → Choice //
      ∀ index ∈ selected,
        ¬ Disjoint (sets index (assignment index))
          (outsidePoints sets occupied selected (fun outside => assignment outside))} ≤
      Fintype.card Choice ^ (Fintype.card Index - selected.card) *
        (occupied.card + Fintype.card Index * setSize) ^ selected.card := by
  classical
  let allowed := fun (outside : {index // index ∉ selected} → Choice)
      (index : {index // index ∈ selected}) =>
    Finset.univ.filter fun choice =>
      ¬ Disjoint (sets index choice) (outsidePoints sets occupied selected outside)
  have allowedSmall : ∀ outside index, (allowed outside index).card ≤
      occupied.card + Fintype.card Index * setSize := by
    intro outside index
    apply le_trans _ (cardOutsidePoints_le sets occupied selected outside setSize setsSmall)
    simpa only [allowed, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card] using
      blocking index.val (outsidePoints sets occupied selected outside)
  have counted := cardConditionallyRestricted_le selected allowed
    (occupied.card + Fintype.card Index * setSize) allowedSmall
  simpa only [allowed, Finset.mem_filter, Finset.mem_univ, true_and,
    Subtype.forall] using counted

omit [Fintype Choice] in
private theorem outsideFailureOfCutWitness
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (assignment : Index → Choice) (selected : Finset Index) (index : Index)
    (witness : ¬ Disjoint (sets index (assignment index)) occupied ∨
      ∃ other, other ∉ selected ∧
        ¬ Disjoint (sets index (assignment index)) (sets other (assignment other))) :
    ¬ Disjoint (sets index (assignment index))
      (outsidePoints sets occupied selected (fun outside => assignment outside)) := by
  classical
  intro disjoint
  rcases witness with occupiedHit | ⟨other, otherOutside, collision⟩
  · exact occupiedHit (disjoint.mono_right Finset.subset_union_left)
  · apply collision
    apply disjoint.mono_right
    intro point membership
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨⟨other, otherOutside⟩, Finset.mem_univ _, membership⟩

/-- A union bound over cuts of size `ceil(k/4)` counts all assignments in
which at least half of the requests are nonclean. -/
theorem cardManyCollisions_le
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (setSize : Nat) (setsSmall : ∀ index choice, (sets index choice).card ≤ setSize)
    (blocking : ∀ (index : Index) (used : Finset Point),
      Nat.card {choice : Choice // ¬ Disjoint (sets index choice) used} ≤ used.card) :
    Nat.card {assignment : Index → Choice //
      Fintype.card Index ≤ 2 * (badRequests sets occupied assignment).card} ≤
      2 ^ Fintype.card Index *
        (Fintype.card Choice ^ (Fintype.card Index - (Fintype.card Index + 3) / 4) *
          (occupied.card + Fintype.card Index * setSize) ^ ((Fintype.card Index + 3) / 4)) := by
  classical
  let size := (Fintype.card Index + 3) / 4
  let cuts := (Finset.univ : Finset Index).powersetCard size
  let failures := fun selected : Finset Index =>
    Finset.univ.filter fun assignment : Index → Choice =>
      ∀ index ∈ selected, ¬ Disjoint (sets index (assignment index))
        (outsidePoints sets occupied selected (fun outside => assignment outside))
  have covered : (Finset.univ.filter fun assignment : Index → Choice =>
      Fintype.card Index ≤ 2 * (badRequests sets occupied assignment).card) ⊆
        cuts.biUnion failures := by
    intro assignment membership
    have manyBad := (Finset.mem_filter.mp membership).2
    have enoughBad : 2 * size ≤ (badRequests sets occupied assignment).card + 1 := by
      dsimp [size]
      omega
    obtain ⟨selected, selectedCard, witnesses⟩ :=
      existsRequestCollisionCut sets occupied assignment size enoughBad
    apply Finset.mem_biUnion.mpr
    refine ⟨selected, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, selectedCard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro index indexSelected
    exact outsideFailureOfCutWitness sets occupied assignment selected index
      (witnesses index indexSelected)
  have cutsSmall : cuts.card ≤ 2 ^ Fintype.card Index := by
    calc
      cuts.card ≤ (Finset.univ : Finset Index).powerset.card := by
        apply Finset.card_le_card
        intro selected membership
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp membership).1
      _ = _ := by simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ ≤ (cuts.biUnion failures).card := Finset.card_le_card covered
    _ ≤ ∑ selected ∈ cuts, (failures selected).card := Finset.card_biUnion_le
    _ ≤ ∑ _selected ∈ cuts,
        Fintype.card Choice ^ (Fintype.card Index - size) *
          (occupied.card + Fintype.card Index * setSize) ^ size := by
      apply Finset.sum_le_sum
      intro selected membership
      have selectedCard := (Finset.mem_powersetCard.mp membership).2
      have bound := cardCutFailures_le sets occupied setSize setsSmall blocking selected
      simpa only [failures, Nat.card_eq_fintype_card, Fintype.card_subtype, selectedCard]
        using bound
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      exact Nat.mul_le_mul_right _ cutsSmall

/-- If the blocking budget is at most `1/256` of the choice space, the
fraction of candidates with at least half their requests nonclean is at
most `2^(-k)`. The statement uses exact natural-number cardinalities. -/
theorem cardManyCollisionsMulTwoPow_le
    (sets : Index → Choice → Finset Point) (occupied : Finset Point)
    (setSize : Nat) (setsSmall : ∀ index choice, (sets index choice).card ≤ setSize)
    (blocking : ∀ (index : Index) (used : Finset Point),
      Nat.card {choice : Choice // ¬ Disjoint (sets index choice) used} ≤ used.card)
    (budget : 256 * (occupied.card + Fintype.card Index * setSize) ≤
      Fintype.card Choice) :
    Nat.card {assignment : Index → Choice //
      Fintype.card Index ≤ 2 * (badRequests sets occupied assignment).card} *
        2 ^ Fintype.card Index ≤ Fintype.card Choice ^ Fintype.card Index := by
  let count := Fintype.card Index
  let size := (count + 3) / 4
  let bound := occupied.card + count * setSize
  let choices := Fintype.card Choice
  have sizeLe : size ≤ count := by dsimp [size]; omega
  have exponentBound : 2 * count ≤ 8 * size := by dsimp [size]; omega
  have powerBound : 2 ^ (2 * count) ≤ 256 ^ size := by
    change 2 ^ (2 * count) ≤ (2 ^ 8) ^ size
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) exponentBound
  calc
    _ ≤ (2 ^ count * (choices ^ (count - size) * bound ^ size)) * 2 ^ count :=
      Nat.mul_le_mul_right _ (cardManyCollisions_le sets occupied setSize setsSmall blocking)
    _ = 2 ^ (2 * count) * bound ^ size * choices ^ (count - size) := by
      rw [two_mul count, pow_add]
      ring
    _ ≤ 256 ^ size * bound ^ size * choices ^ (count - size) := by gcongr
    _ = (256 * bound) ^ size * choices ^ (count - size) := by rw [mul_pow]
    _ ≤ choices ^ size * choices ^ (count - size) := by
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left budget size)
    _ = choices ^ count := by rw [← pow_add, Nat.add_sub_of_le sizeLe]

end Algebraic.MassProduction.Nonuniform

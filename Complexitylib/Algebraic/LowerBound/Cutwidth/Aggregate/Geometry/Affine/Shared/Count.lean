/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Relative
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Matching
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Bias

/-!
# Counting the conjunction marks removed by shared controls

Fixing a shared variable removes both endpoints of a selected exact-two pair from
the remaining-primary count. The other remaining marks form a subset of the
original multiple-primary marks.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Shared

open scoped Classical

variable {n g : Nat}

/-- Widening gate references does not change a line's original primary support. -/
private theorem primaryInputs_map_castSucc (line : Line signature n g) :
    primaryInputs (line.mapWires Wire.Renaming.castSucc) = primaryInputs line := by
  ext i
  simp only [primaryInputs, Finset.mem_filter, Finset.mem_univ, true_and,
    Line.mapWires_op, Line.mapWires_wires, Wire.Renaming.castSucc_apply]
  apply exists_congr
  intro slot
  cases line.wires slot <;> simp

/-- Widening gate references leaves the remaining-primary mark unchanged. -/
private theorem remainingMark_map_castSucc (line : Line signature n g)
    (fixed : Finset (Fin n)) :
    remainingMark (line.mapWires Wire.Renaming.castSucc) fixed = remainingMark line fixed := by
  simp [remainingMark, primaryInputs_map_castSucc]

/-- The recursive remaining count is the cardinality of its actual gate-index set. -/
theorem remainingCount_eq_card_filter (p : Program signature n g) (fixed : Finset (Fin n)) :
    remainingCount p fixed =
      (Finset.univ.filter fun gate => remainingMark (p.lines gate) fixed = true).card := by
  rw [Finset.card_filter]
  induction p with
  | empty => simp [remainingCount]
  | gate p line ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [remainingCount, Program.lines_gate_castSucc, Program.lines_gate_last,
        remainingMark_map_castSucc]
      rw [ih]

/-- A mark surviving coordinate fixing was already an original multiple-primary mark. -/
theorem multiPrimary_of_remainingMark (line : Line signature n g) (fixed : Finset (Fin n))
    (remaining : remainingMark line fixed = true) : multiPrimary line = true := by
  simp only [remainingMark, Bool.and_eq_true, decide_eq_true_eq] at remaining
  have card := Finset.card_le_card (Finset.sdiff_subset (s := primaryInputs line) (t := fixed))
  simp only [multiPrimary, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨remaining.1, by lia⟩

/-- Fixing any one variable of an exact-two support leaves at most one variable. -/
theorem remainingMark_eq_false_of_exactTwo (line : Line signature n g)
    (fixed : Finset (Fin n)) (two : (primaryInputs line).card = 2)
    (hit : ∃ j, j ∈ primaryInputs line ∧ j ∈ fixed) : remainingMark line fixed = false := by
  obtain ⟨j, primary, constant⟩ := hit
  have positive : 0 < (primaryInputs line ∩ fixed).card :=
    Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨primary, constant⟩⟩
  have card := Finset.card_sdiff_add_card_inter (primaryInputs line) fixed
  have small : ¬ 2 ≤ (primaryInputs line \ fixed).card := by lia
  simp [remainingMark, small]

/-- Removing every selected pair's common coordinate saves two original marks per pair. -/
theorem PrimaryPairing.remainingCount_add_le (p : Program signature n g)
    (P : PrimaryPairing p) (fixed : Finset (Fin n))
    (hit : ∀ e ∈ P.pairs, ∃ j, j ∈ primaryInputs (p.lines e.1) ∧
      j ∈ primaryInputs (p.lines e.2) ∧ j ∈ fixed) :
    remainingCount p fixed + 2 * P.pairs.card ≤ multiCount p := by
  classical
  let R := Finset.univ.filter fun gate => remainingMark (p.lines gate) fixed = true
  let M := Finset.univ.filter fun gate => multiPrimary (p.lines gate) = true
  have remaining_sub : R ⊆ M := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      multiPrimary_of_remainingMark _ _ (Finset.mem_filter.mp hi).2⟩
  have used_sub : P.used ⊆ M := by
    intro i hi
    obtain ⟨conjunction, two⟩ := mem_exactTwo.mp (P.used_subset hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp [multiPrimary, conjunction, two]⟩
  have disjoint : Disjoint R P.used := by
    apply Finset.disjoint_left.mpr
    intro i hr hu
    obtain ⟨e, he, endpoint⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨j, left, right, member⟩ := hit e he
    have two := (mem_exactTwo.mp (P.used_subset hu)).2
    have no : remainingMark (p.lines i) fixed = false := by
      apply remainingMark_eq_false_of_exactTwo _ _ two
      rcases Finset.mem_insert.mp endpoint with rfl | endpoint
      · exact ⟨j, left, member⟩
      · have eq : i = e.2 := Finset.mem_singleton.mp endpoint
        exact ⟨j, by simpa only [eq] using right, member⟩
    have yes := (Finset.mem_filter.mp hr).2
    rw [no] at yes
    contradiction
  have count := Finset.card_le_card (Finset.union_subset remaining_sub used_sub)
  rw [Finset.card_union_of_disjoint disjoint, P.card_used] at count
  simpa only [R, M, ← remainingCount_eq_card_filter, ← multiCount_eq_card_filter] using count

end Algebraic.Aggregate.Geometry.Shared

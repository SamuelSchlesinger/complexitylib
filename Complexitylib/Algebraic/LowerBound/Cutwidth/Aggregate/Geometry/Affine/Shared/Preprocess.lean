/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Relative
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Matching.Defs

/-!
# Fixing shared primary controls

Each selected pair contributes a common primary coordinate. Fixing that coordinate
makes both primary supports unary and forces one entire gate output. Gate-disjoint
pairs provide distinct constant-output witnesses for the independent equations.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Shared

open scoped Classical

variable {n g : Nat}

/-- The widened actual line computes precisely its indexed gate output. -/
theorem lineFunction_lines (p : Program signature n g) (i : Fin g) :
    lineFunction p (p.lines i) = p.gateFunction interpretation i := by
  funext x
  exact p.lines_eval interpretation x i

/-- Every primary literal of a conjunction has a value forcing the whole line. -/
theorem exists_controlling_value (p : Program signature n g) (line : Line signature n g)
    (conjunction : line.op.isConjunction = true) (j : Fin n)
    (primary : j ∈ primaryInputs line) :
    ∃ b : Bool, ∀ S : AffineFlat n, (∀ x ∈ S.carrier, x j = b) →
      ConstantOn S (lineFunction p line) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient => simp [Op.isConjunction] at conjunction
  | conjunction r polarity negated =>
      obtain ⟨slot, wire⟩ := (Finset.mem_filter.mp primary).2
      refine ⟨!(polarity slot), fun S value => ?_⟩
      apply constantOn_conjunction p polarity negated wires slot
      change wires slot = Wire.input j at wire
      simpa only [wire, Program.wireFunction_input] using value

/-- A finite set of constant gates contributes its full cardinality to the count. -/
theorem card_le_constantCount (p : Program signature n g) (S : AffineFlat n)
    (killed : Finset (Fin g))
    (constant : ∀ i ∈ killed, ConstantOn S (p.gateFunction interpretation i)) :
    killed.card ≤ constantCount p S := by
  have sub : killed ⊆ Finset.univ.filter fun i =>
      ConstantOn S (p.gateFunction interpretation i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, constant i hi⟩
  simpa only [Finset.card_filter, constantCount] using Finset.card_le_card sub

/-- Restricting a selected subfamily fixes every common control while recording
one distinct forced gate for each independent equation. -/
private theorem exists_preprocess_selected (p : Program signature n g) (P : PrimaryPairing p)
    (selected : Finset (Fin g × Fin g)) (subset : selected ⊆ P.pairs) :
    ∃ (S : AffineFlat n) (d : Nat) (killed : Finset (Fin g)),
      2 ^ d * S.carrier.card = 2 ^ n ∧ d ≤ selected.card ∧
      killed ⊆ selected.biUnion (fun e => {e.1, e.2}) ∧ killed.card = d ∧
      (∀ i ∈ killed, ConstantOn S (p.gateFunction interpretation i)) ∧
      ∀ e ∈ selected, ∃ j, j ∈ primaryInputs (p.lines e.1) ∧
        j ∈ primaryInputs (p.lines e.2) ∧ ConstantOn S (fun x => x j) := by
  classical
  induction selected using Finset.induction_on with
  | empty =>
      refine ⟨AffineFlat.full n, 0, ∅, ?_, ?_, ?_, rfl, ?_, ?_⟩ <;> simp
  | @insert e selected fresh ih =>
      have selected_sub : selected ⊆ P.pairs :=
        fun f hf => subset (Finset.mem_insert_of_mem hf)
      obtain ⟨S, d, killed, size, bound, used, card, constant, fixed⟩ := ih selected_sub
      have he : e ∈ P.pairs := subset (Finset.mem_insert_self _ _)
      obtain ⟨j, left, right⟩ := P.overlap e he
      have fresh_gate : e.1 ∉ selected.biUnion (fun f => {f.1, f.2}) := by
        intro h
        obtain ⟨f, hf, endpoint⟩ := Finset.mem_biUnion.mp h
        have different : e ≠ f := by rintro rfl; exact fresh hf
        have disjoint := P.disjoint he (selected_sub hf) different
        exact Finset.disjoint_left.mp disjoint (by simp) endpoint
      have fresh_killed : e.1 ∉ killed := fun h => fresh_gate (used h)
      have used_mono : selected.biUnion (fun f => {f.1, f.2}) ⊆
          (insert e selected).biUnion (fun f => {f.1, f.2}) := by
        intro i hi
        obtain ⟨f, hf, endpoint⟩ := Finset.mem_biUnion.mp hi
        exact Finset.mem_biUnion.mpr ⟨f, Finset.mem_insert_of_mem hf, endpoint⟩
      by_cases already : ConstantOn S (fun x => x j)
      · refine ⟨S, d, killed, size, ?_, used.trans used_mono, card, constant, ?_⟩
        · rw [Finset.card_insert_of_notMem fresh]
          lia
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact ⟨j, left, right, already⟩
          · exact fixed f hf
      · have eligible := (Finset.mem_filter.mp (P.eligible e he).1).2.1
        obtain ⟨b, controlling⟩ := exists_controlling_value p (p.lines e.1) eligible j left
        obtain ⟨T, sub, value, half⟩ := (affineOn_coordinate j).exists_half already b
        have forced : ConstantOn T (p.gateFunction interpretation e.1) := by
          rw [← lineFunction_lines]
          exact controlling T value
        refine ⟨T, d + 1, insert e.1 killed, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Nat.pow_succ, Nat.mul_assoc, half, size]
        · rw [Finset.card_insert_of_notMem fresh]
          lia
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_insert_self _ _, by simp⟩
          · exact used_mono (used hi)
        · rw [Finset.card_insert_of_notMem fresh_killed, card]
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact forced
          · exact (constant i hi).mono sub
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact ⟨j, left, right, b, value⟩
          · obtain ⟨i, hi, hi', hconstant⟩ := fixed f hf
            exact ⟨i, hi, hi', hconstant.mono sub⟩

/-- Shared controls can be fixed before circuit elimination, paying at most one
equation per pair and obtaining at least as many distinct constant gate outputs. -/
theorem PrimaryPairing.exists_preprocess (p : Program signature n g) (P : PrimaryPairing p) :
    ∃ (S : AffineFlat n) (d : Nat), 2 ^ d * S.carrier.card = 2 ^ n ∧
      d ≤ P.pairs.card ∧ d ≤ constantCount p S ∧
      ∀ e ∈ P.pairs, ∃ j, j ∈ primaryInputs (p.lines e.1) ∧
        j ∈ primaryInputs (p.lines e.2) ∧ ConstantOn S (fun x => x j) := by
  obtain ⟨S, d, killed, size, bound, _, card, constant, fixed⟩ :=
    exists_preprocess_selected p P P.pairs (Finset.Subset.refl _)
  exact ⟨S, d, size, bound, card ▸ card_le_constantCount p S killed constant, fixed⟩

end Algebraic.Aggregate.Geometry.Shared

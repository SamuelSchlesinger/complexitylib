/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Counting
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Defs

/-!
# Balanced conjunction outputs have no primary slots

A balanced Boolean function forced into one primary half-cube must be a literal.
Consequently a nonliteral balanced conjunction output reads only internal wires,
and its full-primary one-way message is constant.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open scoped Classical

/-- Actual gate wires selected among the circuit's outputs. -/
noncomputable def outputGateSet {n m : ℕ} (c : Circuit signature n m) : Finset (Fin c.size) :=
  Finset.univ.filter fun gate => ∃ i, c.outputs i = Wire.gate gate

/-- Conjunction gates whose wires are designated circuit outputs. -/
noncomputable def outputConjunctions {n m : ℕ} (c : Circuit signature n m) :
    Finset (Fin c.size) :=
  (outputGateSet c).filter fun gate => (c.program.lines gate).op.isConjunction = true

/-- The number of distinct conjunction output gates. -/
noncomputable def outputConjunctionCount {n m : ℕ} (c : Circuit signature n m) : ℕ :=
  (outputConjunctions c).card

/-- Nonprojection output wires of a permutation are distinct actual gates. -/
theorem exists_injective_outputGates {n : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j) :
    ∃ gate : Fin n → Fin c.size, Function.Injective gate ∧
      ∀ i, c.outputs i = Wire.gate (gate i) := by
  have gates : ∀ i, ∃ gate, c.outputs i = Wire.gate gate := by
    intro i
    cases eq : c.outputs i with
    | gate gate => exact ⟨gate, rfl⟩
    | input j =>
      apply (nonprojection i j).elim
      funext x
      change c.program.wireFunction interpretation (c.outputs i) x = x j
      rw [eq]
      rfl
  choose gate hg using gates
  refine ⟨gate, ?_, hg⟩
  intro i j heq
  by_contra different
  obtain ⟨x, hx⟩ := bijective.surjective (Function.update (fun _ => false) i true)
  have equality : c.eval interpretation x i = c.eval interpretation x j := by
    change c.program.wireFunction interpretation (c.outputs i) x =
      c.program.wireFunction interpretation (c.outputs j) x
    rw [hg i, hg j, heq]
  rw [hx] at equality
  simp [Ne.symm different] at equality

/-- A nonprojection permutation has exactly one distinct designated gate per output. -/
theorem card_outputGateSet {n : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j) :
    (outputGateSet c).card = n := by
  obtain ⟨gate, inj, hg⟩ := exists_injective_outputGates c bijective nonprojection
  have same : outputGateSet c = Finset.univ.image gate := by
    ext j
    simp only [outputGateSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, hg]
    apply exists_congr
    intro i
    constructor
    · intro h; cases h; rfl
    · intro h; rw [h]
  rw [same, Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]

/-- Distinct output gates and conjunction gates overlap exactly at conjunction outputs. -/
theorem input_add_conjunctionCount_le_size_add_outputConjunctionCount {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j) :
    n + conjunctionCount c.program ≤ c.size + outputConjunctionCount c := by
  let C := Finset.univ.filter fun gate => (c.program.lines gate).op.isConjunction = true
  have inter : outputGateSet c ∩ C = outputConjunctions c := by
    ext gate
    simp [C, outputConjunctions]
  have total := Finset.card_union_add_card_inter (outputGateSet c) C
  have upper : (outputGateSet c ∪ C).card ≤ c.size := by
    exact le_trans (Finset.card_le_univ _) (by simp)
  rw [inter, card_outputGateSet c bijective nonprojection] at total
  change (outputGateSet c ∪ C).card + outputConjunctionCount c =
    n + conjunctionCount c.program at total
  lia

/-- A balanced bit forced into a primary half-cube is a primary literal. -/
theorem eq_literal_of_balanced_forced {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i : Fin n) (a b : Bool)
    (balanced : 2 * Fintype.card {x // f x = b} = 2 ^ n)
    (forced : ∀ x, f x = b → x i = a) :
    f = fun x => (a ^^ b) ^^ x i := by
  let A := Finset.univ.filter fun x => f x = b
  let B := Finset.univ.filter fun x : Fin n → Bool => x i = a
  have sub : A ⊆ B := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, forced x (Finset.mem_filter.mp hx).2⟩
  have cardinal : A.card = B.card := by
    have half := two_mul_card_coordinate_fibre i a
    rw [Fintype.card_subtype] at balanced half
    change 2 * A.card = 2 ^ n at balanced
    change 2 * B.card = 2 ^ n at half
    lia
  have same : A = B := Finset.eq_of_subset_of_card_le sub cardinal.ge
  funext x
  have iff : f x = b ↔ x i = a := by
    have := Finset.ext_iff.mp same x
    simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using this
  cases a <;> cases b <;> cases hf : f x <;> cases hx : x i <;> simp_all

/-- A primary literal is forced by the nondefault value of a conjunction line. -/
theorem conjunction_line_forces_primary {n g : ℕ} (p : Program signature n g)
    (line : Line signature n g) (conjunction : line.op.isConjunction = true)
    (i : Fin n) (primary : i ∈ primaryInputs line) :
    ∃ a b, ∀ x, lineFunction p line x = b → x i = a := by
  obtain ⟨slot, hs⟩ := (Finset.mem_filter.mp primary).2
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient => simp [Op.isConjunction] at conjunction
  | conjunction r polarity negated =>
    refine ⟨polarity slot, !negated, ?_⟩
    intro x hx
    have all : ∀ slot, Wire.elim x (p.eval interpretation x) (wires slot) = polarity slot := by
      cases negated <;> simpa [lineFunction, Line.eval, interpretation,
        conjunctionValue] using hx
    change wires slot = .input i at hs
    simpa [hs] using all slot

/-- Balanced nonliteral conjunction output gates cannot read a primary input directly. -/
theorem primaryInputs_eq_empty_of_output_conjunction {n : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (gate : Fin c.size) (output : gate ∈ outputConjunctions c) :
    primaryInputs (c.program.lines gate) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨mem, conjunction⟩ := Finset.mem_filter.mp output
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp mem).2
  have same : lineFunction c.program (c.program.lines gate) =
      c.outputFunction interpretation i := by
    funext x
    rw [lineFunction, c.program.lines_eval]
    change c.program.gateFunction interpretation gate x =
      c.program.wireFunction interpretation (c.outputs i) x
    rw [hi]
    rfl
  obtain ⟨a, b, forced⟩ := conjunction_line_forces_primary c.program _ conjunction j hj
  rw [same] at forced
  exact nonliteral i j (a ^^ b)
    (eq_literal_of_balanced_forced _ j a b
      (two_mul_card_permutation_fibre _ bijective i b) forced)

end Algebraic.Aggregate.Geometry

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Outputs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.OneWay

/-!
# Information savings at permutation outputs

The full-primary messages determine a permutation's input. Conjunction output
messages are constant, while multiple-primary conjunction messages have quarter
bias. Removing the former and applying weighted counting gives both savings.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open scoped Classical
open Cutwidth.Aggregate.Geometry

/-- A conjunction with no primary slot has the constant true primary message. -/
theorem lineSummary_eq_true_of_primaryInputs_eq_empty {n g : ℕ}
    (line : Line signature n g) (conjunction : line.op.isConjunction = true)
    (empty : primaryInputs line = ∅) (x : Fin n → Bool) :
    lineSummary line Finset.univ (Wire.elim x (fun _ => false)) = true := by
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient => simp [Op.isConjunction] at conjunction
  | conjunction r polarity negated =>
    simp only [lineSummary, conjunctionSummary, decide_eq_true_eq]
    intro slot selected
    cases hw : wires slot with
    | gate gate => simp [hw, Capacity.selected] at selected
    | input i =>
      have mem : i ∈ primaryInputs (⟨.conjunction r polarity negated, wires⟩ :
          Line signature n g) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, slot, hw⟩
      rw [empty] at mem
      exact (Finset.notMem_empty _ mem).elim

/-- A full-primary conjunction message testing two variables has quarter bias. -/
theorem key_quarter_of_multiPrimary {n g : ℕ} (p : Program signature n g)
    (gate : Fin g) (marked : multiPrimary (p.lines gate) = true) :
    4 * (Finset.univ.filter fun x => key p Finset.univ x gate = true).card ≤
      Fintype.card (Fin n → Bool) := by
  have line_quarter (line : Line signature n g) (marked : multiPrimary line = true) :
      4 * Fintype.card {x : Fin n → Bool //
        lineSummary line Finset.univ (Wire.elim x (fun _ => false)) = true} ≤ 2 ^ n := by
    obtain ⟨hc, i, hi, j, hj, distinct⟩ := (multiPrimary_iff_exists_pair _).mp marked
    obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hj).2
    rcases line with ⟨op, wires⟩
    cases op with
    | affine r bias coefficient => simp [Op.isConjunction] at hc
    | conjunction r polarity negated =>
      conv_rhs => rw [← Fintype.card_fin n]
      apply four_mul_card_le_of_forces_pair _ i j distinct (polarity s) (polarity t)
      intro x hx
      have all : ∀ slot, Capacity.selected Finset.univ (wires slot) →
          Wire.elim x (fun _ => false) (wires slot) = polarity slot := by
        simpa [lineSummary, conjunctionSummary] using hx
      change wires s = .input i at hs
      change wires t = .input j at ht
      exact ⟨by simpa [hs] using all s (by simp [hs, Capacity.selected]),
        by simpa [ht] using all t (by simp [ht, Capacity.selected])⟩
  have h := line_quarter (p.lines gate) marked
  rw [Fintype.card_subtype] at h
  convert h using 1
  · congr 2
  · simp

/-- The gate messages of a nonprojection permutation determine its complete input. -/
theorem key_injective_of_permutation {n : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j) :
    Function.Injective (key c.program Finset.univ) := by
  obtain ⟨gate, _, hg⟩ := exists_injective_outputGates c bijective nonprojection
  intro x y h
  apply bijective.injective
  funext i
  have traces := eval_eq_of_key_eq c.program Finset.univ x y h (by simp)
  change c.program.wireFunction interpretation (c.outputs i) x =
    c.program.wireFunction interpretation (c.outputs i) y
  rw [hg i]
  exact congrFun traces (gate i)

/-- Constant conjunction outputs and biased internal summaries both save message bits. -/
theorem input_le_size_sub_outputConjunctionCount_sub_bias {n : ℕ}
    (c : Circuit signature n n) (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j) :
    (n : ℝ) ≤ c.size - outputConjunctionCount c -
      multiCount c.program * Entropy.bitSaving := by
  have nonprojection : ∀ i j, c.outputFunction interpretation i ≠ fun x => x j := by
    intro i j
    simpa using nonliteral i j false
  let O := outputConjunctions c
  let R := {gate : Fin c.size // gate ∉ O}
  let reduced (x : Fin n → Bool) (gate : R) := key c.program Finset.univ x gate.val
  have constant (gate : Fin c.size) (hg : gate ∈ O) (x : Fin n → Bool) :
      key c.program Finset.univ x gate = true := by
    exact lineSummary_eq_true_of_primaryInputs_eq_empty _ (Finset.mem_filter.mp hg).2
      (primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral gate hg) x
  have injective : Function.Injective reduced := by
    intro x y h
    apply key_injective_of_permutation c bijective nonprojection
    funext gate
    by_cases hg : gate ∈ O
    · rw [constant gate hg x, constant gate hg y]
    · exact congrFun h ⟨gate, hg⟩
  have outside (gate : Fin c.size) (hg : multiPrimary (c.program.lines gate) = true) :
      gate ∉ O := by
    intro ho
    have empty := primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral gate ho
    simp [multiPrimary, empty] at hg
  let B : Finset R := Finset.univ.filter fun gate =>
    multiPrimary (c.program.lines gate.val) = true
  have countB : B.card = multiCount c.program := by
    rw [multiCount_eq_card_filter]
    have image : B.image Subtype.val =
        Finset.univ.filter fun gate => multiPrimary (c.program.lines gate) = true := by
      ext gate
      constructor
      · intro h
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      · intro h
        have hg := (Finset.mem_filter.mp h).2
        exact Finset.mem_image.mpr ⟨⟨gate, outside gate hg⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, rfl⟩
    rw [← image, Finset.card_image_of_injective _ Subtype.val_injective]
  have countR : Fintype.card R + outputConjunctionCount c = c.size := by
    have partition := Fintype.card_subtype_compl (fun gate : Fin c.size => gate ∈ O)
    have coe : Fintype.card {gate : Fin c.size // gate ∈ O} = O.card :=
      Fintype.card_coe O
    rw [coe] at partition
    dsimp only [R, O, outputConjunctionCount]
    rw [partition]
    have bound := Finset.card_le_univ O
    simp only [Fintype.card_fin] at bound ⊢
    lia
  have entropy := Entropy.log_card_le_of_fibres_and_bias reduced B (fun _ => true)
    (K := 1) (by decide) (fun message => by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      exact injective ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))
    (fun gate hg => key_quarter_of_multiPrimary c.program gate.val
      (Finset.mem_filter.mp hg).2)
  rw [countB] at entropy
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow, Nat.cast_one, Real.log_one, zero_add] at entropy
  have cards : (Fintype.card R : ℝ) + outputConjunctionCount c = c.size := by
    exact_mod_cast countR
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_left₀ logpos).mp
  rw [sub_mul, sub_mul, Entropy.bitSaving, mul_assoc,
    div_mul_cancel₀ _ logpos.ne']
  nlinarith

end Algebraic.Aggregate.Geometry

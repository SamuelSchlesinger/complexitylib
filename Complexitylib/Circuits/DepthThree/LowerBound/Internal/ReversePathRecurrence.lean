/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-!
# Unrestricted depth-three lower bound: reverse path recurrence

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/ReversePathRecurrence.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open Finset
open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instDecidableEqV : DecidableEq V]
  [instDecidableEqI : DecidableEq I] [Fintype I]

/-- The eligible choices at a reverse reconstruction step. -/
def reverseEligible (scope : I → Finset V) (violation : I → Bool)
    (R : Finset V) : Finset I :=
  univ.filter fun i => violation i = true ∧ Disjoint (scope i) R

omit [DecidableEq I] in
@[simp] theorem mem_reverseEligible
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    (scope : I → Finset V) (violation : I → Bool)
    (R : Finset V) (i : I) :
    i ∈ reverseEligible scope violation R ↔
      violation i = true ∧ Disjoint (scope i) R := by
  classical
  simp [reverseEligible]
/-- Coordinate blocks available to the reverse reconstruction. -/
def reverseBlocks (b : ℕ) (E : Finset V) : Finset (Finset V) :=
  E.powerset.filter fun D => b < D.card

omit [DecidableEq V] in
@[simp] theorem mem_reverseBlocks
    {V : Type uDepth1}

    (b : ℕ) (E D : Finset V) :
    D ∈ reverseBlocks b E ↔ D ⊆ E ∧ b < D.card := by
  classical
  simp [reverseBlocks]
/-- A block and associated data selected during reverse reconstruction. -/
def ReverseChoice (b : ℕ) (scope : I → Finset V) (violation : I → Bool)
    (R : Finset V) (i : I) (D : Finset V) : Prop :=
  i ∈ reverseEligible scope violation R ∧ D ∈ reverseBlocks b (scope i)

omit instDecidableEqI in
theorem ReverseChoice.disjoint {b : ℕ} {scope : I → Finset V}
    {violation : I → Bool} {R : Finset V} {i : I} {D : Finset V}
    (h : ReverseChoice b scope violation R i D) : Disjoint R D := by
  have hi := (mem_reverseEligible scope violation R i).mp h.1
  have hD := (mem_reverseBlocks b (scope i) D).mp h.2
  exact hi.2.symm.mono_right hD.1

omit [DecidableEq I] in
theorem ReverseChoice.eligible_card_pos
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    {b : ℕ} {scope : I → Finset V}
    {violation : I → Bool} {R : Finset V} {i : I} {D : Finset V}
    (h : ReverseChoice b scope violation R i D) :
    0 < (reverseEligible scope violation R).card :=
  Finset.card_pos.mpr ⟨i, h.1⟩
/-- The weight assigned to a reverse reconstruction choice. -/
def reverseChoiceWeight (α : ℝ) (scope : I → Finset V) (violation : I → Bool)
    (R D : Finset V) : ℝ :=
  α ^ D.card / ((reverseEligible scope violation R).card : ℝ)

omit [DecidableEq I] in
theorem reverseChoiceWeight_nonneg
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    {α : ℝ} (hα : 0 ≤ α)
    (scope : I → Finset V) (violation : I → Bool) (R D : Finset V) :
    0 ≤ reverseChoiceWeight α scope violation R D :=
  div_nonneg (pow_nonneg hα _) (Nat.cast_nonneg _)
/-- The scalar controlling a reverse reconstruction step. -/
def reverseTheta (α : ℝ) (b k : ℕ) : ℝ :=
  ∑ l ∈ range (k + 1), if b < l then (k.choose l : ℝ) * α ^ l else 0

theorem reverseTheta_nonneg {α : ℝ} (hα : 0 ≤ α) (b k : ℕ) :
    0 ≤ reverseTheta α b k := by
  apply sum_nonneg
  intro l hl
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)
  · exact le_rfl

/-- Total weight assigned to one reverse reconstruction block. -/
def reverseBlockMass (α : ℝ) (b : ℕ) (E : Finset V) : ℝ :=
  ∑ D ∈ reverseBlocks b E, α ^ D.card

omit [DecidableEq V] in
theorem reverseBlockMass_nonneg
    {V : Type uDepth1}

    {α : ℝ} (hα : 0 ≤ α) (b : ℕ) (E : Finset V) :
    0 ≤ reverseBlockMass α b E :=
  sum_nonneg fun _ _ => pow_nonneg hα _
omit [DecidableEq V] in
theorem reverseBlockMass_eq_theta
    {V : Type uDepth1}

    (α : ℝ) (b : ℕ) (E : Finset V) :
    reverseBlockMass α b E = reverseTheta α b E.card := by
  classical
  unfold reverseBlockMass reverseBlocks
  rw [Finset.sum_filter, Finset.sum_powerset]
  unfold reverseTheta
  apply sum_congr rfl
  intro l hl
  rw [Finset.sum_powersetCard l E (fun n => if b < n then α ^ n else 0)]
  by_cases h : b < l <;> simp [h, nsmul_eq_mul]
theorem reverseTheta_mono_width {α : ℝ} (hα : 0 ≤ α) (b : ℕ)
    {e k : ℕ} (hek : e ≤ k) : reverseTheta α b e ≤ reverseTheta α b k := by
  unfold reverseTheta
  calc
    (∑ l ∈ range (e + 1), if b < l then (e.choose l : ℝ) * α ^ l else 0) ≤
        ∑ l ∈ range (e + 1), if b < l then (k.choose l : ℝ) * α ^ l else 0 := by
      apply sum_le_sum
      intro l hl
      by_cases h : b < l
      · simp only [h, ite_true]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hα _)
        exact Nat.cast_le.mpr (Nat.choose_le_choose l hek)
      · simp only [h, ite_false, le_refl]
    _ ≤ ∑ l ∈ range (k + 1), if b < l then (k.choose l : ℝ) * α ^ l else 0 := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.add_le_add_right hek 1))
      intro l hl hle
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)
      · exact le_rfl

omit instDecidableEqV in
theorem reverseBlockMass_le_theta {α : ℝ} (hα : 0 ≤ α) (b : ℕ)
    (E : Finset V) {k : ℕ} (hE : E.card ≤ k) :
    reverseBlockMass α b E ≤ reverseTheta α b k := by
  rw [reverseBlockMass_eq_theta]
  exact reverseTheta_mono_width hα b hE

/-- Sum of the weighted one-step reverse choices. -/
def reverseOneStep (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (R : Finset V) : ℝ :=
  (∑ i ∈ reverseEligible scope violation R, reverseBlockMass α b (scope i)) /
    ((reverseEligible scope violation R).card : ℝ)

omit [DecidableEq I] in
theorem sum_reverseBlockMass_le
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    {α : ℝ} (hα : 0 ≤ α) (b k : ℕ)
    (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (R : Finset V) :
    (∑ i ∈ reverseEligible scope violation R, reverseBlockMass α b (scope i)) ≤
      ((reverseEligible scope violation R).card : ℝ) * reverseTheta α b k := by
  classical
  calc
    _ ≤ ∑ i ∈ reverseEligible scope violation R, reverseTheta α b k :=
      sum_le_sum fun i hi => reverseBlockMass_le_theta hα b (scope i) (hscope i)
    _ = _ := by simp [nsmul_eq_mul]
omit instDecidableEqI in
theorem reverseOneStep_le_theta {α : ℝ} (hα : 0 ≤ α) (b k : ℕ)
    (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (R : Finset V) :
    reverseOneStep α b scope violation R ≤ reverseTheta α b k := by
  by_cases h : (reverseEligible scope violation R).Nonempty
  · have hc : (0 : ℝ) < (reverseEligible scope violation R).card := by
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr h)
    apply (div_le_iff₀ hc).mpr
    simpa only [mul_comm] using sum_reverseBlockMass_le hα b k scope hscope violation R
  · have he : reverseEligible scope violation R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simpa [reverseOneStep, he] using reverseTheta_nonneg hα b k

/-- Total weight of reverse reconstructions of the specified length. -/
def reverseTotal (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) : ℕ → Finset V → ℝ
  | 0, _ => 1
  | s + 1, R =>
      if (reverseEligible scope violation R).Nonempty then
        (∑ i ∈ reverseEligible scope violation R,
          ∑ D ∈ reverseBlocks b (scope i),
            α ^ D.card * reverseTotal α b scope violation s (R ∪ D)) /
          ((reverseEligible scope violation R).card : ℝ)
      else 0

omit [DecidableEq I] in
@[simp] theorem reverseTotal_zero
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (R : Finset V) :
    reverseTotal α b scope violation 0 R = 1 := rfl
omit [DecidableEq I] in
theorem reverseTotal_succ_of_nonempty
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (s : ℕ) (R : Finset V)
    (h : (reverseEligible scope violation R).Nonempty) :
    reverseTotal α b scope violation (s + 1) R =
      (∑ i ∈ reverseEligible scope violation R,
        ∑ D ∈ reverseBlocks b (scope i),
          α ^ D.card * reverseTotal α b scope violation s (R ∪ D)) /
        ((reverseEligible scope violation R).card : ℝ) := by
  classical
  simp only [reverseTotal, h, ite_true]
omit [DecidableEq I] in
theorem reverseTotal_succ_of_empty
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (s : ℕ) (R : Finset V)
    (h : reverseEligible scope violation R = ∅) :
    reverseTotal α b scope violation (s + 1) R = 0 := by
  classical
  simp [reverseTotal, h]
omit [DecidableEq I] in
theorem reverseTotal_nonneg
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]

    [Fintype I]
    {α : ℝ} (hα : 0 ≤ α) (b : ℕ)
    (scope : I → Finset V) (violation : I → Bool) (s : ℕ) (R : Finset V) :
    0 ≤ reverseTotal α b scope violation s R := by
  classical
  induction s generalizing R with
  | zero => simp
  | succ s ih =>
    simp only [reverseTotal]
    split_ifs
    · apply div_nonneg _ (Nat.cast_nonneg _)
      apply sum_nonneg
      intro i hi
      exact sum_nonneg fun D hD => mul_nonneg (pow_nonneg hα _) (ih (R ∪ D))
    · exact le_rfl
omit instDecidableEqI in
theorem reverseTotal_le_theta_pow {α : ℝ} (hα : 0 ≤ α) (b k : ℕ)
    (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (s : ℕ) (R : Finset V) :
    reverseTotal α b scope violation s R ≤ (reverseTheta α b k) ^ s := by
  have hθ : 0 ≤ reverseTheta α b k := reverseTheta_nonneg hα b k
  induction s generalizing R with
  | zero => simp
  | succ s ih =>
    by_cases h : (reverseEligible scope violation R).Nonempty
    · rw [reverseTotal_succ_of_nonempty α b scope violation s R h]
      have hc : (0 : ℝ) < (reverseEligible scope violation R).card := by
        exact Nat.cast_pos.mpr (Finset.card_pos.mpr h)
      apply (div_le_iff₀ hc).mpr
      calc
        (∑ i ∈ reverseEligible scope violation R,
            ∑ D ∈ reverseBlocks b (scope i),
              α ^ D.card * reverseTotal α b scope violation s (R ∪ D)) ≤
            ∑ i ∈ reverseEligible scope violation R,
              ∑ D ∈ reverseBlocks b (scope i), α ^ D.card * (reverseTheta α b k) ^ s := by
          apply sum_le_sum
          intro i hi
          exact sum_le_sum fun D hD =>
            mul_le_mul_of_nonneg_left (ih (R ∪ D)) (pow_nonneg hα _)
        _ = ∑ i ∈ reverseEligible scope violation R,
              reverseBlockMass α b (scope i) * (reverseTheta α b k) ^ s := by
          simp only [reverseBlockMass, Finset.sum_mul]
        _ ≤ ∑ i ∈ reverseEligible scope violation R,
              reverseTheta α b k * (reverseTheta α b k) ^ s := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right
            (reverseBlockMass_le_theta hα b (scope i) (hscope i)) (pow_nonneg hθ _)
        _ = (reverseTheta α b k) ^ (s + 1) *
              ((reverseEligible scope violation R).card : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, pow_succ]
          ring
    · have he : reverseEligible scope violation R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [reverseTotal_succ_of_empty α b scope violation s R he]
      exact pow_nonneg hθ _

end DepthThreeLowerBound

end

end Complexity

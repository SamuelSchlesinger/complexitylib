/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Program
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Gate-count corollaries of the capacity theorem

A run with `r` input-reading gates changes at most `2 ^ r - 1` times, so it costs at most
`4 ^ r`, and at most `4 · 2 ^ r`. Splitting the gates into single-gate runs bounds the product of
the run costs by `4 ^ s_in`; a split into `B` runs bounds it by `4 ^ B · 2 ^ s_in`. A multilevel
threshold function `F(⟨w, x⟩)` is a decomposition with one block.
-/

public section

namespace Algebraic.Threshold

variable {n s : ℕ}

private theorem two_pow_succ_le (r : ℕ) : 2 ^ (r + 1) ≤ 4 ^ r + 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have h4 : 1 ≤ 4 ^ r := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ 2 (r + 1), pow_succ 4 r]
    omega

theorem cost_oneDim_le_four_pow (r : ℕ) : (BlockKind.oneDim (2 ^ r - 1)).cost ≤ 4 ^ r := by
  rcases r with _ | r
  · simp [BlockKind.cost]
  · have h1 : 1 < 2 ^ (r + 1) := Nat.one_lt_two_pow (by omega)
    have h2 : 2 ^ (r + 1) - 1 ≠ 0 := by omega
    have h3 := two_pow_succ_le r
    simp only [BlockKind.cost, h2, ite_false]
    rw [pow_succ 4 r]
    omega

theorem cost_oneDim_le_four_mul (r : ℕ) : (BlockKind.oneDim (2 ^ r - 1)).cost ≤ 4 * 2 ^ r := by
  have := Nat.one_le_two_pow (n := r)
  simp only [BlockKind.cost]
  split_ifs <;> omega

theorem cost_oneDim_eq_max (T : ℕ) : (BlockKind.oneDim T).cost = max 1 (4 * T) := by
  simp only [BlockKind.cost]
  split_ifs with hT
  · simp [hT]
  · omega

namespace Program

variable {C : Program n s} {B : ℕ}

theorem DirectionRuns.sum_size (R : C.DirectionRuns B) :
    ∑ i ∈ Finset.range B, R.size i = C.inputGates.card := by
  classical
  unfold DirectionRuns.size
  exact (Finset.card_eq_sum_card_fiberwise
    (fun j _ => Finset.mem_range.mpr (R.run_lt j))).symm

/-- The split of the gates into single-gate runs, each along its own input weight vector. -/
noncomputable def gateRuns (C : Program n s) : C.DirectionRuns s where
  run j := j.1
  monotone := fun _ _ h => h
  run_lt j := j.2
  dir i := if h : i < s then C.inputWeight ⟨i, h⟩ else 0
  along j := ⟨1, by simp⟩

/-- The single run of a program whose input weight vectors are all multiples of `w`. -/
def singleRun (C : Program n s) (w : Fin n → ℝ)
    (along : ∀ j, ∃ c : ℝ, C.inputWeight j = c • w) : C.DirectionRuns 1 where
  run _ := 0
  monotone := monotone_const
  run_lt _ := Nat.one_pos
  dir _ := w
  along := along

theorem DirectionRuns.prod_cost_le_four_pow (R : C.DirectionRuns B) :
    ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost ≤
      4 ^ C.inputGates.card := by
  calc ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost
      ≤ ∏ i ∈ Finset.range B, 4 ^ R.size i :=
        Finset.prod_le_prod fun i _ => cost_oneDim_le_four_pow _
    _ = 4 ^ C.inputGates.card := by rw [Finset.prod_pow_eq_pow_sum, R.sum_size]

theorem DirectionRuns.prod_cost_le_four_pow_mul (R : C.DirectionRuns B) :
    ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost ≤
      4 ^ B * 2 ^ C.inputGates.card := by
  calc ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost
      ≤ ∏ i ∈ Finset.range B, 4 * 2 ^ R.size i :=
        Finset.prod_le_prod fun i _ => cost_oneDim_le_four_mul _
    _ = 4 ^ B * 2 ^ C.inputGates.card := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum, R.sum_size]

end Program

variable {f : Cslib.BooleanFunction n} {K : ℕ}

theorem two_pow_lt_of_directionRuns_internal (hf : TwoSidedRectangleFree f K)
    {C : Program n s} (hC : C.Computes f) {B : ℕ} (R : C.DirectionRuns B) :
    2 ^ n < 4 * K ^ 2 * ∏ i ∈ Finset.range B, (BlockKind.oneDim (2 ^ R.size i - 1)).cost :=
  (R.toBlockDecomposition_cost hC) ▸ two_pow_lt_mul_cost_internal hf (R.toBlockDecomposition hC)

/-- The one-block decomposition of a multilevel threshold function `F(⟨w, x⟩)`. -/
noncomputable def multilevelDecomposition (w : Fin n → ℝ) (F : ℝ → Bool) {T : ℕ}
    (hF : ChangesAtMost F T) (hfF : ∀ x, f x = F (weightedSum w x)) :
    BlockDecomposition f Bool where
  length := 1
  kind _ := .oneDim T
  history i x := if i = 0 then false else F (weightedSum w x)
  output := id
  history_zero _ _ := rfl
  step _ _ := ⟨w, fun _ t => F t, fun _ => hF, fun x => by simp⟩
  output_history x := by simp [hfF x]

theorem two_pow_lt_of_multilevel_internal (hf : TwoSidedRectangleFree f K) (w : Fin n → ℝ)
    (F : ℝ → Bool) {T : ℕ} (hF : ChangesAtMost F T) (hfF : ∀ x, f x = F (weightedSum w x)) :
    2 ^ n < 4 * K ^ 2 * max 1 (4 * T) := by
  have h := two_pow_lt_mul_cost_internal hf (multilevelDecomposition w F hF hfF)
  simpa [BlockDecomposition.cost, multilevelDecomposition, cost_oneDim_eq_max] using h

/-- Binary logarithms of a capacity bound with `K ≤ 2 ^ k` and `X ≤ 2 ^ e`. -/
theorem lt_of_two_pow_lt_mul {n k K X e : ℕ} (hK : K ≤ 2 ^ k) (hX : X ≤ 2 ^ e)
    (h : 2 ^ n < 4 * K ^ 2 * X) : n < 2 * k + 2 + e := by
  have hle : 4 * K ^ 2 * X ≤ 2 ^ (2 * k + 2 + e) := by
    calc 4 * K ^ 2 * X ≤ 4 * (2 ^ k) ^ 2 * 2 ^ e :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK _)) hX
      _ = 2 ^ (2 * k + 2 + e) := by
          rw [pow_add, pow_add, ← pow_mul, mul_comm k 2]
          ring
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (h.trans_le hle)

theorem two_pow_sub_lt_of_multilevel_internal (hf : TwoSidedRectangleFree f K) {k : ℕ}
    (hK : K ≤ 2 ^ k) (w : Fin n → ℝ) (F : ℝ → Bool) {T : ℕ} (hF : ChangesAtMost F T)
    (hfF : ∀ x, f x = F (weightedSum w x)) (hn : 2 * k + 4 ≤ n) :
    2 ^ (n - (2 * k + 4)) < T := by
  have h := two_pow_lt_of_multilevel_internal hf w F hF hfF
  by_contra hT
  push Not at hT
  have hX : max 1 (4 * T) ≤ 2 ^ (n - (2 * k + 2)) := by
    have h1 : 1 ≤ 2 ^ (n - (2 * k + 2)) := Nat.one_le_two_pow
    have h2 : 4 * T ≤ 2 ^ (n - (2 * k + 2)) := by
      have : 2 ^ (n - (2 * k + 2)) = 4 * 2 ^ (n - (2 * k + 4)) := by
        rw [show n - (2 * k + 2) = (n - (2 * k + 4)) + 2 by omega, pow_add]
        ring
      omega
    exact max_le h1 h2
  have := lt_of_two_pow_lt_mul hK hX h
  omega

end Algebraic.Threshold

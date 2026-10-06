/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.Family
public import Complexitylib.Circuits.Threshold.Parity.Defs
public import Complexitylib.Circuits.XOR
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Depth-two threshold circuits for parity -- proof internals
-/


public section

namespace Complexity

/-- `Fin.countP` is the sum of the indicator values. -/
private theorem countP_eq_sum_toNat {n : ℕ} (p : Fin n → Bool) :
    Fin.countP p = ∑ i, (p i).toNat := by
  induction n with
  | zero => simp
  | succ n ih => rw [Fin.countP_succ, Fin.sum_univ_succ, ih]

/-- Parity is the parity of the number of true inputs. -/
theorem xorBool_eq_decide_countP_internal (N : ℕ) (x : BitString N) :
    Schnorr.xorBool N x = decide (Fin.countP x % 2 = 1) := by
  induction N with
  | zero => simp [Schnorr.xorBool]
  | succ n ih =>
    rw [Fin.countP_succ]
    change (x 0).xor (Schnorr.xorBool n (fun i => x i.succ)) = _
    rw [ih]
    generalize Fin.countP (fun i => x i.succ) = c
    cases x 0 <;> by_cases h : c % 2 = 1 <;> simp [h] <;> omega

/-- The signed inputs of the output gate, as a sum over `j < n`: exactly
`n / 2 + w % 2` are true when `w ≤ n`. -/
private theorem sum_signed_thresholds (n w : ℕ) :
    ∑ j ∈ Finset.range n, ((decide (j % 2 = 1)).xor (decide (j + 1 ≤ w))).toNat =
      if w ≤ n then n / 2 + w % 2 else (n + 1) / 2 := by
  induction n with
  | zero => by_cases hw : w = 0 <;> simp [hw]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h3 : n % 2 = 1 <;> by_cases h4 : n + 1 ≤ w <;> split_ifs <;> simp [h3, h4] <;>
      omega

/-- A max-fold from zero is bounded by a common bound of its terms. -/
private theorem foldl_max_le {n b : ℕ} (f : Fin n → ℕ) (h : ∀ k, f k ≤ b) :
    Fin.foldl n (fun acc k => max acc (f k)) 0 ≤ b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    exact max_le (ih (fun k => f k.castSucc) fun k => h _) (h _)

namespace Circuit

/-- Internal gate `j` of the parity circuit tests whether at least `j + 1`
inputs are true. -/
theorem wireValue_thresholdParity_natAdd_internal (N : ℕ) [NeZero N]
    (x : BitString N) (j : Fin N) :
    (thresholdParity N).wireValue x (Fin.natAdd N j) =
      decide (j.val + 1 ≤ Fin.countP x) := by
  rw [wireValue_of_not_lt _ _ _ (by simp)]
  have hinputs : (fun i : Fin N =>
      (false).xor ((thresholdParity N).wireValue x (Fin.castAdd N i))) = x := by
    funext i
    rw [wireValue_of_lt _ _ _ (by simp)]
    simp
  change decide ((N + j.val - N) + 1 ≤ Fin.countP (fun i : Fin N =>
      (false).xor ((thresholdParity N).wireValue x (Fin.castAdd N i)))) = _
  rw [hinputs, Nat.add_sub_cancel_left]

theorem eval_thresholdParity_internal (N : ℕ) [NeZero N] (x : BitString N) :
    (thresholdParity N).eval x 0 = Schnorr.xorBool N x := by
  rw [xorBool_eq_decide_countP_internal]
  have hout : (fun j : Fin N => (decide (j.val % 2 = 1)).xor
      ((thresholdParity N).wireValue x (Fin.natAdd N j))) =
      fun j : Fin N => (decide (j.val % 2 = 1)).xor (decide (j.val + 1 ≤ Fin.countP x)) := by
    funext j
    rw [wireValue_thresholdParity_natAdd_internal]
  change decide (N / 2 + 1 ≤ Fin.countP (fun j : Fin N => (decide (j.val % 2 = 1)).xor
      ((thresholdParity N).wireValue x (Fin.natAdd N j)))) = _
  rw [hout, countP_eq_sum_toNat,
    Fin.sum_univ_eq_sum_range (fun j => ((decide (j % 2 = 1)).xor
      (decide (j + 1 ≤ Fin.countP x))).toNat),
    sum_signed_thresholds]
  simp only [Fin.countP_le x, ↓reduceIte]
  by_cases h : Fin.countP x % 2 = 1 <;> simp <;> omega

/-- Every wire of the parity circuit has depth at most one. -/
private theorem wireDepth_thresholdParity_le (N : ℕ) [NeZero N] (w : Fin (N + N)) :
    (thresholdParity N).wireDepth w ≤ 1 := by
  by_cases hw : w.val < N
  · rw [wireDepth_of_lt _ _ hw]
    omega
  · rw [wireDepth_of_not_lt _ _ hw]
    refine Nat.add_le_add_left (foldl_max_le (b := 0) _ fun k => ?_) 1
    have hk : (((thresholdParity N).gates ⟨w.val - N, by omega⟩).inputs k).val < N :=
      k.isLt
    exact (wireDepth_of_lt _ _ hk).le

theorem depth_thresholdParity_le_internal (N : ℕ) [NeZero N] :
    (thresholdParity N).depth ≤ 2 := by
  have hfold := foldl_max_le (b := 1) (fun k => (thresholdParity N).wireDepth
    (((thresholdParity N).outputs 0).inputs k)) fun k => wireDepth_thresholdParity_le N _
  simp only [depth, outputDepth, Fin.foldl_succ, Fin.foldl_zero]
  omega

end Circuit

theorem CircuitFamily.thresholdParity_computes_internal :
    CircuitFamily.thresholdParity.Computes Schnorr.xorBool := by
  funext n x
  cases n with
  | zero => rfl
  | succ n => exact Circuit.eval_thresholdParity_internal (n + 1) x

theorem CircuitFamily.thresholdParity_size_internal (n : ℕ) :
    CircuitFamily.thresholdParity.size n ≤ n + 1 := by
  cases n with
  | zero => simp
  | succ n => exact le_refl _

theorem CircuitFamily.thresholdParity_depth_internal (n : ℕ) :
    CircuitFamily.thresholdParity.depth n ≤ 2 := by
  cases n with
  | zero => simp
  | succ n => exact Circuit.depth_thresholdParity_le_internal (n + 1)

theorem xorBool_mem_TC0_internal : Schnorr.xorBool ∈ TC0 := by
  refine mem_TC0_iff.mpr ⟨CircuitFamily.thresholdParity, 2,
    CircuitFamily.thresholdParity_computes_internal, ⟨Polynomial.X + 1, fun n => ?_⟩,
    CircuitFamily.thresholdParity_depth_internal⟩
  simpa using CircuitFamily.thresholdParity_size_internal n

end Complexity

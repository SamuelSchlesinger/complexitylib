/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Paired
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Internal
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit.Internal

/-!
# The periodic Landsberg–Michałek tensors: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.Periodic`.

* **Entries.** The coefficient `periodicWeight k A M a j` is `2^{2^e}` with
  `e = (a mod A) M + (j mod M) < A M` when `A, M > 0`, so every entry of
  `periodicLMTensor k A M` is `0` or `2^{2^e}` with `e < A M`.
* **Window labels.** Equal codes `(a mod A) M + (j mod M)` give `a ≡ a' (mod A)` and
  `j ≡ j' (mod M)`. If `|a - a'| ≤ L < A` and `|j - j'| ≤ p L < M`, then `a = a'` and `j = j'`.
* **The paired-cluster Koszul bound.** The certificate for `T_k(γ)` with window labels
  (`Tensor3.div_mul_phi_sub_le_borderRank_restrictSlices_lmTensor`) gives
  `PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 (p + 1) L)` for `L < A`, `p L < M`.
* **The bounds.** The assembly of `Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit` applies
  to every tight tensor with nonzero slices satisfying `PairedKoszulBoundOn`. For the asymptotic
  forms fix `p`, then `L ≥ max (3^{2p} + 1) (2 (3^{2p} + 1) / δ)`, then `A = L + 1` and
  `M = p L + 1`.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal.Periodic

open Finset Filter

variable {k p A M : ℕ}

/-! ### Entries -/

theorem periodicWeight_eq (k A M : ℕ) (a j : Fin (2 * k + 1)) :
    periodicWeight k A M a j = 2 ^ 2 ^ ((a : ℕ) % A * M + (j : ℕ) % M) := by
  simp [periodicWeight]

theorem periodicWeight_ne_zero (k A M : ℕ) (a j : Fin (2 * k + 1)) :
    periodicWeight k A M a j ≠ 0 := by
  unfold periodicWeight
  exact_mod_cast (pow_pos two_pos _).ne'

theorem code_lt (hA : 0 < A) (hM : 0 < M) (a j : ℕ) : a % A * M + j % M < A * M := by
  have ha : a % A + 1 ≤ A := Nat.mod_lt _ hA
  have hj : j % M < M := Nat.mod_lt _ hM
  calc a % A * M + j % M < a % A * M + M := by omega
    _ = (a % A + 1) * M := by ring
    _ ≤ A * M := Nat.mul_le_mul_right _ ha

theorem periodicLMTensor_apply (k A M : ℕ) (a j l : Fin (2 * k + 1)) :
    periodicLMTensor k A M a j l =
      if (l : ℤ) = j + ((a : ℤ) - k) then periodicWeight k A M a j else 0 :=
  rfl

theorem periodicLMTensor_apply_mem (hA : 0 < A) (hM : 0 < M) (a j l : Fin (2 * k + 1)) :
    periodicLMTensor k A M a j l ∈
      insert (0 : ℂ) ((range (A * M)).image fun e => ((2 ^ 2 ^ e : ℕ) : ℂ)) := by
  rw [periodicLMTensor_apply]
  split_ifs
  · exact mem_insert_of_mem (mem_image.2 ⟨_, mem_range.2 (code_lt hA hM a j), rfl⟩)
  · exact mem_insert_self _ _

/-! ### Window labels -/

/-- The periodic codes `(a mod A) M + (j mod M)` separate positions whose slices differ by at
most `L < A` and whose columns differ by at most `p L < M`. -/
theorem periodic_label_window {L : ℕ} (hA : L < A) (hM : p * L < M) (a a' j j' : Fin (2 * k + 1))
    (ha : |(a : ℤ) - a'| ≤ L) (hj : |(j : ℤ) - j'| ≤ p * L)
    (h : (a : ℕ) % A * M + (j : ℕ) % M = (a' : ℕ) % A * M + (j' : ℕ) % M) :
    a = a' ∧ j = j' := by
  obtain ⟨h1, h2⟩ := Diagonal.code_injective (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h
  have hpL : ((p * L : ℕ) : ℤ) < M := by exact_mod_cast hM
  push_cast at hpL
  refine ⟨Fin.ext (Nat.ModEq.eq_of_abs_lt h1 ?_), Fin.ext (Nat.ModEq.eq_of_abs_lt h2 ?_)⟩
  · rw [abs_sub_comm]
    exact ha.trans_lt (by exact_mod_cast hA)
  · rw [abs_sub_comm]
    exact hj.trans_lt hpL

/-! ### The paired-cluster Koszul bound -/

theorem pairedKoszulBoundOn_periodicLMTensor {L : ℕ} (hA : L < A) (hM : p * L < M) :
    PairedKoszulBoundOn (periodicLMTensor k A M) p L (8 * (p + 1) * L) :=
  fun S cp cn hcp hcn hSP hSN hoP hoN hLP hLN hP hN =>
    div_mul_phi_sub_le_borderRank_restrictSlices_lmTensor (periodicWeight k A M)
      (fun a j => (a : ℕ) % A * M + (j : ℕ) % M) (periodicWeight_eq k A M) S cp cn hcp hcn hSP
      hSN (periodic_label_window hA hM) hoP hoN hLP hLN hP hN

/-! ### The bounds -/

theorem tight_periodicLMTensor (k A M : ℕ) : (periodicLMTensor k A M).Tight :=
  tight_lmTensor k _

theorem periodicLMTensor_ne_zero (k A M : ℕ) (a : Fin (2 * k + 1)) :
    periodicLMTensor k A M a ≠ 0 :=
  lmTensor_ne_zero k (periodicWeight_ne_zero k A M) a

theorem le_borderRank {L : ℕ} (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k)
    (hA : L < A) (hM : p * L < M) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) -
        (16 * (p + 1) * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      (periodicLMTensor k A M).borderRank :=
  Explicit.le_borderRank_of_pairedKoszulBoundOn_eight (tight_periodicLMTensor k A M)
    (periodicLMTensor_ne_zero k A M) (pairedKoszulBoundOn_periodicLMTensor hA hM) hp hL hLk

theorem eventually_le_borderRank (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {L : ℕ}
    (hL : 3 ^ (2 * p) + 1 ≤ L) (hLδ : 2 * (3 ^ (2 * p) + 1 : ℝ) / δ ≤ L) (hA : L < A)
    (hM : p * L < M) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (periodicLMTensor k A M).borderRank :=
  Explicit.eventually_le_borderRank_of_pairedKoszulBoundOn
    (T := fun k => periodicLMTensor k A M) (fun k => tight_periodicLMTensor k A M)
    (fun k => periodicLMTensor_ne_zero k A M) hp hδ hL hLδ
    (Eventually.of_forall fun _ => pairedKoszulBoundOn_periodicLMTensor hA hM)

theorem exists_eventually_le_borderRank (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A M : ℕ, ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (periodicLMTensor k A M).borderRank := by
  obtain ⟨L, hL, hLδ⟩ := Explicit.exists_blockLength p δ
  exact ⟨L + 1, p * L + 1, eventually_le_borderRank hp hδ hL hLδ (by omega) (by omega)⟩

theorem eventually_twentyOne_div_ten :
    ∀ᶠ k : ℕ in atTop, (21 / 10 : ℝ) * (2 * k + 1) ≤
      (periodicLMTensor k 14761 29521).borderRank := by
  filter_upwards [eventually_le_borderRank (p := 2) (δ := 1 / 90) (L := 14760) (A := 14761)
    (M := 29521) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)] with k hk
  convert hk using 2
  norm_num

theorem exists_eventually_seven_div_three {ε : ℝ} (hε : 0 < ε) :
    ∃ A M : ℕ, ∀ᶠ k : ℕ in atTop, (7 / 3 - ε) * (2 * k + 1 : ℝ) ≤
      (periodicLMTensor k A M).borderRank := by
  obtain ⟨p, hp, hlt⟩ := Explicit.exists_two_div_lt hε
  obtain ⟨A, M, h⟩ := exists_eventually_le_borderRank hp (sub_pos.2 hlt)
  refine ⟨A, M, ?_⟩
  filter_upwards [h] with k hk
  convert hk using 2
  ring

end Algebraic.Tensor3.Internal.Periodic

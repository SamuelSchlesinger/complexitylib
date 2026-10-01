/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Rectangle
import Mathlib.Tactic.Linarith

/-!
# The bounded-round density adversary

Induct on the remaining messages and maintain Korten's density rectangle.
The finite parameter specialization uses `K_i = 194^i*k` and
`p_i = (32768*194^d*k)^i*p`. Bilateral limits at the root avoid a mirror
step for the first message, giving the exponent `d-1` for `d` rounds.

Source: Oliver Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221
(2026), https://eccc.weizmann.ac.il/report/2026/221/, Sections 2--4.
-/

public section

namespace Complexity.KarchmerWigderson.RoundProtocol

open BooleanAnalysis
open scoped Classical

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]

theorem not_solves_density_internal {d : ℕ} (P : RoundProtocol ι M d)
    {X Y : Finset (ι → Bool)} {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m)
    (k p : ℕ → ℝ)
    (hstep : ∀ i < d, 1 ≤ k i ∧ 194 * k i ≤ k (i + 1) ∧
      2 * k i + 2 + m ≤ k (i + 1) ∧ 32768 * k i * p i ≤ p (i + 1))
    (hcap : ∀ i ≤ d, p i ≤ 1 / 4) (h : DensityRectangle X Y (p 0) (k 0)) :
    ¬ P.Solves X Y := by
  intro hsol
  induction d generalizing X Y k p with
  | zero =>
    cases P with
    | answer i => exact h.not_separated_internal (by linarith [hcap 0 (by omega)]) i hsol
  | succ d ih =>
    cases P with
    | answer i => exact h.not_separated_internal (by linarith [hcap 0 (by omega)]) i hsol
    | alice send next =>
      have hs := hstep 0 (by omega)
      obtain ⟨a, X', hsub, hsend, hnew⟩ := h.select_left_message_internal send hM
        hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 (hcap 1 (by omega))
      have hchild : (next a).Solves X' Y := by
        intro x hx y hy
        have he := hsol x (hsub hx) y hy
        simpa only [run, hsend x hx] using he
      exact ih (next a) (fun i => k (i + 1)) (fun i => p (i + 1))
        (fun i hi => hstep (i + 1) (by omega))
        (fun i hi => hcap (i + 1) (by omega)) hnew hchild
    | bob send next =>
      have hs := hstep 0 (by omega)
      obtain ⟨a, Y', hsub, hsend, hnew⟩ := h.swap_internal.select_left_message_internal send hM
        hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 (hcap 1 (by omega))
      have hchild : (next a).Solves X Y' := by
        intro x hx y hy
        have he := hsol x hx y (hsub hy)
        simpa only [run, hsend y hy] using he
      exact ih (next a) (fun i => k (i + 1)) (fun i => p (i + 1))
        (fun i hi => hstep (i + 1) (by omega))
        (fun i hi => hcap (i + 1) (by omega)) hnew.swap_internal hchild

theorem not_solves_bounded_density_internal {d : ℕ} (P : RoundProtocol ι M d)
    {X Y : Finset (ι → Bool)} {m k p : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hk : 1 ≤ k) (hmk : m + 1 ≤ k)
    (hbudget : (32768 * (194 : ℝ) ^ d * k) ^ d * p ≤ 1 / 4)
    (h : DensityRectangle X Y p k) : ¬ P.Solves X Y := by
  let C : ℝ := 32768 * (194 : ℝ) ^ d * k
  let K (i : ℕ) : ℝ := (194 : ℝ) ^ i * k
  let B (i : ℕ) : ℝ := C ^ i * p
  have hp : 0 ≤ p := by
    obtain ⟨r, hr, hrp, _⟩ := h.2.2.2.2
    exact hr.le.trans hrp
  have hC : 1 ≤ C := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    dsimp [C]
    nlinarith [mul_le_mul hk hh (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  have hK (i : ℕ) : k ≤ K i := by
    have hh : 1 ≤ (194 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    dsimp [K]
    nlinarith
  have hKsucc (i : ℕ) : K (i + 1) = 194 * K i := by dsimp [K]; rw [pow_succ]; ring
  have hBsucc (i : ℕ) : B (i + 1) = C * B i := by dsimp [B]; rw [pow_succ]; ring
  apply P.not_solves_density_internal hM K B
  · intro i hi
    refine ⟨hk.trans (hK i), (hKsucc i).ge, ?_, ?_⟩
    · rw [hKsucc]
      linarith [hK i]
    · rw [hBsucc]
      have hiC : 32768 * K i ≤ C := by
        have ht := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 194) (Nat.le_of_lt hi))
          (show 0 ≤ k by linarith)
        dsimp [K, C]
        nlinarith
      exact mul_le_mul_of_nonneg_right hiC (mul_nonneg (pow_nonneg (by linarith) _) hp)
  · intro i hi
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hi) hp).trans hbudget
  · simpa only [K, B, pow_zero, one_mul] using h

theorem not_solves_bilateral_density_with_deficit_internal {d : ℕ} (P : RoundProtocol ι M (d + 1))
    {X Y : Finset (ι → Bool)} {m p k : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m) (hk : 1 ≤ k) (hp : 0 < p)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hdX : uniformDeficit X ≤ k) (hdY : uniformDeficit Y ≤ k)
    (hleft : ∀ x ∈ X, IsDensityLimit Y p k x) (hright : ∀ y ∈ Y, IsDensityLimit X p k y)
    (hbudget : (32768 * (194 : ℝ) ^ d * (m + k)) ^ d * p ≤ 1 / 4) :
    ¬ P.Solves X Y := by
  have hC : 1 ≤ 32768 * (194 : ℝ) ^ d * (m + k) := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ (194 : ℝ) ^ d by positivity) hm]
  have hcap : p ≤ 1 / 4 := by
    have ht := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := d) hC) hp.le
    simp only [one_mul] at ht
    exact ht.trans hbudget
  intro hsol
  cases P with
  | answer i =>
    have h : DensityRectangle X Y p k := ⟨hX, hY, hdX, hdY, p, hp, le_rfl, Or.inl hleft⟩
    exact h.not_separated_internal (by linarith) i hsol
  | alice send next =>
    obtain ⟨a, hne, hdef⟩ := exists_large_message_fiber_internal X hX send hM
    let X' := X.filter (fun x => send x = a)
    have hnew : DensityRectangle X' Y p (m + k) := by
      refine ⟨hne, hY, by linarith, by linarith, p, hp, le_rfl, Or.inl ?_⟩
      intro x hx
      exact (hleft x (Finset.mem_filter.mp hx).1).mono_deficit_internal
        hp.le (by linarith) (by linarith)
    apply (next a).not_solves_bounded_density_internal hM (k := m + k)
      (by linarith) (by linarith) hbudget hnew
    intro x hx y hy
    have he := hsol x (Finset.mem_filter.mp hx).1 y hy
    simpa only [run, (Finset.mem_filter.mp hx).2] using he
  | bob send next =>
    obtain ⟨a, hne, hdef⟩ := exists_large_message_fiber_internal Y hY send hM
    let Y' := Y.filter (fun y => send y = a)
    have hnew : DensityRectangle X Y' p (m + k) := by
      refine ⟨hX, hne, by linarith, by linarith, p, hp, le_rfl, Or.inr ?_⟩
      intro y hy
      exact (hright y (Finset.mem_filter.mp hy).1).mono_deficit_internal
        hp.le (by linarith) (by linarith)
    apply (next a).not_solves_bounded_density_internal hM (k := m + k)
      (by linarith) (by linarith) hbudget hnew
    intro x hx y hy
    have he := hsol x hx y (Finset.mem_filter.mp hy).1
    simpa only [run, (Finset.mem_filter.mp hy).2] using he

theorem not_solves_bilateral_density_internal {d : ℕ} (P : RoundProtocol ι M (d + 1))
    {X Y : Finset (ι → Bool)} {m p : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m) (hp : 0 < p)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hdX : uniformDeficit X ≤ 1) (hdY : uniformDeficit Y ≤ 1)
    (hleft : ∀ x ∈ X, IsDensityLimit Y p 1 x) (hright : ∀ y ∈ Y, IsDensityLimit X p 1 y)
    (hbudget : (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d * p ≤ 1 / 4) :
    ¬ P.Solves X Y :=
  not_solves_bilateral_density_with_deficit_internal P hM hm le_rfl hp
    hX hY hdX hdY hleft hright hbudget

end Complexity.KarchmerWigderson.RoundProtocol

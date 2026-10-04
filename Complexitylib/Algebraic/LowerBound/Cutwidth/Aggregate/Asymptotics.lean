/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics

/-!
# Absorbing aggregate budgets in a circuit lower bound

This numerical layer takes the density-preserving slice and its accepting-input bound as
explicit hypotheses. Sublinear aggregate budgets and rectangle thresholds preserve the
leading coefficient of the underlying graph-ordering bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open Filter

/-- Taking logarithms of the finite aggregate-count bound costs seven constant bits. -/
theorem log_bound_of_count {A η C N : ℝ} (hAη : 0 ≤ A + η) (hC : 0 ≤ C)
    (hN : 1 ≤ N) {m g D K : Nat} (hK : 0 < K)
    (hcount : (2 : ℝ) ^ ((m : ℝ) - 2) ≤
      (N * (2 : ℝ) ^ ((A + η) * max ((g : ℝ) - m) 0 +
        3 * Real.logb 2 N + C + 3) + 1) * (2 : ℝ) ^ ((D : ℝ) + 1) * K ^ 2) :
    (m : ℝ) ≤ (A + η) * max ((g : ℝ) - m) 0 +
      4 * Real.logb 2 N + C + D + 2 * Real.logb 2 K + 7 := by
  let X := (A + η) * max ((g : ℝ) - m) 0 + 3 * Real.logb 2 N + C + 3
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hX : 0 ≤ X := by
    have hlog := Real.logb_nonneg one_lt_two hN
    have hmul := mul_nonneg hAη (le_max_right ((g : ℝ) - m) 0)
    dsimp [X]
    linarith
  have hpow : 1 ≤ (2 : ℝ) ^ X := Real.one_le_rpow one_le_two hX
  have hNX : 1 ≤ N * (2 : ℝ) ^ X := by nlinarith
  have hdouble : N * (2 : ℝ) ^ X + 1 ≤ 2 * N * (2 : ℝ) ^ X := by linarith
  have hupper : (2 : ℝ) ^ ((m : ℝ) - 2) ≤
      2 * N * (2 : ℝ) ^ X * (2 : ℝ) ^ ((D : ℝ) + 1) * K ^ 2 := by
    exact hcount.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdouble (by positivity)) (by positivity))
  have hexact : 2 * N * (2 : ℝ) ^ X * (2 : ℝ) ^ ((D : ℝ) + 1) * K ^ 2 =
      (2 : ℝ) ^ (1 + Real.logb 2 N + X + ((D : ℝ) + 1) + 2 * Real.logb 2 K) := by
    symm
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_logb (by norm_num) (by norm_num) hNpos,
      show (2 : ℝ) ^ (2 * Real.logb 2 K) = ((2 : ℝ) ^ Real.logb 2 K) ^ 2 by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        push_cast
        ring_nf,
      Real.rpow_logb (by norm_num) (by norm_num) hKpos]
  rw [hexact] at hupper
  have hexp := (Real.rpow_le_rpow_left_iff one_lt_two).mp hupper
  dsimp [X] at hexp
  linarith

/-- The finite slice information needed by the asymptotic numerical argument. -/
def SliceBound (A η C : ℝ) (n g D K : Nat) : Prop :=
  ∃ m : Nat, 2 ≤ m ∧ m ≤ n ∧ n - m ≤ D + Nat.clog 2 K + 3 ∧
    (2 : ℝ) ^ ((m : ℝ) - 2) ≤
      (((n : ℝ) + 3 * g) * (2 : ℝ) ^ ((A + η) * max ((g : ℝ) - m) 0 +
        3 * Real.logb 2 ((n : ℝ) + 3 * g) + C + 3) + 1) *
          (2 : ℝ) ^ ((D : ℝ) + 1) * K ^ 2

/-- Increasing the allowed aggregate budget preserves the finite slice bound. -/
theorem SliceBound.mono_budget {A η C : ℝ} {n g D D' K : Nat}
    (h : SliceBound A η C n g D K) (hD : D ≤ D') :
    SliceBound A η C n g D' K := by
  obtain ⟨m, hm, hmn, hdef, hcount⟩ := h
  refine ⟨m, hm, hmn, by lia, hcount.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  exact_mod_cast Nat.add_le_add_right hD 1

/-- A positive linear slack absorbs the explicit logarithmic and aggregate remainders. -/
theorem lt_size_of_sliceBound {A η θ C : ℝ} (hA : 0 < A) (hη : 0 ≤ η)
    (hηθ : η ≤ A ^ 2 * θ / 2) (hθ : 0 ≤ θ) (hθA : θ ≤ 1 / A) (hC : 0 ≤ C)
    {n g D K : Nat} (hK : 1 < K) (hslice : SliceBound A η C n g D K)
    (hlog : (A + η + 2) * D + (A + η + 3) * Real.logb 2 K +
      4 * Real.logb 2 n + (4 * Real.logb 2 (4 + 3 / A) + C + 4 * (A + η) + 11) <
        A * θ / 2 * n) : (1 + 1 / A - θ) * n < g := by
  by_contra! hsmall
  obtain ⟨m, hm, hmn, hdefnat, hcount⟩ := hslice
  have hn : 1 ≤ n := by lia
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (1 : ℝ) ≤ (n : ℝ) + 3 * g := by linarith [Nat.cast_nonneg (α := ℝ) g]
  have hAη : 0 ≤ A + η := by positivity
  have hlogK : 0 ≤ Real.logb 2 K := Real.logb_nonneg one_lt_two (by exact_mod_cast hK.le)
  have hclog : (Nat.clog 2 K : ℝ) < Real.logb 2 K + 1 := by
    rw [← Real.natCeil_logb_natCast 2 K]
    exact Nat.ceil_lt_add_one hlogK
  have hdef : (n : ℝ) - m ≤ D + Real.logb 2 K + 4 := by
    have hh : ((n - m : Nat) : ℝ) ≤ D + (Nat.clog 2 K : ℝ) + 3 := by
      exact_mod_cast hdefnat
    rw [Nat.cast_sub hmn] at hh
    linarith
  have hmax : max ((g : ℝ) - m) 0 ≤
      (1 / A - θ) * n + (D + Real.logb 2 K + 4) := by
    apply max_le
    · linarith
    · have := mul_nonneg (sub_nonneg.mpr hθA) (Nat.cast_nonneg (α := ℝ) n)
      positivity
  have hM : (0 : ℝ) < 4 + 3 / A := by positivity
  have hNpos : (0 : ℝ) < (n : ℝ) + 3 * g := by positivity
  have hNle : (n : ℝ) + 3 * g ≤ (4 + 3 / A) * n := by
    have hθn := mul_nonneg hθ (Nat.cast_nonneg (α := ℝ) n)
    simp only [div_eq_mul_inv, one_mul] at hsmall ⊢
    nlinarith
  have hlogN : Real.logb 2 ((n : ℝ) + 3 * g) ≤
      Real.logb 2 (4 + 3 / A) + Real.logb 2 n := by
    have h := (Real.logb_le_logb one_lt_two hNpos (by positivity)).mpr hNle
    rwa [Real.logb_mul hM.ne' (by positivity)] at h
  have hmbound := log_bound_of_count hAη hC hN (by lia : 0 < K) hcount
  have hBmax := mul_le_mul_of_nonneg_left hmax hAη
  have hmain : (n : ℝ) ≤ (A + η) * (1 / A - θ) * n +
      (A + η + 2) * D + (A + η + 3) * Real.logb 2 K +
        4 * Real.logb 2 n + (4 * Real.logb 2 (4 + 3 / A) + C + 4 * (A + η) + 11) := by
    nlinarith only [hmbound, hBmax, hdef, hlogN]
  have hηdiv : η / A ≤ A * θ / 2 := by
    apply (div_le_iff₀ hA).mpr
    nlinarith only [hηθ]
  have hAinv : A * (1 / A) = 1 := by field_simp
  have hcoef : (A + η) * (1 / A - θ) ≤ 1 - A * θ / 2 := by
    have hηθpos := mul_nonneg hη hθ
    simp only [div_eq_mul_inv, one_mul] at hAinv hηdiv ⊢
    nlinarith only [hAinv, hηdiv, hηθpos]
  have hcoefn := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hmain, hcoefn, hlog]

/-- Any family of circuit sizes admitting the finite slice estimate at every positive
ordering slack has leading coefficient `1 + 1/A` when its aggregate budget and logarithmic
rectangle threshold are sublinear. -/
theorem eventually_lt_size_of_sliceBound {A : ℝ} (hA : 0 < A)
    (Good : Nat → Nat → Prop) (D K : Nat → Nat)
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hKtwo : ∀ᶠ n in atTop, 1 < K n)
    (hslices : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ g, Good n g → SliceBound A η C n g (D n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g, Good n g → (1 + 1 / A - ε) * n < g := by
  let θ := min ε (1 / A)
  have hθ : 0 < θ := lt_min hε (by positivity)
  have hθA : θ ≤ 1 / A := min_le_right _ _
  have hθε : θ ≤ ε := min_le_left _ _
  let η := A ^ 2 * θ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hslice⟩ := hslices η hη
  have hB2 : 0 < A + η + 2 := by positivity
  have hB3 : 0 < A + η + 3 := by positivity
  have hDn := hD.def (by positivity : 0 < A * θ / (8 * (A + η + 2)))
  have hKn := hK.def (by positivity : 0 < A * θ / (8 * (A + η + 3)))
  have hlogn := eventually_mul_logb_add_lt 4
    (4 * Real.logb 2 (4 + 3 / A) + C + 4 * (A + η) + 11)
    (by positivity : 0 < A * θ / 4)
  filter_upwards [hslice, hDn, hKn, hlogn, hKtwo] with n hs hDn hKn hlogn hKtwo g hg
  have hDval : (D n : ℝ) ≤ A * θ / (8 * (A + η + 2)) * n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (D n)),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hDn
  have hKval : Real.logb 2 (K n) ≤ A * θ / (8 * (A + η + 3)) * n :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hKn)
  have hDscaled : (A + η + 2) * D n ≤ A * θ / 8 * n := by
    calc (A + η + 2) * D n ≤
        (A + η + 2) * (A * θ / (8 * (A + η + 2)) * n) :=
          mul_le_mul_of_nonneg_left hDval hB2.le
      _ = A * θ / 8 * n := by field_simp
  have hKscaled : (A + η + 3) * Real.logb 2 (K n) ≤ A * θ / 8 * n := by
    calc (A + η + 3) * Real.logb 2 (K n) ≤
        (A + η + 3) * (A * θ / (8 * (A + η + 3)) * n) :=
          mul_le_mul_of_nonneg_left hKval hB3.le
      _ = A * θ / 8 * n := by field_simp
  have key := lt_size_of_sliceBound hA hη.le (le_refl η) hθ.le hθA hC hKtwo
    (hs g hg) (by linarith :
      (A + η + 2) * D n + (A + η + 3) * Real.logb 2 (K n) +
        4 * Real.logb 2 n + (4 * Real.logb 2 (4 + 3 / A) + C + 4 * (A + η) + 11) <
          A * θ / 2 * n)
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 + 1 / A - ε ≤ 1 + 1 / A - θ)
    (Nat.cast_nonneg n)).trans_lt key

end Algebraic.Cutwidth.Aggregate

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Internal.Circuit
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Exponentially small correlation below `(1 + 1/(2A)) n` gates

Balance the two finite bounds at the threshold `θ n` unread inputs, where
`θ = (1/2 - A (c - 1)) / (1 + A)`:

* with at least `θ n` unread inputs, the correlation is at most `2^{-(θ - τ) n / 2 + O(1)}`;
* with fewer, the compiled network has cycle rank at most `(c - 1 + θ) n + 1`, a layout of
  width about `A (c - 1 + θ) n`, and the frontier bound gives the same exponent, since
  `A (c - 1 + θ) - 1/2 = -θ`.

So the correlation is `2^{-γ n}` for every `γ < (θ - τ)/2 = (c* - c)/(2L) - τ/2`, where
`c* = 1 + 1/(2A)` and `L = 1 + 1/A`.
-/

@[expose] public section

namespace Complexity.Correlation

open Set Filter Asymptotics Complexity.Frontier

universe v

/-- From a squared bound to an absolute bound with half the exponent. -/
theorem abs_le_two_rpow_of_sq_le {y γ : ℝ} {n : ℕ} (h : y ^ 2 ≤ (2 : ℝ) ^ (-(2 * γ) * n)) :
    |y| ≤ (2 : ℝ) ^ (-γ * n) := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have hsq : ((2 : ℝ) ^ (-γ * n)) ^ 2 = (2 : ℝ) ^ (-(2 * γ) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast
    ring_nf
  rw [hsq]
  exact h

/-- **Exponentially small correlation, rate form.** Under the layout hypothesis with
coefficient `A`, if every set of `⌊n/2⌋` coordinates has cut rank at least `⌊n/2⌋ - τ n`, then
every fan-in-two circuit with at most `c n` gates of positive arity, `c ≥ 1/2`, has correlation
at most `2^{-γ n}` with the quadratic form, for every `γ` with
`2 γ < (1/2 - A (c - 1)) / (1 + A) - τ` and all large `n`. -/
theorem eventually_abs_corr_le {A c τ γ : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hc : 1 / 2 ≤ c) (hγ : 2 * γ < (1 / 2 - A * (c - 1)) / (1 + A) - τ)
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ cutRank (Q n) U + τ * n) :
    ∀ᶠ n in atTop, ∀ (σ : Cslib.Circuits.Signature.{v})
      (I : Cslib.Circuits.Interpretation σ Bool) (C : Cslib.Circuits.Circuit σ n 1),
      C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |2 * agreement (quadForm (Q n)) (fun x => C.eval I x 0) - 1| ≤ (2 : ℝ) ^ (-γ * n) := by
  set θ := (1 / 2 - A * (c - 1)) / (1 + A) with hθdef
  have hθeq : A * (c - 1 + θ) - 1 / 2 = -θ := by
    rw [hθdef]
    field_simp
    ring
  have hθhalf : θ ≤ 1 / 2 := by
    rw [hθdef, div_le_iff₀ (by linarith)]
    nlinarith
  set δ := θ - τ - 2 * γ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set K := 5 * c + |θ| + 1 with hKdef
  have hK : 0 < K := by rw [hKdef]; have := abs_nonneg θ; linarith
  set η := δ / (2 * K) with hηdef
  have hη : 0 < η := by positivity
  have hηK : η * K = δ / 2 := by rw [hηdef]; field_simp
  have hηθ : η * (5 * c - 1 + θ) ≤ δ / 2 := by
    rw [← hηK]
    apply mul_le_mul_of_nonneg_left _ hη.le
    have := le_abs_self θ
    rw [hKdef]
    linarith
  obtain ⟨C₀, hC₀⟩ := hlayout η hη
  set R := (2 / δ) * (3 / 2 + A + 4 * η + |C₀|) with hRdef
  have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)
  filter_upwards [hQ, hlarge] with n hQn hRn
  intro σ I C hfan hsize
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hRn' : 3 / 2 + A + 4 * η + |C₀| ≤ δ / 2 * n := by
    have : δ / 2 * R = 3 / 2 + A + 4 * η + |C₀| := by rw [hRdef]; field_simp
    nlinarith
  have hC₀abs := le_abs_self C₀
  have hC₀nn := abs_nonneg C₀
  have hθn : θ * n ≤ 1 / 2 * n := mul_le_mul_of_nonneg_right hθhalf hn0
  apply abs_le_two_rpow_of_sq_le
  set N := constraintNetwork I {true} C
  set s := C.innerSize
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hcompl : (N.readᶜ.ncard : ℝ) + N.read.ncard = n := by
    have H := ncard_add_ncard_compl N.read
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at H
    have H' : (N.read.ncard : ℝ) + N.readᶜ.ncard = n := by exact_mod_cast H
    linarith
  have hhalf : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self n 2
  have hhalf' : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  by_cases hd : θ * n ≤ N.readᶜ.ncard
  · -- Many unread inputs.
    have H := sq_corr_le_of_unread I C (Q n) hQn (k := min N.readᶜ.ncard (n / 2))
      (min_le_right _ _) (min_le_left _ _)
    refine H.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hk : θ * n - 1 / 2 ≤ ((min N.readᶜ.ncard (n / 2) : ℕ) : ℝ) := by
      rcases min_choice N.readᶜ.ncard (n / 2) with h | h <;> rw [h]
      · linarith
      · linarith
    rw [hδdef] at hRn'
    linarith
  · -- Few unread inputs: the frontier bound.
    push Not at hd
    have hread : n / 2 ≤ N.read.ncard := by
      have : ((n / 2 : ℕ) : ℝ) < N.read.ncard := by linarith
      exact_mod_cast this.le
    have hrankNat := Compiler.cycleRank_add_ncard_read_le (out := C.outputs)
      I (fun _ => {true}) hfan (Compiler.connected I _)
    have hrank : (N.cycleRank : ℝ) + N.read.ncard ≤ s + 1 := by
      have H : N.cycleRank + N.read.ncard ≤ s + 1 := by
        simpa only [N, s, Cslib.Circuits.Circuit.innerSize, Nat.reduceSub, one_mul]
          using hrankNat
      exact_mod_cast H
    have hV : Nat.card (Compiler.Vertex C.program C.outputs) ≤ 4 * s + 3 := by
      simpa [s, Cslib.Circuits.Circuit.innerSize] using
        Compiler.card_vertex_le (out := C.outputs) hfan
    have hVreal : (Nat.card (Compiler.Vertex C.program C.outputs) : ℝ) ≤ 4 * s + 3 := by
      exact_mod_cast hV
    obtain ⟨π, hπ⟩ := hC₀ _ _ N.toMultigraph (Compiler.connected I _)
      (Compiler.loopless I _) (Compiler.maxDegreeLE I _ (by decide) hfan)
    set B := (A + η) * N.cycleRank + η * Nat.card (Compiler.Vertex C.program C.outputs) + C₀
    have hB : 0 ≤ B := by simpa [Layout.initial_zero] using hπ 0
    have hw : ∀ t, (N.frontier π t).ncard ≤ ⌊B⌋₊ := fun t => Nat.le_floor (hπ t)
    have H := sq_corr_le_of_layout I C (Q n) hQn π hw hread
    refine H.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
    have hcycle : (N.cycleRank : ℝ) ≤ (c - 1 + θ) * n + 1 := by
      have : (c - 1 + θ) * n = c * n - n + θ * n := by ring
      linarith
    have hcyc0 : (0 : ℝ) ≤ N.cycleRank := Nat.cast_nonneg _
    have hBle : B ≤ (A + η) * ((c - 1 + θ) * n + 1) + η * (4 * c * n + 3) + C₀ := by
      have h1 := mul_le_mul_of_nonneg_left hcycle (by positivity : (0 : ℝ) ≤ A + η)
      have h2 : η * (Nat.card (Compiler.Vertex C.program C.outputs) : ℝ) ≤
          η * (4 * c * n + 3) := by
        apply mul_le_mul_of_nonneg_left _ hη.le
        have : 4 * c * n = 4 * (c * n) := by ring
        linarith
      change (A + η) * N.cycleRank + η * Nat.card (Compiler.Vertex C.program C.outputs) + C₀ ≤ _
      linarith
    have hexp : (A + η) * ((c - 1 + θ) * n + 1) + η * (4 * c * n + 3) =
        (A * (c - 1 + θ) - 1 / 2) * n + n / 2 + η * (5 * c - 1 + θ) * n + A + 4 * η := by
      ring
    rw [hθeq] at hexp
    have hηθn := mul_le_mul_of_nonneg_right hηθ hn0
    rw [hδdef] at hRn' hηθn
    linarith

/-- **Exponentially small correlation, sublinear deficiency.** If every set of `⌊n/2⌋`
coordinates has cut rank at least `⌊n/2⌋ - o(n)`, the rate is every `γ` with
`2 γ < (1/2 - A (c - 1)) / (1 + A)`. -/
theorem eventually_abs_corr_le_of_isLittleO {A c γ : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hc : 1 / 2 ≤ c) (hγ : 2 * γ < (1 / 2 - A * (c - 1)) / (1 + A))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ cutRank (Q n) U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Cslib.Circuits.Signature.{v})
      (I : Cslib.Circuits.Interpretation σ Bool) (C : Cslib.Circuits.Circuit σ n 1),
      C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        |2 * agreement (quadForm (Q n)) (fun x => C.eval I x 0) - 1| ≤ (2 : ℝ) ^ (-γ * n) := by
  set τ := ((1 / 2 - A * (c - 1)) / (1 + A) - 2 * γ) / 2 with hτ
  have hτpos : 0 < τ := by rw [hτ]; linarith
  refine eventually_abs_corr_le hA hlayout hc (τ := τ) (by rw [hτ]; linarith) Q ?_
  filter_upwards [hQ, he.bound hτpos] with n hQn hen U hU
  have h1 := hQn U hU
  have h2 : e n ≤ τ * n := by
    have := le_abs_self (e n)
    simp only [Real.norm_eq_abs, Nat.abs_cast] at hen
    linarith
  linarith

end Complexity.Correlation

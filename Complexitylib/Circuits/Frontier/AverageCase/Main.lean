/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Circuit
public import Complexitylib.Circuits.Frontier.AverageCase.Asymptotics
public import Complexitylib.Circuits.Frontier.Layouts
import Mathlib.Tactic

/-!
# Average-case circuit lower bounds

Rectangle bias `2 b` bounds the agreement of circuits of size `(1 + 1/A - ε)n` by
`1/2 + b + 2^(-γ n)` for every `0 < γ < min(1, A ε)`. The theorem includes the compiler,
weighted peeling, unused inputs, and the layout comparison. Only the extractor's bias
hypothesis is external.
-/

@[expose] public section

namespace Complexity.Frontier

open Set Filter Asymptotics Cslib.Circuits

universe v

/-- **Average-case frontier lower bound.** Bias `2 b_n` on all sufficiently large coordinate
rectangles bounds agreement with every binary circuit a fixed linear distance below `L n`.
The exponential rate can be any `γ < min(1, A ε)`. -/
theorem averageCase {A ε γ : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hε : 0 < ε) (hγ1 : γ < 1) (hγε : γ < A * ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, RectangleBias (f n) (K n) (2 * b n)) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Circuit σ n 1),
      c.FanInAtMost 2 → (c.innerSize : ℝ) ≤ (1 + 1 / A - ε) * n →
        agreement (f n) (fun x => c.eval I x 0) ≤ 1 / 2 + b n + (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨η, hη, H⟩ := eventually_frontier_log_error hA hε hγ1 hγε K hK
  obtain ⟨C, hC⟩ := hlayout η hη
  filter_upwards [H C, hK2, hb, hf] with n hn hKn hbn hfn
  intro σ I c hfan hsize
  let N := constraintNetwork I {true} c
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast (show 0 < K n by lia)
  have hq : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  by_cases hu : K n ≤ 2 ^ N.readᶜ.ncard
  · have hlog : Real.logb 2 (2 * (K n : ℝ) ^ 2) ≤ (1 - γ) * n := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      simpa using hn.1
    have herr := div_two_pow_le_of_logb (by positivity) hlog
    have hbound := agreement_le_unused I c hfn hKn (by positivity) hu
    linarith
  · have hunread : (N.readᶜ.ncard : ℝ) < Real.logb 2 (K n) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) hKpos,
        Real.rpow_natCast]
      exact_mod_cast not_le.mp hu
    have hrankNat := Compiler.cycleRank_add_ncard_read_le (out := c.outputs)
      I (fun _ => {true}) hfan (Compiler.connected I _)
    have hrank : (N.cycleRank : ℝ) + N.read.ncard ≤ (c.innerSize : ℝ) + 1 := by
      have H : N.cycleRank + N.read.ncard ≤ c.innerSize + 1 := by
        simpa only [N, Circuit.innerSize, Nat.reduceSub, one_mul] using hrankNat
      exact_mod_cast H
    have hcompl : (N.readᶜ.ncard : ℝ) + N.read.ncard = n := by
      have H := ncard_add_ncard_compl N.read
      simpa [Nat.card_eq_fintype_card, add_comm] using congrArg (fun z : ℕ => (z : ℝ)) H
    have hcycle : (N.cycleRank : ℝ) ≤ c.innerSize - n + Real.logb 2 (K n) + 1 := by
      linarith
    have hV : Nat.card (Compiler.Vertex c.program c.outputs) ≤ 4 * c.innerSize + 3 := by
      simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
    have hVreal : (Nat.card (Compiler.Vertex c.program c.outputs) : ℝ) ≤
        4 * c.innerSize + 3 := by exact_mod_cast hV
    obtain ⟨π, hπ⟩ := hC _ _ N.toMultigraph (Compiler.connected I _)
      (Compiler.loopless I _) (Compiler.maxDegreeLE I _ (by decide) hfan)
    let B := (A + η) * N.cycleRank + η * Nat.card (Compiler.Vertex c.program c.outputs) + C
    have hB : 0 ≤ B := by simpa [Layout.initial_zero] using hπ 0
    let w := ⌊B⌋₊
    have hw : ∀ t, (N.frontier π t).ncard ≤ w := fun t => Nat.le_floor (hπ t)
    have hsupply : (w : ℝ) ≤ (A + η) *
        (c.innerSize - n + Real.logb 2 (K n) + 1) +
          η * Nat.card (Compiler.Vertex c.program c.outputs) + C := by
      have hfloor : (w : ℝ) ≤ B := Nat.floor_le hB
      have H := mul_le_mul_of_nonneg_left hcycle (by positivity : 0 ≤ A + η)
      dsimp [B] at hfloor
      linarith
    have hlog := hn.2 c.innerSize (Nat.card (Compiler.Vertex c.program c.outputs)) w
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsize hVreal hsupply
    let v := Nat.card (Compiler.Vertex c.program c.outputs)
    let T : ℝ := (K n : ℝ) ^ 3 * (v + 1) * (2 : ℝ) ^ (w + 4)
    have hTpos : 0 < T := by dsimp [T]; positivity
    have hlogT : Real.logb 2 T ≤ (1 - γ) * n := by
      dsimp [T]
      rw [Real.logb_mul (by positivity) (by positivity),
        Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      push_cast
      dsimp [v] at *
      linarith
    have herr := div_two_pow_le_of_logb hTpos hlogT
    have hres : (K n - 1) ^ 2 * (v * 2 ^ (w + 4) + 2 ^ N.readᶜ.ncard) ≤
        K n ^ 3 * (v + 1) * 2 ^ (w + 4) := by
      calc _ ≤ K n ^ 2 * (v * K n * 2 ^ (w + 4) + K n * 2 ^ (w + 4)) := by
            gcongr
            · lia
            · exact Nat.le_mul_of_pos_right _ (by lia)
            · exact (not_le.mp hu).le.trans (Nat.le_mul_of_pos_right _ (by positivity))
        _ = _ := by ring
    have hresR : (((K n - 1) ^ 2 * (v * 2 ^ (w + 4) + 2 ^ N.readᶜ.ncard) : ℕ) : ℝ) ≤ T := by
      dsimp [T]
      exact_mod_cast hres
    have hfrac := div_le_div_of_nonneg_right hresR (by positivity : 0 ≤ (2 : ℝ) ^ n)
    have hbound := agreement_le_layout I c hfn hKn (by positivity) hfan π hw
    linarith

/-- The same theorem bounds absolute signed correlation, with the correct normalization. -/
theorem averageCase_abs {A ε γ : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hε : 0 < ε) (hγ1 : γ < 1) (hγε : γ < A * ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, RectangleBias (f n) (K n) (2 * b n)) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Circuit σ n 1),
      c.FanInAtMost 2 → (c.innerSize : ℝ) ≤ (1 + 1 / A - ε) * n →
        |2 * agreement (f n) (fun x => c.eval I x 0) - 1| ≤
          2 * b n + 2 * (2 : ℝ) ^ (-γ * n) := by
  filter_upwards [averageCase hA hlayout hε hγ1 hγε f K b hK2 hK hb hf,
    averageCase hA hlayout hε hγ1 hγε (fun n x => !(f n x)) K b hK2 hK hb
      (hf.mono fun _ h => h.not)] with n hpos hneg
  intro σ I c hfan hs
  have hp := hpos σ I c hfan hs
  have hm := hneg σ I c hfan hs
  rw [agreement_not] at hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The Gaussian average-case bound.** At every fixed linear gap below
`L = 4.562497...`, rectangle bias `2 b_n` bounds agreement by `1/2 + b_n + 2^(-Ω(n))`. -/
theorem averageCase_gaussian {ε : ℝ} (hε : 0 < ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, RectangleBias (f n) (K n) (2 * b n)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Circuit σ n 1),
        c.FanInAtMost 2 →
        (c.innerSize : ℝ) ≤
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n →
        agreement (f n) (fun x => c.eval I x 0) ≤ 1 / 2 + b n + (2 : ℝ) ^ (-γ * n) := by
  let A := 2 * Algebraic.Cutwidth.Gaussian.frontierCoefficient
  have hA : 0 < A := two_mul_frontierCoefficient_pos
  let γ := min 1 (A * ε) / 2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ < 1 := by have := min_le_left (1 : ℝ) (A * ε); dsimp [γ]; linarith
  have hγε : γ < A * ε := by
    have := min_le_right (1 : ℝ) (A * ε)
    have := mul_pos hA hε
    dsimp [γ]
    linarith
  refine ⟨γ, hγ, ?_⟩
  have H := averageCase hA layoutBound_gaussian hε hγ1 hγε f K b hK2 hK hb hf
  dsimp [A] at H
  rwa [Algebraic.Cutwidth.Gaussian.one_add_inv_two_mul_frontierCoefficient] at H

end Complexity.Frontier

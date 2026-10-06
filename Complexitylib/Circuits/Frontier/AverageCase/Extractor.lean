/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Main
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Average-case hardness from sumset bias

The flat-source hypothesis below is the part of the sumset-extractor guarantee used by the
proof: independent uniform sources on any two sets of size at least `K` have XOR output bias
at most `β`. A one-bit extractor of statistical error `b` supplies `β = 2 b`.
No explicit extractor construction or polynomial-time evaluation is assumed to be formalized.
-/

@[expose] public section

namespace Complexity.Frontier

open Set Filter Asymptotics Cslib.Circuits

variable {α β ι : Type*}

private theorem sumOn_image [Finite α] [Finite β] (w : β → ℝ) (S : Set α)
    {g : α → β} (hg : Function.Injective g) :
    sumOn w (g '' S) = sumOn (fun x => w (g x)) S := by
  classical
  unfold sumOn
  rw [Set.Finite.toFinset_image g (toFinite S)]
  exact Finset.sum_image hg.injOn

private theorem sumOn_prod [Finite α] [Finite β] (w : α × β → ℝ) (A : Set α) (B : Set β) :
    sumOn w (A ×ˢ B) = sumOn (fun a => sumOn (fun b => w (a, b)) B) A := by
  unfold sumOn
  rw [← Set.Finite.toFinset_prod (toFinite A) (toFinite B)]
  exact Finset.sum_product _ _ _

/-- Coordinatewise XOR of two Boolean inputs. -/
def xorInputs (x y : ι → Bool) : ι → Bool := fun i => x i ^^ y i

/-- The signed-bias guarantee for sums of two independent uniform (flat) sources. -/
def FlatSumsetBias [Finite ι] (f : (ι → Bool) → Bool) (K : ℕ) (bias : ℝ) : Prop :=
  ∀ A B : Set (ι → Bool), K ≤ A.ncard → K ≤ B.ncard →
    |sumOn (fun x => sumOn (fun y => boolSign (f (xorInputs x y))) B) A| ≤
      bias * (A.ncard * B.ncard : ℕ)

/-- A Boolean partial input, extended by `false` outside its coordinates. -/
private noncomputable def xorPad (X : Set ι) (a : X → Bool) : ι → Bool :=
  open Classical in fun i => if h : i ∈ X then a ⟨i, h⟩ else false

private theorem xorPad_injective (X : Set ι) : Function.Injective (xorPad X) := by
  intro a b h
  funext i
  simpa [xorPad, i.2] using congrFun h i

private theorem restrict_xorPads (X : Set ι) (a : X → Bool) (b : ↥Xᶜ → Bool) :
    X.domRestrict (xorInputs (xorPad X a) (xorPad Xᶜ b)) = a ∧
      Xᶜ.domRestrict (xorInputs (xorPad X a) (xorPad Xᶜ b)) = b := by
  constructor
  · funext i
    simp [domRestrict, xorInputs, xorPad, i.2]
  · funext i
    have hi : (i : ι) ∉ X := i.2
    simp [domRestrict, xorInputs, xorPad, hi]

/-- Sumset bias implies the required coordinate-rectangle bias, without entropy loss. -/
theorem FlatSumsetBias.rectangleBias [Finite ι] {f : (ι → Bool) → Bool} {K : ℕ} {bias : ℝ}
    (hf : FlatSumsetBias f K bias) : RectangleBias f K bias := by
  intro X A B hA hB
  let glue := fun ab : (X → Bool) × (↥Xᶜ → Bool) => xorInputs (xorPad X ab.1) (xorPad Xᶜ ab.2)
  have hi : Function.Injective glue := by
    intro ab ab' h
    have h1 := congrArg X.domRestrict h
    have h2 := congrArg Xᶜ.domRestrict h
    rw [(restrict_xorPads X ab.1 ab.2).1, (restrict_xorPads X ab'.1 ab'.2).1] at h1
    rw [(restrict_xorPads X ab.1 ab.2).2, (restrict_xorPads X ab'.1 ab'.2).2] at h2
    exact Prod.ext h1 h2
  have himage : glue '' (A ×ˢ B) = rectangle X A B := by
    apply subset_antisymm
    · rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      change X.domRestrict (xorInputs (xorPad X a) (xorPad Xᶜ b)) ∈ A ∧
        Xᶜ.domRestrict (xorInputs (xorPad X a) (xorPad Xᶜ b)) ∈ B
      rw [(restrict_xorPads X a b).1, (restrict_xorPads X a b).2]
      exact ⟨ha, hb⟩
    · intro x hx
      refine ⟨⟨X.domRestrict x, Xᶜ.domRestrict x⟩, hx, ?_⟩
      exact eq_of_domRestrict_eq (restrict_xorPads X _ _).1 (restrict_xorPads X _ _).2
  have H := hf (xorPad X '' A) (xorPad Xᶜ '' B)
    (by rwa [ncard_image_of_injective _ (xorPad_injective X)])
    (by rwa [ncard_image_of_injective _ (xorPad_injective Xᶜ)])
  rw [sumOn_image _ _ (xorPad_injective X)] at H
  simp_rw [sumOn_image _ _ (xorPad_injective Xᶜ)] at H
  rw [ncard_image_of_injective _ (xorPad_injective X),
    ncard_image_of_injective _ (xorPad_injective Xᶜ)] at H
  rw [sumOn_const, ← himage, ncard_image_of_injective _ hi, ncard_prod,
    sumOn_image _ _ hi, sumOn_prod]
  exact H

universe v

/-- **Average-case lower bound for sumset extractors, in the flat-source form used here.** -/
theorem averageCase_sumset {ε : ℝ} (hε : 0 < ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, FlatSumsetBias (f n) (K n) (2 * b n)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Circuit σ n 1),
        c.FanInAtMost 2 →
        (c.innerSize : ℝ) ≤
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n →
        agreement (f n) (fun x => c.eval I x 0) ≤ 1 / 2 + b n + (2 : ℝ) ^ (-γ * n) :=
  averageCase_gaussian hε f K b hK2 hK hb (hf.mono fun _ h => h.rectangleBias)

/-- Polynomially small extractor error gives polynomially small agreement advantage.
The entropy hypothesis is still only `log K = o(n)`, allowing polylogarithmic entropy.
The exponent `α` may be any real number; a positive exponent gives the intended decay. -/
theorem averageCase_sumset_polynomial {ε : ℝ} (hε : 0 < ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, FlatSumsetBias (f n) (K n) (2 * b n))
    {α C : ℝ} (hpoly : ∀ᶠ n in atTop, b n ≤ C * (n : ℝ) ^ (-α)) :
    ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Circuit σ n 1),
        c.FanInAtMost 2 →
        (c.innerSize : ℝ) ≤
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n →
        agreement (f n) (fun x => c.eval I x 0) ≤
          1 / 2 + (C + 1) * (n : ℝ) ^ (-α) := by
  obtain ⟨γ, hγ, h⟩ := averageCase_sumset hε f K b hK2 hK hb hf
  have hdecay := (isLittleO_exp_neg_mul_rpow_atTop
    (mul_pos hγ (Real.log_pos (by norm_num : (1 : ℝ) < 2))) (-α)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [h, hpoly, hdecay.bound (by norm_num : (0 : ℝ) < 1)] with n hn hbnd hexp
  intro σ I c hfan hsize
  have htail : (2 : ℝ) ^ (-γ * n) ≤ (n : ℝ) ^ (-α) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), one_mul,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      show Real.log 2 * (-γ * n) = -(γ * Real.log 2) * n by ring] using hexp
  linarith [hn σ I c hfan hsize]

end Complexity.Frontier

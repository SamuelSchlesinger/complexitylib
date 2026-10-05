/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Main

/-!
# Hard sets from sumset dispersers

The lower bound needs dense rectangle-free sets. Over an alphabet `U` with an addition, a
rectangle is a *sumset*: an input whose part on `X` lies in `A` and whose part on the complement
of `X` lies in `B` is the sum `a + b` of the input `a` that agrees with it on `X` and vanishes
elsewhere, and the input `b` that agrees with it off `X` and vanishes on `X`. So a function that
is not constant on any sumset `A + B` of two large sets of inputs has rectangle-free fibers
(`Frontier.SumsetDisperser.rectangleFree`).

Such functions are *sumset dispersers*. A *sumset extractor* is better: its output on `X + Y`, for
independent random inputs `X` and `Y` with enough min-entropy, is close to uniform. An extractor
with error less than `1/2` disperses sumsets. Over a finite additive group its fibers are
dense, since `X + Y` is uniform when `X` and `Y` are.

For `U = {0, 1}` with addition modulo two, polynomial-time computable extractors for the sum of
two independent sources of min-entropy `c log n` are known (Xin Li, *Two source extractors for
asymptotically optimal entropy, and (many) more*, FOCS 2023, Theorem 7.13). Their fibers are dense
and `n^c`-rectangle-free, so `Frontier.lowerBound_sumsetDisperser` applies to them: there is a
language in `P` whose circuits of fan-in two over any binary basis need `(L - ε) n` gates, with
`L ≈ 4.5625`. The extractor itself is not formalized here.

## Main definitions

* `Frontier.SumsetDisperser f K`: `f` takes both values on every sumset of two sets of size
  at least `K`.

## Main results

* `Frontier.SumsetDisperser.rectangleFree`: the fibers of a sumset disperser are rectangle-free.
* `Frontier.lowerBound_sumsetDisperser`: the `(L - ε) n` lower bound for balanced sumset
  dispersers.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Set Filter Asymptotics

variable {ι U : Type*}

/-- A function `f` *disperses sumsets* of size `K` when it takes both values on the sumset
`A + B` of any two sets of inputs with at least `K` elements each. -/
def SumsetDisperser [Add U] (f : (ι → U) → Bool) (K : ℕ) : Prop :=
  ∀ A B : Set (ι → U), K ≤ A.ncard → K ≤ B.ncard → ∀ b : Bool, ∃ x ∈ A, ∃ y ∈ B, f (x + y) ≠ b

/-- The input that agrees with `a` on `X` and vanishes elsewhere. -/
noncomputable def pad [Zero U] (X : Set ι) (a : X → U) : ι → U :=
  open Classical in fun i => if h : i ∈ X then a ⟨i, h⟩ else 0

theorem pad_injective [Zero U] (X : Set ι) : Function.Injective (pad (U := U) X) := by
  intro a a' h
  funext i
  have := congrFun h i
  simpa [pad, i.2] using this

theorem domRestrict_pad_add_pad [AddZeroClass U] (X : Set ι) (a : X → U) (b : ↥Xᶜ → U) :
    X.domRestrict (pad X a + pad Xᶜ b) = a ∧ Xᶜ.domRestrict (pad X a + pad Xᶜ b) = b := by
  constructor <;> funext i
  · have : (i : ι) ∉ Xᶜ := fun h => h i.2
    simp [domRestrict, pad, i.2, this]
  · have : (i : ι) ∉ X := i.2
    simp [domRestrict, pad, i.2, this]

/-- **The fibers of a sumset disperser are rectangle-free.** A rectangle with sides `A` and `B`
is the sumset of the inputs supported on `X` with parts in `A` and those supported off `X` with
parts in `B`. -/
theorem SumsetDisperser.rectangleFree [AddZeroClass U] {f : (ι → U) → Bool} {K : ℕ}
    (hf : SumsetDisperser f K) (b : Bool) : RectangleFree {x | f x = b} K := by
  intro X A B hAB
  by_contra! h
  obtain ⟨hA, hB⟩ := h
  obtain ⟨x, ⟨a, ha, rfl⟩, y, ⟨b', hb', rfl⟩, hne⟩ := hf (pad X '' A) (pad Xᶜ '' B)
    (by rwa [ncard_image_of_injective _ (pad_injective X)])
    (by rwa [ncard_image_of_injective _ (pad_injective Xᶜ)]) b
  have hmem : pad X a + pad Xᶜ b' ∈ rectangle X A B := by
    obtain ⟨h₁, h₂⟩ := domRestrict_pad_add_pad X a b'
    rw [mem_rectangle, h₁, h₂]
    exact ⟨ha, hb'⟩
  exact hne (hAB hmem)

/-- A set containing at least a fixed fraction of all inputs is dense:
`n log |U| - log |S_n| = O(1)`. -/
theorem isLittleO_of_card_le [Finite U] [Nonempty U] (S : ∀ n, Set (Fin n → U)) {δ : ℝ}
    (hδ : 0 < δ) (hS : ∀ᶠ n in atTop, δ * (Nat.card U : ℝ) ^ n ≤ (S n).ncard) :
    (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop] fun n => (n : ℝ) := by
  have hq : (0 : ℝ) < Nat.card U := by exact_mod_cast Nat.card_pos
  have hbound : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =O[atTop]
      fun _ : ℕ => (1 : ℝ) := by
    refine IsBigO.of_bound (|Real.log δ|) ?_
    filter_upwards [hS] with n hn
    have hpos : 0 < ((S n).ncard : ℝ) := lt_of_lt_of_le (by positivity) hn
    have hle : ((S n).ncard : ℝ) ≤ (Nat.card U : ℝ) ^ n := by
      have := ncard_le_card (S n)
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
      exact_mod_cast this
    have h1 : Real.log (S n).ncard ≤ n * Real.log (Nat.card U) := by
      rw [← Real.log_pow]; exact Real.log_le_log hpos hle
    have h2 : Real.log δ + n * Real.log (Nat.card U) ≤ Real.log (S n).ncard := by
      rw [← Real.log_pow, ← Real.log_mul hδ.ne' (by positivity)]
      exact Real.log_le_log (by positivity) hn
    rw [Real.norm_eq_abs, norm_one, mul_one, abs_of_nonneg (by linarith)]
    linarith [neg_abs_le (Real.log δ)]
  exact hbound.trans_isLittleO (isLittleO_const_left.mpr
    (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)))

universe u v

/-- **The `(L - ε) n` lower bound for sumset dispersers.** Let `f_n` be functions on `U^n`, over
a finite alphabet with an addition, that disperse sumsets of size `K_n` with `log K_n = o(n)` and
take the value `true` on at least a fixed fraction `δ > 0` of all inputs. Then for every `ε > 0`
and all large `n`, every circuit of fan-in two over any basis on `U` deciding where `f_n` is
`true` has more than `(L - ε) n` gates, with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem lowerBound_sumsetDisperser {U : Type u} [AddZeroClass U] [Finite U] [Nontrivial U]
    (f : ∀ n, (Fin n → U) → Bool) (K : ℕ → ℕ) (hf : ∀ᶠ n in atTop, SumsetDisperser (f n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hbal : ∀ᶠ n in atTop, δ * (Nat.card U : ℝ) ^ n ≤ {x | f n x = true}.ncard) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc {x | f n x = true} →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n < c.size := by
  filter_upwards [lowerBound_gaussian (fun n => {x | f n x = true}) K
    (hf.mono fun n hn => hn.rectangleFree true) hK (isLittleO_of_card_le _ hδ hbal) hε] with n hn
  intro σ I Acc c hfan hS
  exact (hn σ I Acc c hfan hS).trans_le (by exact_mod_cast c.innerSize_le_size)

end Complexity.Frontier

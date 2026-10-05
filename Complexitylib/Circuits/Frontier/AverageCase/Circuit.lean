/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Network
public import Complexitylib.Circuits.Frontier.AverageCase.Bias
public import Complexitylib.Circuits.Frontier.Reduction
import Mathlib.Tactic

/-! # Finite average-case circuit bounds -/

@[expose] public section

namespace Complexity.Frontier

open Set Cslib.Circuits

variable {σ : Signature} {n : ℕ} (I : Interpretation σ Bool) (c : Circuit σ n 1)

private theorem accepted_output_class (b : Bool) :
    (constraintNetwork I {b} c).accepted = {x | c.eval I x 0 = b} :=
  accepted_constraintNetwork (fun _ => Iff.rfl)

/-- Bias on the two output classes is bounded by the size of any frontier layout. -/
theorem agreement_le_layout {f : (Fin n → Bool) → Bool} {K : ℕ} {β : ℝ}
    (hf : RectangleBias f K β) (hK : 1 < K) (hβ : 0 ≤ β) (hfan : c.FanInAtMost 2)
    (π : Layout (Compiler.Vertex c.program c.outputs)) {w : ℕ}
    (hw : ∀ t, ((constraintNetwork I {true} c).frontier π t).ncard ≤ w) :
    agreement f (fun x => c.eval I x 0) ≤ (1 + β) / 2 +
      (((K - 1) ^ 2 * (Nat.card (Compiler.Vertex c.program c.outputs) * 2 ^ (w + 4) +
        2 ^ (constraintNetwork I {true} c).readᶜ.ncard) : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  have hq : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  have H := agreement_le_of_output_bias f (fun x => c.eval I x 0)
    (R := (((K - 1) ^ 2 * (Nat.card (Compiler.Vertex c.program c.outputs) * 2 ^ (w + 4) +
      2 ^ (constraintNetwork I {true} c).readᶜ.ncard) : ℕ) : ℝ)) (β := β) fun b => by
    have Hu : ∀ x α β, (constraintNetwork I {b} c).Satisfies x α →
        (constraintNetwork I {b} c).Satisfies x β → α = β := by
      intro x α β hα hβ
      exact funext fun e => (Compiler.eq_trace hα e).trans (Compiler.eq_trace hβ e).symm
    have Hb := (constraintNetwork I {b} c).abs_sumOn_accepted_le π Hu hK hK
      (a := 1) (by norm_num) (fun x => (abs_boolSign (f x)).le) (fun _ => hβ) hf
      (w := w) (d := 3) (m := 1) hw
      (Compiler.maxDegreeLE I (fun _ => {b}) (by decide) hfan)
      (Compiler.ncard_readAt_le I (fun _ => {b}))
    have hr : (constraintNetwork I {b} c).read = (constraintNetwork I {true} c).read := by
      simp only [constraintNetwork, Compiler.read_network]
    rw [accepted_output_class I c b, sumOn_const, hq, hr] at Hb
    simpa only [one_mul, sq, show w + 3 + 1 = w + 4 by lia] using Hb
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using H

/-- A circuit with many unread inputs has negligible advantage beyond the rectangle bias. -/
theorem agreement_le_unused {f : (Fin n → Bool) → Bool} {K : ℕ} {β : ℝ}
    (hf : RectangleBias f K β) (hK : 1 < K) (hβ : 0 ≤ β)
    (hu : K ≤ 2 ^ (constraintNetwork I {true} c).readᶜ.ncard) :
    agreement f (fun x => c.eval I x 0) ≤ (1 + β) / 2 +
      (2 * (K : ℝ) ^ 2) / (2 : ℝ) ^ n := by
  have hq : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  have H := agreement_le_of_output_bias f (fun x => c.eval I x 0)
    (R := 2 * (K : ℝ) ^ 2) (β := β) fun b => by
    have hdep := (constraintNetwork I {b} c).dependsOn_read
    rw [accepted_output_class I c b] at hdep
    have hr : (constraintNetwork I {b} c).read = (constraintNetwork I {true} c).read := by
      simp only [constraintNetwork, Compiler.read_network]
    have Hb := hf.abs_sumOn_le_of_dependsOn hK hβ hdep (by simpa only [hq, hr] using hu)
    simpa only [hq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using Hb
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using H

end Complexity.Frontier

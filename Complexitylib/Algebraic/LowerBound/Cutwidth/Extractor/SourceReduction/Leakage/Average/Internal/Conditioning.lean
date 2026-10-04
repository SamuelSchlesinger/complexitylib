/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Internal
import Mathlib.Tactic.NormNum

/-!
# Conditioning on all deterministic seed leakage

The observation graph keeps every original source occurrence. Its conditional
rows have the existing normalized completion at null events, and multiplying
by the observation marginal recovers the exact original mass. These identities
implement the conditioning step in Chattopadhyay--Liao, Lemma 5.3, printed
pp.19--20: <https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem leakageConditioning_factor {X Z : Type*} [Fintype X]
    (p : X → ℝ) (leak : X → Z) (nonnegative : ∀ x, 0 ≤ p x) (z : Z) (x : X) :
    mapWeight leak p z * conditionalWeight (mapWeight (fun x => (leak x, x)) p) z x =
      if leak x = z then p x else 0 := by
  rw [← transcript_graph_first p leak]
  rw [conditionalWeight_factor _ (fun zx => by
    rw [transcript_map_graph]
    split_ifs <;> first | exact nonnegative _ | exact le_rfl)]
  exact transcript_map_graph p leak z x

theorem leakageConditioning_factored {X Z Y : Type*}
    [Fintype X] [Fintype Y]
    (p : X → ℝ) (leak : X → Z) (right : Y → ℝ) (nonnegative : ∀ x, 0 ≤ p x) :
    mapWeight (fun yx : Y × X => ((leak yx.2, yx.1), yx.2))
      (fun yx => right yx.1 * p yx.2) =
      factoredWeight (mapWeight leak p)
        (conditionalWeight (mapWeight (fun x => (leak x, x)) p)) (fun _ => right) := by
  funext zyx
  rcases zyx with ⟨⟨z, y⟩, x⟩
  rw [factoredWeight, mul_right_comm,
    leakageConditioning_factor p leak nonnegative]
  simp only [mapWeight, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, and_comm (a := _ = y), ite_and]
  simp only [mul_comm, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_eq_single x]
  · simp
  · intro a _ different
    simp [different]
  · simp

theorem leakage_map_tagged {Y X A B : Type*} [Fintype Y] [Fintype X]
    (w : Y → ℝ) (p : X → ℝ) (f : Y → X → A × B) :
    mapWeight (fun yx : Y × X => ((yx.1, (f yx.1 yx.2).1), (f yx.1 yx.2).2))
      (fun yx => w yx.1 * p yx.2) =
        fun yab : (Y × A) × B => w yab.1.1 * mapWeight (f yab.1.1) p (yab.1.2, yab.2) := by
  funext yab
  rcases yab with ⟨⟨y, a⟩, b⟩
  simp only [mapWeight, Fintype.sum_prod_type, Prod.mk.injEq, and_assoc, ite_and]
  simp [Finset.mul_sum, mul_ite]
  simp only [Prod.ext_iff, ite_and]

theorem leakage_xor_uniform {d : Nat} (z : Fin d → Bool) :
    mapWeight (fun y => xorInput y z) (uniformWeight (Fin d → Bool)) =
      uniformWeight (Fin d → Bool) := by
  let e : (Fin d → Bool) ≃ (Fin d → Bool) :=
    { toFun := fun y => xorInput y z
      invFun := fun y => xorInput y z
      left_inv := fun y => by funext i; simp [xorInput]
      right_inv := fun y => by funext i; simp [xorInput] }
  funext y
  change mapWeight e (uniformWeight (Fin d → Bool)) y = _
  rw [mapWeight_equiv_apply]
  rfl

theorem leakage_envelope_sum (t d k : Nat) :
    (∑ _ : Option (Fin t) → Fin d → Bool, ((2 : ℝ) ^ (k + (t + 1) * d))⁻¹) =
      ((2 : ℝ) ^ k)⁻¹ := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Fintype.card_option, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm d (t + 1), pow_add, mul_inv_rev]
  have positive : (2 : ℝ) ^ ((t + 1) * d) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [← mul_assoc, mul_inv_cancel₀ positive, one_mul]

end Algebraic.Cutwidth.Extractor.Internal

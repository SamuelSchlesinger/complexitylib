/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Hash
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin

/-!
# Unrestricted depth-three lower bound: hash triangular

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HashTriangular.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound.BinaryHash

open scoped BigOperators

theorem exists_last_nonzero {d : ℕ} (w : Data d) (hw : w ≠ 0) :
    ∃ s : Fin d, w s ≠ 0 ∧ ∀ a : Fin d, s.val < a.val → w a = 0 := by
  classical
  have hex : ∃ a : Fin d, w a ≠ 0 := by
    by_contra h
    apply hw
    funext a
    by_contra ha
    exact h ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun a : Fin d => w a ≠ 0) Fin.val
      ⟨a, by simp [ha]⟩
  refine ⟨s, (Finset.mem_filter.mp hs).2, ?_⟩
  intro b hsb
  by_contra hb
  have hle := hmax b (by simp [hb])
  omega

/-- The last nonzero coordinate used as a pivot in the hash argument. -/
noncomputable def lastIndex {d : ℕ} (w : Data d) (hw : w ≠ 0) : Fin d :=
  (exists_last_nonzero w hw).choose

theorem lastIndex_nonzero {d : ℕ} (w : Data d) (hw : w ≠ 0) :
    w (lastIndex w hw) ≠ 0 :=
  (exists_last_nonzero w hw).choose_spec.1

theorem zero_after_lastIndex {d : ℕ} (w : Data d) (hw : w ≠ 0)
    (a : Fin d) (ha : (lastIndex w hw).val < a.val) : w a = 0 :=
  (exists_last_nonzero w hw).choose_spec.2 a ha

theorem data_dim_pos {d : ℕ} (w : Data d) (hw : w ≠ 0) : 0 < d :=
  Nat.zero_le (lastIndex w hw).val |>.trans_lt (lastIndex w hw).isLt

/-- Seed positions other than the chosen pivot positions. -/
def Nonpivot {d r : ℕ} (w : Data d) (hw : w ≠ 0) :=
  {j : Fin (d + r - 1) // ¬ ∃ i : Fin r, sumIndex i (lastIndex w hw) = j}

noncomputable instance {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Fintype (Nonpivot (r := r) w hw) := by
  classical
  unfold Nonpivot
  infer_instance

theorem card_nonpivot {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Fintype.card (Nonpivot (r := r) w hw) = d - 1 := by
  classical
  have hp : Fintype.card
      {j : Fin (d + r - 1) // ∃ i : Fin r, sumIndex i (lastIndex w hw) = j} = r := by
    let e : Fin r ≃
        {j : Fin (d + r - 1) // ∃ i : Fin r, sumIndex i (lastIndex w hw) = j} :=
      Equiv.ofInjective (fun i : Fin r => sumIndex i (lastIndex w hw))
        (sumIndex_left_injective (lastIndex w hw))
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  calc
    Fintype.card (Nonpivot (r := r) w hw) = Fintype.card
        {j : Fin (d + r - 1) // ¬ ∃ i : Fin r, sumIndex i (lastIndex w hw) = j} :=
      Fintype.card_congr (Equiv.refl _)
    _ = (d + r - 1) - r := by
      rw [Fintype.card_subtype_compl, hp, Fintype.card_fin]
    _ = d - 1 := by
      have hd := data_dim_pos w hw
      omega

/-- The triangular coordinate map used to solve the hash equations. -/
def triangularMap {d r : ℕ} (w : Data d) (hw : w ≠ 0) (u : Seed d r) :
    Output r × (Nonpivot (r := r) w hw → F2) :=
  (hashF2 u w, fun j => u j.val)

theorem triangularMap_injective {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Function.Injective (triangularMap (r := r) w hw) := by
  classical
  intro u v huv
  have hhash : hashF2 u w = hashF2 v w := congrArg Prod.fst huv
  have hfree : (fun j : Nonpivot (r := r) w hw => u j.val) =
      (fun j : Nonpivot (r := r) w hw => v j.val) := congrArg Prod.snd huv
  have heq : ∀ n : ℕ, ∀ j : Fin (d + r - 1), j.val = n → u j = v j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hp : ∃ i : Fin r, sumIndex i (lastIndex w hw) = j
      · obtain ⟨i, rfl⟩ := hp
        have hrow : (∑ a : Fin d,
            (u (sumIndex i a) - v (sumIndex i a)) * w a) = 0 := by
          calc
            (∑ a : Fin d, (u (sumIndex i a) - v (sumIndex i a)) * w a) =
                hashF2 u w i - hashF2 v w i := by
                  simp only [hashF2, sub_mul, Finset.sum_sub_distrib]
            _ = 0 := sub_eq_zero.mpr (congrFun hhash i)
        have hsingle : (∑ a : Fin d,
            (u (sumIndex i a) - v (sumIndex i a)) * w a) =
            (u (sumIndex i (lastIndex w hw)) -
              v (sumIndex i (lastIndex w hw))) * w (lastIndex w hw) := by
          apply Finset.sum_eq_single_of_mem (lastIndex w hw) (Finset.mem_univ _)
          intro a _ ha
          by_cases hlt : a.val < (lastIndex w hw).val
          · have hidx : (sumIndex i a).val < n := by
              simp only [sumIndex_val] at hj ⊢
              omega
            rw [ih (sumIndex i a).val hidx (sumIndex i a) rfl, sub_self, zero_mul]
          · have hne : a.val ≠ (lastIndex w hw).val := by
              intro he
              exact ha (Fin.ext he)
            have hgt : (lastIndex w hw).val < a.val := by omega
            rw [zero_after_lastIndex w hw a hgt, mul_zero]
        rw [hsingle] at hrow
        exact sub_eq_zero.mp ((mul_eq_zero.mp hrow).resolve_right (lastIndex_nonzero w hw))
      · exact congrFun hfree ⟨j, hp⟩
  exact funext fun j => heq j.val j rfl

theorem triangularMap_bijective {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Function.Bijective (triangularMap (r := r) w hw) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨triangularMap_injective w hw, ?_⟩
  have hd := data_dim_pos w hw
  simp only [Seed, Output, Fintype.card_prod, Fintype.card_fun,
    F2, BinaryAlgebra.F2, ZMod.card, Fintype.card_fin, card_nonpivot]
  rw [← pow_add]
  congr 1
  omega

/-- Invert the triangular map by solving for the pivot coordinates. -/
noncomputable def triangularEquiv {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Seed d r ≃ Output r × (Nonpivot (r := r) w hw → F2) :=
  Equiv.ofBijective (triangularMap w hw) (triangularMap_bijective w hw)

@[simp] theorem triangularEquiv_fst {d r : ℕ} (w : Data d) (hw : w ≠ 0)
    (u : Seed d r) : (triangularEquiv w hw u).1 = hashF2 u w := rfl

@[simp] theorem triangularEquiv_snd {d r : ℕ} (w : Data d) (hw : w ≠ 0)
    (u : Seed d r) (j : Nonpivot (r := r) w hw) :
    (triangularEquiv w hw u).2 j = u j.val := rfl

end DepthThreeLowerBound.BinaryHash

end Complexity

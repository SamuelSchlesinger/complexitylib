/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Internal.Degree
public import Complexitylib.Circuits.XOR
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Parity is hard to approximate by low-degree functions over `ZMod 3`

Write `yᵢ = 1 + xᵢ ∈ {1, -1} ⊆ ZMod 3`, so that `∏ᵢ yᵢ = (-1)^{|x|}` is parity in
`±1` form and every `yᵢ² = 1`. If a degree-`D` function `Q` agrees with `∏ᵢ yᵢ` on
a set `G`, then on `G` every `y`-monomial `y_S` with `|S| > n/2` equals
`Q · y_{Sᶜ}`, of degree at most `D + n/2`. Since the `y`-monomials span all
functions, every function `G → ZMod 3` is the restriction of a function of
degree at most `n/2 + D`. Comparing cardinalities, `3^{|G|}` is at most `3` to
the number of monomials of at most `n/2 + D` coordinates.
-/


public section

namespace Complexity

namespace Smolensky

open Finset

variable {n : ℕ}

/-- The product of the `±1` variables `yᵢ = 1 + xᵢ` over `S`. -/
def signMonomial (S : Finset (Fin n)) (x : BitString n) : ZMod 3 :=
  ∏ i ∈ S, (1 + bitVal (x i))

/-- The span of the `±1` monomials of at most `H` coordinates. -/
def signSpan (n H : ℕ) : Submodule (ZMod 3) (BitString n → ZMod 3) :=
  Submodule.span (ZMod 3) (signMonomial '' {S | S.card ≤ H})

theorem signMonomial_mem_lowDegree (S : Finset (Fin n)) :
    signMonomial S ∈ lowDegree n S.card := by
  have hfun : signMonomial S = ∏ i ∈ S, (1 + fun x : BitString n => bitVal (x i)) := by
    funext x
    simp [signMonomial, Finset.prod_apply]
  rw [hfun]
  simpa using prod_mem_lowDegree S _ (a := 1) fun i _ =>
    Submodule.add_mem _ (one_mem_lowDegree 1) (bitVal_mem_lowDegree i)

theorem one_add_bitVal_sq (b : Bool) : (1 + bitVal b) ^ 2 = 1 := by
  cases b <;> decide

theorem signMonomial_sq (S : Finset (Fin n)) (x : BitString n) :
    signMonomial S x ^ 2 = 1 := by
  rw [signMonomial, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => one_add_bitVal_sq (x i)

theorem signMonomial_mul_compl (S : Finset (Fin n)) (x : BitString n) :
    signMonomial S x * signMonomial Sᶜ x = signMonomial univ x :=
  Finset.prod_mul_prod_compl S _

theorem one_add_bitVal_mul (a b : Bool) :
    (1 + bitVal a) * (1 + bitVal b) = 1 + bitVal (a.xor b) := by
  cases a <;> cases b <;> decide

/-- The product of all `±1` variables is parity in `±1` form. -/
theorem signMonomial_univ (x : BitString n) :
    signMonomial univ x = 1 + bitVal (Schnorr.xorBool n x) := by
  induction n with
  | zero => simp [signMonomial, Schnorr.xorBool, bitVal_false]
  | succ n ih =>
    rw [signMonomial, Fin.prod_univ_succ]
    have htail := ih (x ∘ Fin.succ)
    simp only [signMonomial, Function.comp_apply] at htail
    rw [htail, one_add_bitVal_mul]
    rfl

/-- Every function on the cube has degree at most `n`. -/
theorem mem_lowDegree_self (f : BitString n → ZMod 3) : f ∈ lowDegree n n := by
  classical
  have hind : ∀ a : BitString n,
      (fun x : BitString n => if x = a then (1 : ZMod 3) else 0) ∈ lowDegree n n := by
    intro a
    have hfactor : ∀ (x : BitString n) (i : Fin n),
        (if a i then bitVal (x i) else 1 - bitVal (x i)) =
          if x i = a i then 1 else 0 := by
      intro x i
      cases a i <;> cases x i <;> decide
    have hfun : (fun x : BitString n => if x = a then (1 : ZMod 3) else 0) =
        ∏ i : Fin n, fun x : BitString n =>
          if a i then bitVal (x i) else 1 - bitVal (x i) := by
      funext x
      rw [Finset.prod_apply]
      simp only [hfactor x, Finset.prod_boole, Finset.mem_univ, true_implies]
      simp only [funext_iff]
    rw [hfun]
    have hmem := prod_mem_lowDegree (n := n) univ
      (fun i x => if a i then bitVal (x i) else 1 - bitVal (x i)) (a := 1) fun i _ => by
        by_cases h : a i
        · simpa [h] using bitVal_mem_lowDegree i
        · simp only [h, Bool.false_eq_true, ite_false]
          exact one_sub_mem_lowDegree (bitVal_mem_lowDegree i)
    simpa using hmem
  have hsum : f = ∑ a, f a • fun x : BitString n => if x = a then (1 : ZMod 3) else 0 := by
    funext x
    simp [Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hind a)

theorem signSpan_mono {H K : ℕ} (hHK : H ≤ K) : signSpan n H ≤ signSpan n K :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans hS hHK)

/-- Each monomial expands into `±1` monomials of its subsets. -/
theorem monomial_mem_signSpan (S : Finset (Fin n)) : monomial S ∈ signSpan n S.card := by
  classical
  have hfun : monomial S =
      ∑ T ∈ S.powerset, ((-1 : ZMod 3) ^ (S \ T).card) • signMonomial T := by
    funext x
    simp only [monomial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, signMonomial]
    have hsplit : ∏ i ∈ S, bitVal (x i) = ∏ i ∈ S, ((1 + bitVal (x i)) + (-1)) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [hsplit, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const, mul_comm]
  rw [hfun]
  exact Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨T, Finset.card_le_card (Finset.mem_powerset.mp hT), rfl⟩)

theorem lowDegree_le_signSpan (H : ℕ) : lowDegree n H ≤ signSpan n H := by
  rw [lowDegree, Submodule.span_le]
  rintro _ ⟨S, hS, rfl⟩
  exact signSpan_mono hS (monomial_mem_signSpan S)

/-- If `Q` has degree at most `D` and agrees with the `±1` parity on `G`, every
function agrees on `G` with a function of degree at most `n / 2 + D`. -/
theorem exists_agree_of_parity {D : ℕ} {Q : BitString n → ZMod 3}
    (hQ : Q ∈ lowDegree n D) (G : Finset (BitString n))
    (hG : ∀ x ∈ G, Q x = signMonomial univ x) (f : BitString n → ZMod 3) :
    ∃ p ∈ lowDegree n (n / 2 + D), ∀ x ∈ G, p x = f x := by
  have hf : f ∈ signSpan n n := lowDegree_le_signSpan n (mem_lowDegree_self f)
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, -, rfl⟩ := hg
    by_cases hS : S.card ≤ n / 2
    · exact ⟨signMonomial S,
        mem_lowDegree_of_le (signMonomial_mem_lowDegree S) (by omega), fun _ _ => rfl⟩
    · refine ⟨Q * signMonomial Sᶜ, ?_, fun x hx => ?_⟩
      · have hc : Sᶜ.card ≤ n / 2 := by
          rw [Finset.card_compl, Fintype.card_fin]
          omega
        exact mem_lowDegree_of_le
          (mul_mem_lowDegree hQ (signMonomial_mem_lowDegree Sᶜ)) (by omega)
      · rw [Pi.mul_apply, hG x hx, ← signMonomial_mul_compl S x, mul_assoc, ← sq,
          signMonomial_sq, mul_one]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp, hpx⟩ := hf
    obtain ⟨q, hq, hqx⟩ := hg
    exact ⟨p + q, Submodule.add_mem _ hp hq, fun x hx => by
      simp [hpx x hx, hqx x hx]⟩
  | smul c f _ hf =>
    obtain ⟨p, hp, hpx⟩ := hf
    exact ⟨c • p, Submodule.smul_mem _ c hp, fun x hx => by simp [hpx x hx]⟩

/-- If every function agrees on `G` with a function of degree at most `H`, then
`|G|` is at most the number of monomials of at most `H` coordinates. -/
theorem card_le_of_forall_exists_agree {H : ℕ} (G : Finset (BitString n))
    (hG : ∀ f : BitString n → ZMod 3, ∃ p ∈ lowDegree n H, ∀ x ∈ G, p x = f x) :
    G.card ≤ (univ.filter fun S : Finset (Fin n) => S.card ≤ H).card := by
  classical
  set small := univ.filter fun S : Finset (Fin n) => S.card ≤ H
  have hset : ({S | S.card ≤ H} : Set (Finset (Fin n))) = ↑small := by
    ext S
    simp [small]
  let E : (↥(small : Set (Finset (Fin n))) → ZMod 3) → (↥G → ZMod 3) :=
    fun c x => ∑ S, c S * monomial S.1 x.1
  have hsurj : Function.Surjective E := by
    intro g
    obtain ⟨p, hp, hpx⟩ := hG fun x => if hx : x ∈ G then g ⟨x, hx⟩ else 0
    rw [lowDegree, hset, Fintype.mem_span_image_iff_exists_fun] at hp
    obtain ⟨c, hc⟩ := hp
    refine ⟨c, ?_⟩
    funext x
    have hx := hpx x.1 x.2
    rw [← hc] at hx
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, x.2, dite_true] at hx
    exact hx
  have hcard := Fintype.card_le_of_surjective E hsurj
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe, Finset.coe_sort_coe] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcard

/-- **Parity is hard to approximate.** A function of degree at most `D` agrees
with parity on at most as many inputs as there are monomials of at most
`n / 2 + D` coordinates. -/
theorem card_agree_xorBool_le_internal {D : ℕ} {P : BitString n → ZMod 3}
    (hP : P ∈ lowDegree n D) :
    (univ.filter fun x => P x = bitVal (Schnorr.xorBool n x)).card ≤
      (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + D).card := by
  classical
  apply card_le_of_forall_exists_agree
  apply exists_agree_of_parity (Submodule.add_mem _ (one_mem_lowDegree D) hP)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [signMonomial_univ, Pi.add_apply, hx]
  rfl

end Smolensky

end Complexity

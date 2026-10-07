/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TupleCounting
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Unrestricted depth-three lower bound: moment bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/MomentBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11
universe uDepth12

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

/-- Every collection of at most the specified number of bits is uniform. -/
def UniformBitsUpTo {Ω : Type uDepth1} {Z : Type uDepth2} [Fintype Ω] [DecidableEq Z]
    (t : ℕ) (bits : Ω → Z → Bool) : Prop :=
  ∀ s : Finset Z, s.card ≤ t → ∀ F : (↥s → Bool) → ℝ,
    finiteAvg (fun ω => F (fun z => bits ω z.val)) = finiteAvg F

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

theorem abs_sign_mul_indicator_le_one (b c : Bool) :
    |sign b * indicator c| ≤ 1 := by
  cases b <;> cases c <;> norm_num [sign, indicator]

/-- Flip one coordinate of a Boolean assignment. -/
def flipCoordinate {A : Type uDepth3} [DecidableEq A] (a₀ : A) :
    (A → Bool) ≃ (A → Bool) where
  toFun x a := if a = a₀ then !(x a) else x a
  invFun x a := if a = a₀ then !(x a) else x a
  left_inv x := by
    funext a
    by_cases h : a = a₀ <;> simp [h]
  right_inv x := by
    funext a
    by_cases h : a = a₀ <;> simp [h]

theorem uniform_product_zero_of_singleton {A : Type uDepth4} {I : Type uDepth5}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (a : I → A) (w : I → ℝ) (i₀ : I)
    (hunique : ∀ i, a i = a i₀ → i = i₀) :
    finiteAvg (fun x : A → Bool => ∏ i, sign (x (a i)) * w i) = 0 := by
  let F : (A → Bool) → ℝ := fun x => ∏ i, sign (x (a i)) * w i
  let e := flipCoordinate (a i₀)
  have hflip (x : A → Bool) : F (e x) = -F x := by
    have hother : (∏ i ∈ Finset.univ.erase i₀, sign ((e x) (a i)) * w i) =
        ∏ i ∈ Finset.univ.erase i₀, sign (x (a i)) * w i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : a i ≠ a i₀ := fun h => (Finset.mem_erase.mp hi).1 (hunique i h)
      simp [e, flipCoordinate, hne]
    have hat : sign ((e x) (a i₀)) * w i₀ = -(sign (x (a i₀)) * w i₀) := by
      simp [e, flipCoordinate]
    change (∏ i, sign ((e x) (a i)) * w i) = -(∏ i, sign (x (a i)) * w i)
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => sign ((e x) (a i)) * w i) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ
        (fun i => sign (x (a i)) * w i) (Finset.mem_univ i₀), hat, hother]
    ring
  have havg : finiteAvg F = -finiteAvg F := by
    calc
      finiteAvg F = finiteAvg (fun x => F (e x)) := (finiteAvg_equiv e F).symm
      _ = finiteAvg (fun x => (-1) * F x) := by
        apply finiteAvg_congr
        intro x
        rw [hflip]
        ring
      _ = -finiteAvg F := by rw [finiteAvg_const_mul]; ring
  change finiteAvg F = 0
  linarith

theorem tuple_product_avg_zero {Ω : Type uDepth6} {Z : Type uDepth7} [Fintype Ω] [DecidableEq Z]
    {t : ℕ} (bits : Ω → Z → Bool) (hdist : UniformBitsUpTo t bits)
    (a : Fin t → Z) (w : Fin t → ℝ) (hns : ¬ TupleNoSingleton a) :
    finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * w i) = 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := tuple_singleton_of_not a hns
  let s : Finset Z := Finset.univ.image a
  let a' : Fin t → ↥s := fun i =>
    ⟨a i, Finset.mem_image_of_mem a (Finset.mem_univ i)⟩
  have hs : s.card ≤ t := by
    simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := a))
  have huniq : ∀ i, a' i = a' i₀ → i = i₀ := by
    intro i hi
    exact hi₀ i (congrArg Subtype.val hi)
  calc
    finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * w i) =
        finiteAvg (fun x : ↥s → Bool => ∏ i, sign (x (a' i)) * w i) :=
      hdist s hs (fun x => ∏ i, sign (x (a' i)) * w i)
    _ = 0 := uniform_product_zero_of_singleton a' w i₀ huniq

theorem sign_indicator_product_le_one {I : Type uDepth8} [Fintype I]
    (b c : I → Bool) : (∏ i, sign (b i) * indicator (c i)) ≤ 1 := by
  calc
    _ ≤ |∏ i, sign (b i) * indicator (c i)| := le_abs_self _
    _ = ∏ i, |sign (b i) * indicator (c i)| := Finset.abs_prod _ _
    _ ≤ 1 := Finset.prod_le_one₀
      (fun _ _ => abs_nonneg _) (fun i _ => abs_sign_mul_indicator_le_one (b i) (c i))

theorem even_moment_le {Ω : Type uDepth9} {Z : Type uDepth10} [Fintype Ω] [Nonempty Ω]
    [Fintype Z] [Nonempty Z] [DecidableEq Z] (h : ℕ)
    (bits : Ω → Z → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (J : Z → Bool) :
    finiteAvg (fun ω => |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h)) ≤
      (Fintype.card Z : ℝ) ^ h * (h : ℝ) ^ (2 * h) := by
  classical
  have hexpand : finiteAvg
      (fun ω => |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h)) =
      ∑ a : Fin (2 * h) → Z,
        finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * indicator (J (a i))) := by
    calc
      _ = finiteAvg (fun ω => ∑ a : Fin (2 * h) → Z,
          ∏ i, sign (bits ω (a i)) * indicator (J (a i))) := by
        apply finiteAvg_congr
        intro ω
        rw [show |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h) =
            (∑ z, sign (bits ω z) * indicator (J z)) ^ (2 * h) by
          simp only [pow_mul, sq_abs]]
        exact Fintype.sum_pow _ _
      _ = _ := finiteAvg_sum Finset.univ _
  have hterm (a : Fin (2 * h) → Z) :
      finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * indicator (J (a i))) ≤
        if TupleNoSingleton a then (1 : ℝ) else 0 := by
    by_cases ha : TupleNoSingleton a
    · simp only [ite_eq_left ha]
      calc
        _ ≤ finiteAvg (fun _ : Ω => (1 : ℝ)) :=
          finiteAvg_mono (fun ω => sign_indicator_product_le_one
            (fun i => bits ω (a i)) (fun i => J (a i)))
        _ = 1 := finiteAvg_const 1
    · rw [ite_eq_right ha, tuple_product_avg_zero bits hdist a (fun i => indicator (J (a i))) ha]
  calc
    _ = _ := hexpand
    _ ≤ ∑ a : Fin (2 * h) → Z, if TupleNoSingleton a then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun a _ => hterm a)
    _ = ((Finset.univ.filter (fun a : Fin (2 * h) → Z => TupleNoSingleton a)).card : ℝ) :=
      Finset.sum_boole _ _
    _ ≤ ((Fintype.card Z) ^ h * h ^ (2 * h) : ℕ) := by
      exact_mod_cast (card_noSingleton_tuples_le (Z := Z) h)
    _ = (Fintype.card Z : ℝ) ^ h * (h : ℝ) ^ (2 * h) := by push_cast; rfl

theorem even_moment_le_manuscript {Ω : Type uDepth11} {Z : Type uDepth12} [Fintype Ω] [Nonempty Ω]
    [Fintype Z] [Nonempty Z] [DecidableEq Z] (h : ℕ)
    (bits : Ω → Z → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (J : Z → Bool) :
    finiteAvg (fun ω => |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h)) ≤
      ((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card Z : ℝ) ^ h := by
  have hh : (h : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast (show h ≤ 2 * h by omega)
  calc
    _ ≤ (Fintype.card Z : ℝ) ^ h * (h : ℝ) ^ (2 * h) :=
      even_moment_le h bits hdist J
    _ ≤ (Fintype.card Z : ℝ) ^ h * ((2 * h : ℕ) : ℝ) ^ (2 * h) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg h) hh _) (by positivity)
    _ = _ := mul_comm _ _

end DepthThreeLowerBound

end

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.FourierExpansion.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Chapter 1: Boolean functions and the Fourier expansion — Internal lemmas

Technical helper lemmas for the Fourier expansion theory. These support the
main results in `BooleanAnalysis.FourierExpansion` but are not intended for
direct use by downstream code.
-/


public section

namespace Complexity

namespace BooleanAnalysis.Internal

open Finset BigOperators BooleanAnalysis

variable {n : ℕ}

/-- `χ(0) = 1`. -/
@[simp]
theorem chi_zero : chi (0 : ZMod 2) = 1 := by
  unfold chi; norm_num

/-- `χ(1) = -1`. -/
@[simp]
theorem chi_one : chi (1 : ZMod 2) = -1 := by
  unfold chi; norm_num

/-- `χ(b)² = 1` for all `b : ZMod 2`. -/
@[simp]
theorem chi_sq (b : ZMod 2) : chi b ^ 2 = 1 := by
  fin_cases b <;> (unfold chi; split_ifs <;> norm_num)

/-- `χ(b) · χ(b) = 1` (non-`pow` form, useful when `simp` doesn't see `sq`). -/
@[simp]
theorem chi_mul_self (b : ZMod 2) : chi b * chi b = 1 := by
  have := chi_sq b; linarith [sq (chi b)]

/-- `χ(b) = 1` or `χ(b) = -1`. -/
theorem chi_eq_one_or_neg_one (b : ZMod 2) : chi b = 1 ∨ chi b = -1 := by
  fin_cases b
  · left; exact chi_zero
  · right; exact chi_one

/-- Every element of `ZMod 2` is `0` or `1`. -/
private theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left; rwa [ZMod.val_eq_zero] at h
  · right; exact Fin.ext h

/-- `χ` is multiplicative: `χ(a + b) = χ(a) · χ(b)`. -/
@[simp]
theorem chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [chi, show (1 : ZMod 2) + 1 = 0 from Fin.ext (by decide)]

/-- `χ(b) ≠ 0` for all `b : ZMod 2`. -/
theorem chi_ne_zero (b : ZMod 2) : chi b ≠ 0 := by
  rcases chi_eq_one_or_neg_one b with h | h <;> simp [h]

/-- The parity function on the empty set is the constant function 1. -/
@[simp]
theorem parityFun_empty : (χ (∅ : Finset (Fin n))) = fun _ => 1 := by
  ext x; simp [parityFun]

/-- Parity functions are multiplicative: `χ S (x + y) = χ S x · χ S y`.
    (Equation 1.5 in the book) -/
@[simp]
theorem parityFun_add (S : Finset (Fin n)) (x y : Cube n) :
    (χ S) (x + y) = (χ S) x * (χ S) y := by
  simp only [parityFun]
  rw [← Finset.prod_mul_distrib]
  congr 1; ext i; exact chi_add (x i) (y i)

/-- `(χ S x)² = 1` for all `S` and `x`. -/
@[simp]
theorem parityFun_sq (S : Finset (Fin n)) (x : Cube n) :
    (χ S) x ^ 2 = 1 := by
  simp only [parityFun, ← Finset.prod_pow]
  simp [chi_sq]

/-- `χ S 0 = 1`. -/
@[simp]
theorem parityFun_zero (S : Finset (Fin n)) : (χ S) 0 = 1 := by
  simp [parityFun, chi_zero]

/-- **Fact 1.7**: `𝔼[χ S] = 1` if `S = ∅` and `𝔼[χ S] = 0` if `S ≠ ∅`. -/
theorem expect_parityFun_proof (S : Finset (Fin n)) :
    𝔼[χ S] = if S = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h; simp [parityFun_empty, expect, Finset.expect_const]
  · simp only [expect_unfold]
    obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty h
    let ej : Cube n := Pi.single j 1
    have hej : (χ S) ej = -1 := by
      simp only [parityFun]
      have hprod : ∀ i ∈ S, chi (ej i) = if i = j then -1 else 1 := by
        intro i _; simp only [ej, Pi.single_apply]; split_ifs <;> simp [chi_zero, chi_one]
      rw [Finset.prod_congr rfl hprod]
      simp [hj]
    suffices ∑ x : Cube n, (χ S) x = 0 by rw [this, mul_zero]
    have hself : ∑ x : Cube n, (χ S) x = -(∑ x : Cube n, (χ S) x) := by
      have key : ∑ x : Cube n, (χ S) x = ∑ y : Cube n, -(χ S) y :=
        Fintype.sum_equiv (Equiv.addRight ej) _ (fun y => -(χ S) y) (fun x => by
          show (χ S) x = -(χ S) (x + ej)
          rw [parityFun_add, hej, mul_neg_one, neg_neg])
      conv_lhs => rw [key]
      exact Finset.sum_neg_distrib (f := fun x : Cube n => (χ S) x)
    linarith

/-- **Definition 1.11** (explicit form): For Boolean-valued `f`,
    `𝔼[f] = Pr[f = 1] - Pr[f = -1]`. -/
theorem expect_boolean_eq_prob_diff (f : BooleanFunction n) (hf : IsBooleanValued f) :
    𝔼[f] = Pr[fun x => f x = 1] - Pr[fun x => f x = -1] := by
  simp only [prob, expect_unfold, indicator]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rcases hf x with h | h <;>
    simp [h, show (1 : ℝ) ≠ -1 by norm_num, show (-1 : ℝ) ≠ 1 by norm_num]

/-- For Boolean-valued `f`, `Pr[f = 1] + Pr[f = -1] = 1`.
    (Implicit in Definition 1.11: every input maps to exactly one of `1` or `-1`.) -/
theorem prob_boolean_sum_one (f : BooleanFunction n) (hf : IsBooleanValued f) :
    Pr[fun x => f x = 1] + Pr[fun x => f x = -1] = 1 := by
  simp only [prob, expect_unfold, indicator]
  rw [← mul_add, ← Finset.sum_add_distrib]
  have : ∀ x : Cube n, (if f x = 1 then (1 : ℝ) else 0) + (if f x = -1 then 1 else 0) = 1 := by
    intro x
    rcases hf x with h | h <;>
      simp [h, show (1 : ℝ) ≠ -1 by norm_num, show (-1 : ℝ) ≠ 1 by norm_num]
  rw [Finset.sum_congr rfl (fun x _ => this x)]
  simp [Fintype.card_fin, ZMod.card]

/-- Helper: `⟪f, g⟫ + 2 · dist(f, g) = 1` for Boolean-valued `f, g`. -/
theorem inner_add_two_hammingDist (f g : BooleanFunction n)
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    ⟪f, g⟫ + 2 * hammingDist f g = 1 := by
  simp only [inner_def, hammingDist, prob, indicator, expect_unfold]
  have h2n : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  have hkey : ∀ x : Cube n,
      f x * g x + 2 * (@ite ℝ (f x ≠ g x) (Classical.propDecidable _) 1 0) = 1 := by
    intro x
    rcases hf x with hfx | hfx <;> rcases hg x with hgx | hgx <;> simp only [hfx, hgx] <;> norm_num
  have hsum : (∑ x : Cube n, f x * g x)
      + 2 * (∑ x : Cube n, @ite ℝ (f x ≠ g x) (Classical.propDecidable _) 1 0)
      = (2 : ℝ) ^ n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun x _ => hkey x)]
    simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
  have h1 : 1 / (2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by field_simp
  calc 1 / 2 ^ n * ∑ x : Cube n, f x * g x
          + 2 * (1 / 2 ^ n * ∑ x : Cube n, @ite ℝ (f x ≠ g x) (Classical.propDecidable _) 1 0)
        = 1 / 2 ^ n * ((∑ x : Cube n, f x * g x)
          + 2 * (∑ x : Cube n, @ite ℝ (f x ≠ g x) (Classical.propDecidable _) 1 0)) := by ring
    _ = 1 / (2 : ℝ) ^ n * (2 : ℝ) ^ n := by congr 1
    _ = 1 := h1

/-- `χ_S · χ_T = χ_{S △ T}` (pointwise). -/
theorem parityFun_mul (S T : Finset (Fin n)) (x : Cube n) :
    (χ S) x * (χ T) x = (χ (symmDiff S T)) x := by
  simp only [parityFun]
  have hsdiff := Finset.prod_sdiff (Finset.inter_subset_union (s := S) (t := T))
    (f := fun i => chi (x i))
  have hsd : (S ∪ T) \ (S ∩ T) = symmDiff S T := by
    ext i; simp [Finset.mem_symmDiff]; tauto
  rw [hsd] at hsdiff
  have hunion := Finset.prod_union_inter (s₁ := S) (s₂ := T) (f := fun i => chi (x i))
  have hchi_sq : (∏ i ∈ S ∩ T, chi (x i)) ^ 2 = 1 := by
    rw [← Finset.prod_pow]; simp [chi_sq]
  rw [← hunion, ← hsdiff, mul_assoc, ← sq, hchi_sq, mul_one]

/-- **Theorem 1.5**: The parity functions are orthonormal:
    `⟪χ S, χ T⟫ = 1` if `S = T` and `0` otherwise. -/
theorem parityFun_orthonormal_proof (S T : Finset (Fin n)) :
    ⟪χ S, χ T⟫ = if S = T then 1 else 0 := by
  rw [inner_eq_expect]
  have : (fun x : Cube n => (χ S) x * (χ T) x) = (χ (symmDiff S T)) := by
    ext x; exact parityFun_mul S T x
  rw [this, expect_parityFun_proof]
  have : symmDiff S T = ∅ ↔ S = T := symmDiff_eq_bot
  simp [this]

/-- Sum of all parity functions at a point: `∑_S χ_S(z) = 2^n` if `z = 0`, else `0`. -/
theorem sum_parityFun (z : Cube n) :
    ∑ S : Finset (Fin n), (χ S) z = if z = 0 then (2 : ℝ) ^ n else 0 := by
  split_ifs with hz
  · subst hz; simp [parityFun_zero, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  · have ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h; push Not at h; exact hz (funext (fun i => by simpa using h i))
    have hzj : z j = 1 := by
      have := ZMod.val_lt (z j)
      rcases (show (z j).val = 0 ∨ (z j).val = 1 by omega) with h | h
      · exact absurd (Fin.ext h : z j = 0) hj
      · exact Fin.ext h
    have hflip : ∀ S : Finset (Fin n), (χ (symmDiff S {j})) z = -(χ S) z := by
      intro S
      rw [← parityFun_mul S {j} z]
      simp only [parityFun, Finset.prod_singleton, hzj, chi_one, mul_neg_one]
    have hself : ∑ S : Finset (Fin n), (χ S) z = -(∑ S : Finset (Fin n), (χ S) z) := by
      conv_lhs =>
        rw [Fintype.sum_equiv ((symmDiff_right_involutive ({j} : Finset (Fin n))).toPerm)
          _ (fun S => -(χ S) z) (fun S => by
            show (χ S) z = -(χ (symmDiff {j} S)) z
            rw [symmDiff_comm, hflip]; ring)]
      rw [Finset.sum_neg_distrib]
    linarith

/-- The Fourier expansion: `f(x) = ∑_S 𝓕 f S · χ_S(x)`. -/
theorem fourier_expansion_proof (f : BooleanFunction n) (x : Cube n) :
    f x = ∑ S : Finset (Fin n), 𝓕 f S * (χ S) x := by
  simp only [fourierCoeff, inner_def]
  have h2n : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  have hadd_zero : ∀ y : Cube n, y + x = 0 ↔ y = x := by
    intro y; constructor
    · intro h; funext i
      have hi := congr_fun h i
      simp only [Pi.add_apply, Pi.zero_apply] at hi
      have : x i + (y i + x i) = x i + 0 := congr_arg (x i + ·) hi
      rwa [add_comm (y i) (x i), ← add_assoc, CharTwo.add_self_eq_zero, zero_add,
        add_zero] at this
    · intro h; subst h; funext i; simp [CharTwo.add_self_eq_zero]
  conv_rhs =>
    arg 2; ext S
    rw [show (1 / (2 : ℝ) ^ n * ∑ y, f y * (χ S) y) * (χ S) x =
      ∑ y : Cube n, 1 / (2 : ℝ) ^ n * (f y * ((χ S) (y + x))) from by
      rw [mul_comm _ ((χ S) x), Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [parityFun_add]; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_parityFun, hadd_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x, ite_eq_left (Finset.mem_univ _)]
  field_simp

/-- **Fourier uniqueness**: If `f(x) = ∑_S c_S · χ_S(x)` for all `x`,
    then `c_S = 𝓕 f S` for all `S`.

    Proof: take `⟪–, χ T⟫` of both sides. On the right, orthonormality
    kills every term except `S = T`, leaving `c T`. On the left we get `𝓕 f T`. -/
theorem fourier_uniqueness_proof (f : BooleanFunction n) (c : Finset (Fin n) → ℝ)
    (h : ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x)
    (T : Finset (Fin n)) : c T = 𝓕 f T := by
  -- Orthonormality: ⟪χ S, χ T⟫ = δ_{S,T}  (the key fact)
  have key : ∀ S, 𝔼[fun x => (χ S) x * (χ T) x] = if S = T then 1 else 0 :=
    fun S => by rw [← inner_eq_expect]; exact parityFun_orthonormal_proof S T
  -- Unfold 𝓕 f T = ⟪f, χ T⟫ and substitute the expansion
  simp only [fourierCoeff, inner_def]
  have step1 : ∑ x : Cube n, f x * (χ T) x =
    ∑ x : Cube n, ∑ S : Finset (Fin n), c S * ((χ S) x * (χ T) x) := by
    apply Finset.sum_congr rfl; intro x _; rw [h x, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro S _; ring
  rw [step1, Finset.sum_comm]
  -- Factor out c_S and apply orthonormality to collapse the sum
  rw [show 1 / (2 : ℝ) ^ n *
    ∑ S : Finset (Fin n), ∑ x : Cube n, c S * ((χ S) x * (χ T) x) =
    ∑ S : Finset (Fin n), c S * (1 / (2 : ℝ) ^ n * ∑ x : Cube n, (χ S) x * (χ T) x) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _
    simp_rw [Finset.mul_sum,
      show ∀ i : Cube n, 1 / (2 : ℝ) ^ n * (c S * ((χ S) i * (χ T) i)) =
        c S * (1 / (2 : ℝ) ^ n * ((χ S) i * (χ T) i)) from fun i => by ring]]
  have step4 : ∀ S : Finset (Fin n),
    c S * (1 / (2 : ℝ) ^ n * ∑ x : Cube n, (χ S) x * (χ T) x) =
    c S * (if S = T then 1 else 0) := by
    intro S; congr 1
    have := key S; rw [expect_unfold (f := fun x : Cube n => (χ S) x * (χ T) x)] at this; exact this
  simp_rw [step4, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ### Orthonormal basis of parity functions

The parity functions `χ S` form an orthonormal basis for `BooleanFunction n`
under the uniform-measure inner product. Plancherel and Parseval follow
directly from Mathlib's `OrthonormalBasis` API. -/

/-- The parity functions are orthonormal under the uniform-measure inner product. -/
theorem parityFun_orthonormal : Orthonormal ℝ (parityFun (n := n)) := by
  rw [orthonormal_iff_ite]
  intro i j
  exact parityFun_orthonormal_proof i j

/-- The parity functions span `BooleanFunction n`. -/
theorem parityFun_span : ⊤ ≤ Submodule.span ℝ (Set.range (parityFun (n := n))) := by
  intro f _
  have hexp := fourier_expansion_proof f
  have hf : f = ∑ S : Finset (Fin n), fourierCoeff f S • parityFun S := by
    ext x
    have : (∑ S : Finset (Fin n), fourierCoeff f S • parityFun S) x =
        ∑ S : Finset (Fin n), fourierCoeff f S * (χ S) x := by
      simp [BooleanFunction.smul_apply]
    rw [this]; exact hexp x
  rw [hf]
  exact Submodule.sum_mem _ (fun S _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩))

/-- The parity functions form an orthonormal basis for `BooleanFunction n`. -/
noncomputable def parityOrthonormalBasis :
    OrthonormalBasis (Finset (Fin n)) ℝ (BooleanFunction n) :=
  OrthonormalBasis.mk parityFun_orthonormal parityFun_span

@[simp] theorem parityOrthonormalBasis_apply (S : Finset (Fin n)) :
    parityOrthonormalBasis S = parityFun S := by
  show (OrthonormalBasis.mk parityFun_orthonormal parityFun_span) S = _
  simp [OrthonormalBasis.coe_mk]

/-- **Plancherel's theorem**: `⟪f, g⟫ = ∑_S 𝓕 f S · 𝓕 g S`.
    Derived from the `OrthonormalBasis` of parity functions. -/
theorem plancherel_proof (f g : BooleanFunction n) :
    ⟪f, g⟫ = ∑ S : Finset (Fin n), 𝓕 f S * 𝓕 g S := by
  have h := parityOrthonormalBasis.sum_inner_mul_inner f g
  simp only [parityOrthonormalBasis_apply] at h
  rw [h.symm]; congr 1; ext S
  congr 1; exact real_inner_comm _ _

/-! ### Helpers for §1.4 Proposition 1.15 (variance–distance bounds) -/

/-- `dist(f, 1) = Pr[f = -1]` for Boolean-valued `f`. -/
theorem hammingDist_const_one (f : BooleanFunction n) (hf : IsBooleanValued f) :
    hammingDist f (fun _ => 1) = Pr[fun x => f x = -1] := by
  unfold hammingDist prob indicator; congr 1; ext x
  rcases hf x with h | h <;>
    simp [h, show (1 : ℝ) ≠ -1 by norm_num, show (-1 : ℝ) ≠ 1 by norm_num]

/-- `dist(f, -1) = Pr[f = 1]` for Boolean-valued `f`. -/
theorem hammingDist_const_neg_one (f : BooleanFunction n) (hf : IsBooleanValued f) :
    hammingDist f (fun _ => -1) = Pr[fun x => f x = 1] := by
  unfold hammingDist prob indicator; congr 1; ext x
  rcases hf x with h | h <;>
    simp [h, show (1 : ℝ) ≠ -1 by norm_num, show (-1 : ℝ) ≠ 1 by norm_num]

/-- For `p, q ≥ 0` with `p + q = 1`: `2 · min(q, p) ≤ 4pq ≤ 4 · min(q, p)`. -/
theorem variance_dist_bounds_arith (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    2 * min q p ≤ 4 * p * q ∧ 4 * p * q ≤ 4 * min q p := by
  rcases le_total q p with hle | hle
  · rw [min_eq_left hle]
    have hp' : 1/2 ≤ p := by linarith
    constructor <;> nlinarith
  · rw [min_eq_right hle]
    have hq' : 1/2 ≤ q := by linarith
    constructor <;> nlinarith

/-! ### Helpers for §1.5 (densities and convolution) -/

/-- `z + y + y = z` in `𝔽₂ⁿ` (characteristic 2 cancellation). -/
theorem cube_add_right_cancel (z y : Cube n) : z + y + y = z := by
  ext i; simp [Pi.add_apply, add_assoc, CharTwo.add_self_eq_zero]

/-- `setDensity {0}` evaluates to `2^n` at `0` and `0` elsewhere. -/
theorem setDensity_singleton_zero_ite (y : Cube n) :
    setDensity ({0} : Finset (Cube n)) y = if y = 0 then (2 : ℝ) ^ n else 0 := by
  unfold setDensity indicator
  simp only [Finset.mem_singleton]
  split_ifs with hy
  · subst hy; simp [expect, Finset.expect_eq_sum_div_card, Finset.card_univ, ZMod.card]
  · ring

/-- `setDensity {0}` equals the sum of all parity functions. -/
theorem setDensity_singleton_zero_proof :
    ∀ y : Cube n, setDensity ({0} : Finset (Cube n)) y =
      ∑ S : Finset (Fin n), (χ S) y := by
  intro y
  unfold setDensity
  rw [sum_parityFun]; unfold indicator
  simp only [Finset.mem_singleton]
  split_ifs with hy
  · subst hy; simp [expect, Finset.expect_eq_sum_div_card, Finset.card_univ, ZMod.card]
  · ring

/-- Every Fourier coefficient of `setDensity {0}` is `1`. -/
theorem fourierCoeff_setDensity_singleton_zero_proof (S : Finset (Fin n)) :
    𝓕 (setDensity ({0} : Finset (Cube n))) S = 1 := by
  simp only [fourierCoeff, inner_def]
  simp_rw [setDensity_singleton_zero_ite]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
  simp [parityFun_zero]

/-- The convolution of two densities is again a density. -/
theorem convolution_density_isDensity_proof (φ ψ : BooleanFunction n)
    (hφ : IsDensity φ) (hψ : IsDensity ψ) :
    IsDensity (φ ⊛ ψ) := by
  constructor
  · intro x
    simp only [convolution]
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg; intro y _
      exact mul_nonneg (hφ.nonneg y) (hψ.nonneg (x + y))
  · simp only [convolution, expect_unfold]
    have hinner : ∀ x : Cube n, 𝔼[fun y => φ y * ψ (x + y)]
        = 1 / 2 ^ n * ∑ y : Cube n, φ y * ψ (x + y) :=
      fun x => expect_unfold (f := fun y : Cube n => φ y * ψ (x + y))
    simp only [hinner]
    have hshift : ∀ y : Cube n, ∑ x : Cube n, ψ (x + y) = ∑ x : Cube n, ψ x := by
      intro y; exact Equiv.sum_comp (Equiv.addRight y) ψ
    rw [show (1 : ℝ) / 2 ^ n * ∑ x, 1 / 2 ^ n * ∑ y, φ y * ψ (x + y) =
      (1 / 2 ^ n) ^ 2 * ∑ x, ∑ y, φ y * ψ (x + y) from by
      rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring]
    rw [Finset.sum_comm]
    have h1 : ∀ y : Cube n, ∑ x : Cube n, φ y * ψ (x + y) = φ y * ∑ x : Cube n, ψ x := by
      intro y; rw [← Finset.mul_sum]; congr 1; exact hshift y
    simp_rw [h1]
    rw [← Finset.sum_mul (s := Finset.univ) (f := fun x : Cube n => φ x)
      (a := ∑ x : Cube n, ψ x)]
    have hφ1 := hφ.expect_one
    have hψ1 := hψ.expect_one
    rw [expect_unfold (f := φ)] at hφ1
    rw [expect_unfold (f := ψ)] at hψ1
    nlinarith

/-- The convolution theorem: `𝓕 (f ⊛ g) S = (𝓕 f S) · (𝓕 g S)`. -/
theorem fourierCoeff_convolution_proof (f g : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 (f ⊛ g) S = (𝓕 f S) * (𝓕 g S) := by
  simp only [fourierCoeff, inner_def, convolution]
  have hconv : ∀ x : Cube n, 𝔼[fun y => f y * g (x + y)]
      = 1 / 2 ^ n * ∑ y : Cube n, f y * g (x + y) :=
    fun x => expect_unfold (f := fun y : Cube n => f y * g (x + y))
  simp only [hconv]
  have hinner : ∀ y : Cube n, ∑ x : Cube n, g (x + y) * (χ S) x =
    (χ S) y * ∑ z : Cube n, g z * (χ S) z := by
    intro y
    rw [(Equiv.sum_comp (Equiv.addRight y) (fun z => g (z + y) * (χ S) z)).symm]
    simp only [Equiv.coe_addRight]
    conv_lhs => arg 2; ext z; rw [cube_add_right_cancel, parityFun_add S z y,
      show g z * ((χ S) z * (χ S) y) = (χ S) y * (g z * (χ S) z) from by ring]
    rw [← Finset.mul_sum]
  suffices hlhs : ∑ x : Cube n, (∑ y, f y * g (x + y)) * (χ S) x =
    (∑ y, f y * (χ S) y) * (∑ z, g z * (χ S) z) by
    rw [show 1 / 2 ^ n * ∑ x, (1 / 2 ^ n * ∑ y, f y * g (x + y)) * χ S x =
      (1 / 2 ^ n) ^ 2 * (∑ x, (∑ y, f y * g (x + y)) * χ S x) from by
      rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring]
    rw [hlhs]; ring
  calc ∑ x : Cube n, (∑ y, f y * g (x + y)) * (χ S) x
      = ∑ x, ∑ y, f y * g (x + y) * (χ S) x := by
        apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_mul]
    _ = ∑ y, ∑ x, f y * g (x + y) * (χ S) x := Finset.sum_comm
    _ = ∑ y, f y * ((χ S) y * ∑ z, g z * (χ S) z) := by
        apply Finset.sum_congr rfl; intro y _
        have : (∑ x, f y * g (x + y) * (χ S) x) = f y * ∑ x, g (x + y) * (χ S) x := by
          rw [Finset.mul_sum]; congr 1; ext x; ring
        rw [this, hinner]
    _ = (∑ y, f y * (χ S) y) * (∑ z, g z * (χ S) z) := by
        have : ∀ y : Cube n, f y * ((χ S) y * ∑ z, g z * (χ S) z) =
          f y * (χ S) y * (∑ z, g z * (χ S) z) := fun y => by ring
        simp_rw [this]; exact (Finset.sum_mul ..).symm

/-! ### Helpers for §1.6 (BLR test and local correctability) -/

/-- `Pr[P] + Pr[¬P] = 1`. -/
theorem prob_compl (P : Cube n → Prop) : Pr[P] + Pr[fun x => ¬ P x] = 1 := by
  simp only [prob, expect_unfold, indicator]
  rw [← mul_add, ← Finset.sum_add_distrib]
  have : ∀ x : Cube n,
    (@ite ℝ (P x) (Classical.propDecidable _) 1 0) +
    (@ite ℝ (¬ P x) (Classical.propDecidable _) 1 0) = 1 := by
    intro x; by_cases hP : P x <;> simp [hP]
  rw [Finset.sum_congr rfl (fun x _ => this x)]
  simp [Fintype.card_fin, ZMod.card]

/-- `0 ≤ Pr[P]`. -/
theorem prob_nonneg (P : Cube n → Prop) : 0 ≤ Pr[P] := by
  simp only [prob, indicator, expect_unfold]
  apply mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => by split_ifs <;> norm_num))

/-- Union bound: if `¬P ⊆ Q ∪ R` then `Pr[¬P] ≤ Pr[Q] + Pr[R]`. -/
theorem prob_union_bound {P Q R : Cube n → Prop}
    (h : ∀ x, ¬ P x → Q x ∨ R x) :
    Pr[fun x => ¬ P x] ≤ Pr[Q] + Pr[R] := by
  simp only [prob, expect_unfold, indicator]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum; intro x _
  by_cases hp : P x
  · simp [hp]; split_ifs <;> linarith
  · rcases h x hp with hq | hr
    · simp [hp, hq]; split_ifs <;> linarith
    · simp [hp, hr]; split_ifs <;> linarith

/-- Shift invariance of probability: `Pr_y[P(x + y)] = Pr_z[P(z)]`. -/
theorem prob_shift (P : Cube n → Prop) (x : Cube n) :
    Pr[fun y => P (x + y)] = Pr[P] := by
  simp only [prob, expect_unfold, indicator]; congr 1
  exact Equiv.sum_comp (Equiv.addLeft x)
    (fun z => @ite ℝ (P z) (Classical.propDecidable _) 1 0)

/-- `χ S y · χ S (x + y) = χ S x` (key identity for local correctability). -/
theorem parityFun_mul_cancel (S : Finset (Fin n)) (x y : Cube n) :
    (χ S) y * (χ S) (x + y) = (χ S) x := by
  rw [parityFun_add]; have h := parityFun_sq S y
  have : (χ S) y * ((χ S) x * (χ S) y) = (χ S) x * ((χ S) y * (χ S) y) := by ring
  rw [this, show (χ S) y * (χ S) y = (χ S) y ^ 2 from by ring, h, mul_one]

/-- Local correctability of the Fourier decoding algorithm. -/
theorem local_correctability_proof (f : BooleanFunction n) (_hf : IsBooleanValued f)
    (S : Finset (Fin n)) (ε : ℝ) (hclose : IsClose f (χ S) ε) (x : Cube n) :
    Pr[fun y => f y * f (x + y) = (χ S) x] ≥ 1 - 2 * ε := by
  have hdist : hammingDist f (χ S) ≤ ε := hclose
  have hcompl : Pr[fun y => f y * f (x + y) ≠ (χ S) x] ≤ 2 * ε := by
    calc Pr[fun y => f y * f (x + y) ≠ (χ S) x]
        ≤ Pr[fun y => f y ≠ (χ S) y] + Pr[fun y => f (x + y) ≠ (χ S) (x + y)] :=
          prob_union_bound (fun y hne => by
            by_contra h; push Not at h
            exact hne (by rw [h.1, h.2, parityFun_mul_cancel]))
      _ = hammingDist f (χ S) + hammingDist f (χ S) := by
          unfold hammingDist; congr 1; exact prob_shift (fun z => f z ≠ (χ S) z) x
      _ ≤ 2 * ε := by linarith
  linarith [prob_compl (fun y => f y * f (x + y) = (χ S) x)]

/-! ### Helpers for §1.6 (BLR acceptance probability and soundness) -/

/-- **Parseval's theorem**: `⟪f, f⟫ = ∑_S (𝓕 f S)²`. -/
theorem parseval_proof (f : BooleanFunction n) :
    ⟪f, f⟫ = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 := by
  rw [plancherel_proof]; congr 1; ext S; rw [sq]

/-- Parseval's theorem for Boolean-valued functions. -/
theorem parseval_boolean_proof (f : BooleanFunction n) (hf : IsBooleanValued f) :
    ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 = 1 := by
  rw [← parseval_proof]; simp only [inner_def]
  simp_rw [show ∀ x : Cube n, f x * f x = 1 from
    fun x => by rcases hf x with h | h <;> simp [h],
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]; simp [ZMod.card]

/-- For Boolean `f`, `(𝓕 f S)² ≤ 1`. -/
theorem fourierCoeff_sq_le_one (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) : (𝓕 f S) ^ 2 ≤ 1 := by
  linarith [parseval_boolean_proof f hf,
    Finset.single_le_sum (fun T (_ : T ∈ Finset.univ) => sq_nonneg (𝓕 f T))
      (Finset.mem_univ S)]

/-- For Boolean `f`, `(𝓕 f S)³ ≤ c · (𝓕 f S)²` when `c` dominates all Fourier
    coefficients. -/
theorem cube_le_max_sq (_f : BooleanFunction n) (_hf : IsBooleanValued f)
    (c : ℝ) (hmax : ∀ T, 𝓕 f T ≤ c) (S : Finset (Fin n)) :
    (𝓕 f S) ^ 3 ≤ c * (𝓕 f S) ^ 2 := by
  rw [show (𝓕 f S) ^ 3 = 𝓕 f S * (𝓕 f S) ^ 2 from by ring]
  exact mul_le_mul_of_nonneg_right (hmax S) (sq_nonneg _)

/-- Parity functions are Boolean-valued. -/
theorem parityFun_isBoolean (S : Finset (Fin n)) : IsBooleanValued (χ S) := by
  intro x; have h := parityFun_sq S x
  have : ((χ S) x - 1) * ((χ S) x + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linarith
  · right; linarith

/-- `dist(f, χ S) = (1 - 𝓕 f S) / 2` for Boolean-valued `f`. -/
theorem hammingDist_eq_fourier (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) : hammingDist f (χ S) = (1 - 𝓕 f S) / 2 := by
  have h := inner_add_two_hammingDist f (χ S) hf (parityFun_isBoolean S)
  show hammingDist f (χ S) = (1 - ⟪f, χ S⟫) / 2; linarith

/-- For Boolean `f`, the BLR indicator equals `(1 + f(x)·f(y)·f(x+y))/2`. -/
theorem blr_indicator_eq (f : BooleanFunction n) (hf : IsBooleanValued f) (x y : Cube n) :
    (𝟙 (fun y => f x * f y = f (x + y))) y = (1 + f x * f y * f (x + y)) / 2 := by
  unfold indicator
  rcases hf x with h1 | h1 <;> rcases hf y with h2 | h2 <;> rcases hf (x + y) with h3 | h3 <;>
    simp [h1, h2, h3, show (1 : ℝ) ≠ -1 by norm_num, show (-1 : ℝ) ≠ 1 by norm_num]

/-- `𝔼_x[𝔼_y[f(x)·f(y)·f(x+y)]] = ⟪f, f ⊛ f⟫`. -/
theorem triple_expect_eq (f : BooleanFunction n) :
    𝔼[fun x => 𝔼[fun y => f x * f y * f (x + y)]] = ⟪f, f ⊛ f⟫ := by
  simp only [inner_def, convolution]
  have hi1 : ∀ x : Cube n, 𝔼[fun y => f x * f y * f (x + y)]
      = 1 / 2 ^ n * ∑ y : Cube n, f x * f y * f (x + y) :=
    fun x => expect_unfold (f := fun y : Cube n => f x * f y * f (x + y))
  have hi2 : ∀ x : Cube n, 𝔼[fun y => f y * f (x + y)]
      = 1 / 2 ^ n * ∑ y : Cube n, f y * f (x + y) :=
    fun x => expect_unfold (f := fun y : Cube n => f y * f (x + y))
  rw [expect_unfold (f := fun x : Cube n => 𝔼[fun y => f x * f y * f (x + y)])]
  simp only [hi1, hi2]
  congr 1; apply Finset.sum_congr rfl; intro x _
  simp_rw [show ∀ y : Cube n,
    f x * f y * f (x + y) = f x * (f y * f (x + y)) from fun y => by ring,
    ← Finset.mul_sum]; ring

/-- `⟪f, f ⊛ f⟫ = ∑_S (𝓕 f S)³`. -/
theorem inner_conv_eq_sum_cube (f : BooleanFunction n) :
    ⟪f, f ⊛ f⟫ = ∑ S : Finset (Fin n), (𝓕 f S) ^ 3 := by
  rw [plancherel_proof]; apply Finset.sum_congr rfl; intro S _
  rw [fourierCoeff_convolution_proof]; ring

/-- Linearity of expectation: `𝔼[c + g] = c + 𝔼[g]`. -/
theorem expect_add_const (c : ℝ) (g : BooleanFunction n) :
    𝔼[fun x => c + g x] = c + 𝔼[g] := by
  rw [expect_unfold (f := fun x : Cube n => c + g x), expect_unfold (f := g),
    Finset.sum_add_distrib (f := fun _ : Cube n => c) (g := fun x : Cube n => g x)]
  simp [Finset.card_univ, ZMod.card]
  field_simp

/-- Linearity of expectation: `𝔼[c · g] = c · 𝔼[g]`. -/
theorem expect_scale (c : ℝ) (g : BooleanFunction n) :
    𝔼[fun x => c * g x] = c * 𝔼[g] := by
  unfold expect; exact (Finset.mul_expect ..).symm

/-- The BLR acceptance probability formula. -/
theorem blrAcceptProb_eq_proof (f : BooleanFunction n) (hf : IsBooleanValued f) :
    blrAcceptProb f = 1 / 2 + 1 / 2 * ∑ S : Finset (Fin n), (𝓕 f S) ^ 3 := by
  rw [← inner_conv_eq_sum_cube, ← triple_expect_eq]
  unfold blrAcceptProb prob₂
  suffices hstep : ∀ x : Cube n,
    𝔼[𝟙 (fun y => f x * f y = f (x + y))] =
    1 / 2 + 1 / 2 * 𝔼[fun y => f x * f y * f (x + y)] by
    simp_rw [hstep]
    rw [expect_add_const (c := 1 / 2)
      (g := fun x : Cube n => 1 / 2 * 𝔼[fun y => f x * f y * f (x + y)]),
      expect_scale (c := 1 / 2)
      (g := fun x : Cube n => 𝔼[fun y => f x * f y * f (x + y)])]
  intro x
  rw [show 𝔼[𝟙 (fun y => f x * f y = f (x + y))] =
    𝔼[fun y => (1 + f x * f y * f (x + y)) / 2] from by
    rw [expect_unfold (f := 𝟙 (fun y : Cube n => f x * f y = f (x + y))),
      expect_unfold (f := fun y : Cube n => (1 + f x * f y * f (x + y)) / 2)]
    congr 1; apply Finset.sum_congr rfl; intro y _
    exact blr_indicator_eq f hf x y,
    show (fun y : Cube n => (1 + f x * f y * f (x + y)) / 2) =
    (fun y => 1/2 + 1/2 * (f x * f y * f (x + y))) from by ext y; ring]
  rw [expect_add_const (c := 1 / 2)
    (g := fun y : Cube n => 1 / 2 * (f x * f y * f (x + y))),
    expect_scale (c := 1 / 2) (g := fun y : Cube n => f x * f y * f (x + y))]

/-- **BLR completeness**: If `f` is linear (i.e., `f = χ_S` for some `S`),
    then the BLR test accepts with probability 1. -/
theorem blr_completeness_proof (f : BooleanFunction n) (hf : IsLinear f) :
    blrAcceptProb f = 1 := by
  obtain ⟨S, hS⟩ := hf
  unfold blrAcceptProb prob₂
  have hev : ∀ x y : Cube n, f x * f y = f (x + y) := by
    intro x y; simp only [hS, parityFun_add]
  have hind : ∀ x : Cube n, 𝔼[𝟙 (fun y => f x * f y = f (x + y))] = 1 := by
    intro x
    have : (𝟙 (fun y => f x * f y = f (x + y)) : BooleanFunction n) = fun _ => 1 := by
      ext y; simp [indicator, hev x y]
    rw [this]; simp [expect, Finset.expect_const]
  simp_rw [hind]; simp [expect, Finset.expect_const]

/-- BLR soundness: if the BLR test accepts with probability `≥ 1 - ε`,
    then `f` is `ε`-close to a linear function. -/
theorem blr_soundness_proof (f : BooleanFunction n) (hf : IsBooleanValued f) (ε : ℝ)
    (hε : blrAcceptProb f ≥ 1 - ε) :
    IsCloseToProperty f IsLinear ε := by
  have hblr := blrAcceptProb_eq_proof f hf
  have hsum3 : ∑ S : Finset (Fin n), (𝓕 f S) ^ 3 ≥ 1 - 2 * ε := by linarith
  have hpars := parseval_boolean_proof f hf
  obtain ⟨S₀, _, hmax⟩ := Finset.exists_max_image Finset.univ (𝓕 f ·)
    ⟨∅, Finset.mem_univ _⟩
  have hmax' : ∀ T, 𝓕 f T ≤ 𝓕 f S₀ := fun T => hmax T (Finset.mem_univ T)
  have hle : ∑ S : Finset (Fin n), (𝓕 f S) ^ 3 ≤
      𝓕 f S₀ * ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro S _
    exact cube_le_max_sq f hf (𝓕 f S₀) hmax' S
  rw [hpars, mul_one] at hle
  have hcoeff : 𝓕 f S₀ ≥ 1 - 2 * ε := by linarith
  have hdist := hammingDist_eq_fourier f hf S₀
  have hclose : hammingDist f (χ S₀) ≤ ε := by linarith
  exact ⟨χ S₀, ⟨S₀, fun _ => rfl⟩, hclose⟩

/-! ### Equivalence of linearity characterizations (§1.6) -/

/-- For Boolean-valued multiplicative `f`, `f(0) = 1`. -/
theorem multiplicative_zero (f : BooleanFunction n) (hf : IsBooleanValued f)
    (hmul : IsMultiplicative f) : f 0 = 1 := by
  have h := hmul 0 0
  simp only [add_zero] at h
  rcases hf 0 with h0 | h0
  · exact h0
  · exfalso; rw [h0] at h; linarith

/-- Linear implies multiplicative. -/
theorem isLinear_isMultiplicative (f : BooleanFunction n) (hlin : IsLinear f) :
    IsMultiplicative f := by
  obtain ⟨S, hS⟩ := hlin
  intro x y; rw [hS, hS, hS, parityFun_add]

/-- A multiplicative function distributes over finite sums:
    `f(∑_{i ∈ s} gᵢ) = ∏_{i ∈ s} f(gᵢ)`. -/
theorem multiplicative_finset_sum {ι : Type*} (f : BooleanFunction n) (hf : IsBooleanValued f)
    (hmul : IsMultiplicative f) (s : Finset ι) (g : ι → Cube n) :
    f (∑ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp [multiplicative_zero f hf hmul]
  | cons a s has ih => rw [Finset.sum_cons, Finset.prod_cons, hmul, ih]

/-- In `𝔽₂ⁿ`, every element is the sum of its support basis vectors:
    `x = ∑_{i : x i = 1} eᵢ`. -/
theorem cube_eq_sum_support (x : Cube n) :
    x = ∑ i ∈ Finset.univ.filter (fun i => x i = 1), Pi.single i 1 := by
  ext j
  simp only [Finset.sum_apply, Pi.single_apply]
  rcases zmod2_cases (x j) with h | h <;> simp [h]

/-- Multiplicative + Boolean-valued implies linear.
    Key idea: define `S = {i | f(eᵢ) = -1}` and show `f = χ S` by
    decomposing `x` into a sum of basis vectors and using multiplicativity. -/
theorem isMultiplicative_isLinear (f : BooleanFunction n) (hf : IsBooleanValued f)
    (hmul : IsMultiplicative f) : IsLinear f := by
  let S := Finset.univ.filter (fun i : Fin n => f (Pi.single i 1) = -1)
  refine ⟨S, fun x => ?_⟩
  let supp := Finset.univ.filter (fun i : Fin n => x i = 1)
  -- Step 1: f(x) = ∏_{i ∈ supp} f(eᵢ)
  have hfx : f x = ∏ i ∈ supp, f (Pi.single i 1) := by
    conv_lhs => rw [cube_eq_sum_support x]
    exact multiplicative_finset_sum f hf hmul supp _
  -- Step 2: χ_S(x) = ∏_{i ∈ S} χ(x i)
  -- Step 3: Show these are equal
  rw [hfx]; simp only [parityFun]
  -- LHS: f(eᵢ) = -1 when i ∈ S, = 1 when i ∉ S
  have hlhs : ∏ i ∈ supp, f (Pi.single i 1) = ∏ i ∈ supp.filter (· ∈ S), (-1 : ℝ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not supp (· ∈ S)]
    have h1 : ∏ i ∈ supp.filter (· ∈ S), f (Pi.single i 1) =
        ∏ i ∈ supp.filter (· ∈ S), (-1 : ℝ) :=
      Finset.prod_congr rfl (fun i hi => by
        simp only [Finset.mem_filter, S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi.2)
    have h2 : ∏ i ∈ supp.filter (· ∉ S), f (Pi.single i 1) = 1 :=
      Finset.prod_eq_one (fun i hi => by
        simp only [Finset.mem_filter, S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rcases hf (Pi.single i 1) with h | h
        · exact h
        · exact absurd h hi.2)
    rw [h1, h2, mul_one]
  -- RHS: χ(x i) = -1 when i ∈ supp (x i = 1), = 1 when i ∉ supp (x i = 0)
  have hrhs : ∏ i ∈ S, chi (x i) = ∏ i ∈ S.filter (· ∈ supp), (-1 : ℝ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not S (· ∈ supp)]
    have h1 : ∏ i ∈ S.filter (· ∈ supp), chi (x i) =
        ∏ i ∈ S.filter (· ∈ supp), (-1 : ℝ) :=
      Finset.prod_congr rfl (fun i hi => by
        simp only [Finset.mem_filter, supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [hi.2, chi_one])
    have h2 : ∏ i ∈ S.filter (· ∉ supp), chi (x i) = 1 :=
      Finset.prod_eq_one (fun i hi => by
        simp only [Finset.mem_filter, supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rcases zmod2_cases (x i) with h | h
        · rw [h, chi_zero]
        · exact absurd h hi.2)
    rw [h1, h2, mul_one]
  -- Both equal ∏ over S ∩ supp of (-1), and the filter sets are equal
  rw [hlhs, hrhs]
  congr 1
  ext i; simp [Finset.mem_filter, and_comm]

/-- **Definition 1.28** (equivalence): Linear ↔ multiplicative for Boolean-valued functions. -/
theorem isLinear_iff_isMultiplicative (f : BooleanFunction n) (hf : IsBooleanValued f) :
    IsLinear f ↔ IsMultiplicative f :=
  ⟨isLinear_isMultiplicative f, isMultiplicative_isLinear f hf⟩

/-! ### Helpers for §1.5 (set density properties) -/

/-- `∑ x, 𝟙(x ∈ A) = |A|` (as reals). -/
private theorem indicator_sum_eq_card (A : Finset (Cube n)) :
    ∑ x : Cube n, (𝟙 (· ∈ A)) x = ↑A.card := by
  simp only [indicator]; norm_cast; simp

/-- The expectation of an indicator is positive when the set is nonempty. -/
theorem expect_indicator_pos (A : Finset (Cube n)) (hA : A.Nonempty) :
    0 < 𝔼[𝟙 (· ∈ A)] := by
  simp only [expect_unfold]; rw [indicator_sum_eq_card]
  exact mul_pos (by positivity) (Nat.cast_pos.mpr hA.card_pos)

/-- For nonempty `A`, `setDensity A` is a valid probability density. -/
theorem setDensity_isDensity_proof (A : Finset (Cube n)) (hA : A.Nonempty) :
    IsDensity (setDensity A) := by
  have hpos := expect_indicator_pos A hA
  constructor
  · intro x; unfold setDensity
    apply mul_nonneg
    · positivity
    · unfold indicator; split_ifs <;> linarith
  · show 𝔼[fun x => (1 / 𝔼[𝟙 (· ∈ A)]) * (𝟙 (· ∈ A)) x] = 1
    rw [show (fun x => (1 / 𝔼[𝟙 (· ∈ A)]) * (𝟙 (· ∈ A)) x) =
      (fun x => (1 / 𝔼[𝟙 (· ∈ A)]) * (fun x => (𝟙 (· ∈ A)) x) x) from rfl]
    rw [expect_scale]
    exact one_div_mul_cancel (ne_of_gt hpos)

/-- **Fact 1.23** (general): `𝓕 φ_A S = (1/|A|) · ∑_{x ∈ A} χ_S(x)`. -/
theorem fourierCoeff_setDensity_proof (A : Finset (Cube n)) (hA : A.Nonempty)
    (S : Finset (Fin n)) :
    𝓕 (setDensity A) S = (1 / A.card) * ∑ x ∈ A, (χ S) x := by
  have hApos : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hpos := expect_indicator_pos A hA
  simp only [fourierCoeff, inner_def, setDensity]
  -- Rewrite 𝔼[𝟙(· ∈ A)] using the card formula
  have hexpect : 𝔼[𝟙 (· ∈ A)] = ↑A.card / 2 ^ n := by
    simp only [expect_unfold]; rw [indicator_sum_eq_card]; ring
  rw [hexpect]
  -- Simplify the indicator product: 𝟙(x ∈ A) * χ S x = if x ∈ A then χ S x else 0
  simp_rw [show ∀ x : Cube n,
    1 / (↑A.card / 2 ^ n) * (𝟙 (· ∈ A)) x * (χ S) x =
    1 / (↑A.card / 2 ^ n) * (if x ∈ A then (χ S) x else 0) from by
    intro x; unfold indicator; split_ifs <;> ring]
  rw [← Finset.mul_sum, ← Finset.sum_filter (p := fun x : Cube n => x ∈ A)
    (f := fun x : Cube n => (χ S) x), Finset.filter_mem_eq_inter, Finset.univ_inter]
  field_simp

end BooleanAnalysis.Internal

end Complexity

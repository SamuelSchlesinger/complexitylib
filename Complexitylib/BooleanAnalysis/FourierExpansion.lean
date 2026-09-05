/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.FourierExpansion.Internal
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Boolean functions and Fourier analysis

This file contains the main Chapter 1 results and the Chapter 2 foundations on
noise and influence from "Analysis of Boolean Functions" by Ryan O'Donnell.

## References

* Ryan O'Donnell, *Analysis of Boolean Functions*, Chapters 1–2.
-/


public section

namespace Complexity

namespace BooleanAnalysis

open Finset BigOperators

variable {n : ℕ}

/-! ### §1.2 The Fourier expansion theorem -/

/-- **Theorem 1.1** (Fourier expansion existence): Every function `f : 𝔽₂ⁿ → ℝ` can be
    expressed as `f(x) = ∑_S 𝓕 f S · (χ S) x`. -/
theorem fourier_expansion (f : BooleanFunction n) (x : Cube n) :
    f x = ∑ S : Finset (Fin n), 𝓕 f S * (χ S) x :=
  Internal.fourier_expansion_proof f x

/-- **Theorem 1.1** (Fourier uniqueness): If `f(x) = ∑_S c_S · χ_S(x)` for all `x`,
    then `c_S = 𝓕 f S` for all `S`. Together with `fourier_expansion`, this establishes
    the parity functions as an orthonormal basis for the space of functions `𝔽₂ⁿ → ℝ`. -/
theorem fourier_uniqueness (f : BooleanFunction n) (c : Finset (Fin n) → ℝ)
    (h : ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x) :
    ∀ S, c S = 𝓕 f S :=
  Internal.fourier_uniqueness_proof f c h

/-! ### §1.3 Orthonormality of parity functions -/

/-- **Equation 1.5**: `(χ S)(x + y) = (χ S) x · (χ S) y`. -/
theorem parityFun_add (S : Finset (Fin n)) (x y : Cube n) :
    (χ S) (x + y) = (χ S) x * (χ S) y :=
  Internal.parityFun_add S x y

/-- **Fact 1.6**: `(χ S) x · (χ T) x = (χ (S △ T)) x`. -/
theorem parityFun_mul (S T : Finset (Fin n)) (x : Cube n) :
    (χ S) x * (χ T) x = (χ (symmDiff S T)) x :=
  Internal.parityFun_mul S T x

/-- **Fact 1.7**: `𝔼[χ S] = 1` if `S = ∅` and `𝔼[χ S] = 0` if `S ≠ ∅`. -/
theorem expect_parityFun (S : Finset (Fin n)) :
    𝔼[χ S] = if S = ∅ then 1 else 0 :=
  Internal.expect_parityFun_proof S

/-- **Theorem 1.5** (orthonormality): The parity functions are orthonormal:
    `⟪χ S, χ T⟫ = 1` if `S = T` and `0` otherwise. -/
theorem parityFun_orthonormal (S T : Finset (Fin n)) :
    ⟪χ S, χ T⟫ = if S = T then 1 else 0 :=
  Internal.parityFun_orthonormal_proof S T

/-- **Theorem 1.5** (spanning): Every function `f : 𝔽₂ⁿ → ℝ` is a linear combination
    of parity functions. Together with `parityFun_orthonormal`, this establishes
    that the parity functions form an orthonormal basis for the space of functions
    `𝔽₂ⁿ → ℝ`. -/
theorem parityFun_span (f : BooleanFunction n) :
    ∃ c : Finset (Fin n) → ℝ, ∀ x, f x = ∑ S : Finset (Fin n), c S * (χ S) x :=
  ⟨𝓕 f, fourier_expansion f⟩

/-! ### §1.4 Basic Fourier formulas -/

/-- **Proposition 1.8**: `𝓕 f S = ⟪f, χ S⟫`. This is true by definition. -/
theorem fourierCoeff_eq_inner (f : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 f S = ⟪f, χ S⟫ := rfl

/-- **Parseval's Theorem**: `⟪f, f⟫ = ∑ S, (𝓕 f S) ^ 2`. -/
theorem parseval (f : BooleanFunction n) :
    ⟪f, f⟫ = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 :=
  Internal.parseval_proof f

/-- **Parseval's Theorem** (Boolean case): For Boolean-valued `f`,
    `∑ S, (𝓕 f S) ^ 2 = 1`. -/
theorem parseval_boolean (f : BooleanFunction n) (hf : IsBooleanValued f) :
    ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 = 1 :=
  Internal.parseval_boolean_proof f hf

/-- The inner product `⟪f, f⟫` is nonneg. -/
theorem inner_self_nonneg' (f : BooleanFunction n) : 0 ≤ ⟪f, f⟫ := by
  rw [real_inner_self_eq_norm_sq]; positivity

/-- `‖f‖₂² = ⟪f, f⟫`. -/
theorem norm_sq_eq_inner (f : BooleanFunction n) : ‖f‖₂ ^ 2 = ⟪f, f⟫ :=
  (real_inner_self_eq_norm_sq f).symm

/-- `‖f‖₂² = ∑_S (𝓕 f S)²` (Parseval via L² norm). -/
theorem norm_sq_eq_sum_fourierCoeff_sq (f : BooleanFunction n) :
    ‖f‖₂ ^ 2 = ∑ S : Finset (Fin n), (𝓕 f S) ^ 2 := by
  rw [norm_sq_eq_inner, parseval]

/-- **Parseval, partitioned by degree**: summing the Fourier weight at each degree
    `k = 0, …, n` recovers `⟪f, f⟫`. Every coordinate set `S ⊆ [n]` has
    `|S| ≤ n`, so grouping the Fourier weights by `|S|` reassembles Parseval's
    total. This is the identity behind the degree/weight distribution `𝐖`. -/
theorem sum_fourierWeightAtDegree (f : BooleanFunction n) :
    ∑ k ∈ Finset.range (n + 1), 𝐖 f k = ⟪f, f⟫ := by
  have hle : ∀ S : Finset (Fin n), S.card ≤ n := fun S => by
    simpa using Finset.card_le_univ S
  simp only [fourierWeightAtDegree, fourierWeight]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hle S)))]
  exact (parseval f).symm

/-- **The degree decomposition of `f`**: summing the degree-`k` parts `f^{=k}`
    over `k = 0, …, n` reconstructs `f` pointwise. This regroups the Fourier
    expansion `f = ∑_S 𝓕 f S · χ_S` by `|S|`, and is the starting point for the
    low-degree / degree-concentration results used in small-depth-circuit lower
    bounds. -/
theorem sum_degreePart (f : BooleanFunction n) (x : Cube n) :
    ∑ k ∈ Finset.range (n + 1), degreePart f k x = f x := by
  have hle : ∀ S : Finset (Fin n), S.card ≤ n := fun S => by
    simpa using Finset.card_le_univ S
  simp only [degreePart]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hle S)))]
  exact (fourier_expansion f x).symm

/-- The Fourier weight at any degree is nonnegative (it is a sum of squares). -/
theorem fourierWeightAtDegree_nonneg (f : BooleanFunction n) (k : ℕ) : 0 ≤ 𝐖 f k := by
  simp only [fourierWeightAtDegree]
  apply Finset.sum_nonneg
  intro S _
  simp only [fourierWeight]
  positivity

/-- **Total Fourier weight of a Boolean function is one.** Summing the
    degree-`k` weights of a `±1`-valued function over all degrees gives `1`, since
    `⟪f, f⟫ = 𝔼[f²] = 𝔼[1] = 1`. This is what makes `k ↦ 𝐖 f k` a probability
    distribution on degrees — the *spectral sample* of `f`. -/
theorem sum_fourierWeightAtDegree_boolean (f : BooleanFunction n)
    (hf : IsBooleanValued f) : ∑ k ∈ Finset.range (n + 1), 𝐖 f k = 1 := by
  rw [sum_fourierWeightAtDegree, parseval]
  exact parseval_boolean f hf

/-- **The degree-`≤ n` part is all of `f`.** Every coordinate set has size at most
    `n`, so truncating at degree `n` keeps every Fourier term: `f^{≤n} = f`. -/
theorem lowDegreePart_card (f : BooleanFunction n) (x : Cube n) :
    lowDegreePart f n x = f x := by
  have hfilter : (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ n)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro S _
    simpa using Finset.card_le_univ S
  simp only [lowDegreePart, hfilter]
  exact (fourier_expansion f x).symm

/-- **No mass above degree `n`.** There are no coordinate sets of size greater
    than `n`, so every degree part `f^{=k}` with `k > n` is identically zero. -/
theorem degreePart_eq_zero_of_lt (f : BooleanFunction n) (x : Cube n) {k : ℕ}
    (hk : n < k) : degreePart f k x = 0 := by
  have hfilter : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = k)) = ∅ := by
    apply Finset.filter_false_of_mem
    intro S _
    have : S.card ≤ n := by simpa using Finset.card_le_univ S
    omega
  simp only [degreePart, hfilter, Finset.sum_empty]

/-- **No Fourier weight above degree `n`.** For `k > n` the degree-`k` weight
    vanishes, so the degree-weight sum `∑_{k=0}^n 𝐖 f k` already captures all of
    `f`'s spectral energy. -/
theorem fourierWeightAtDegree_eq_zero_of_lt (f : BooleanFunction n) {k : ℕ}
    (hk : n < k) : 𝐖 f k = 0 := by
  have hfilter : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = k)) = ∅ := by
    apply Finset.filter_false_of_mem
    intro S _
    have : S.card ≤ n := by simpa using Finset.card_le_univ S
    omega
  simp only [fourierWeightAtDegree, hfilter, Finset.sum_empty]

/-- **The low-degree part is the sum of exact-degree parts.** `f^{≤k} = ∑_{j≤k}
    f^{=j}`, obtained by grouping the coordinate sets of size `≤ k` by their exact
    size — the identity linking the two degree-truncation operators. -/
theorem lowDegreePart_eq_sum_degreePart (f : BooleanFunction n) (x : Cube n) (k : ℕ) :
    lowDegreePart f k x = ∑ j ∈ Finset.range (k + 1), degreePart f j x := by
  simp only [lowDegreePart, degreePart]
  rw [← Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k))
      (t := Finset.range (k + 1)) (g := fun S => S.card)
      (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2))]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine Finset.sum_congr ?_ (fun S _ => rfl)
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by omega, h⟩

/-- **Plancherel's Theorem**: `⟪f, g⟫ = ∑ S, (𝓕 f S) · (𝓕 g S)`. -/
theorem plancherel (f g : BooleanFunction n) :
    ⟪f, g⟫ = ∑ S : Finset (Fin n), (𝓕 f S) * (𝓕 g S) :=
  Internal.plancherel_proof f g

/-- **Proposition 1.9a**: For Boolean-valued `f, g`,
    `⟪f, g⟫ = Pr[f(x) = g(x)] - Pr[f(x) ≠ g(x)]`. -/
theorem inner_eq_agree_sub_disagree (f g : BooleanFunction n)
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    ⟪f, g⟫ = (1 - hammingDist f g) - hammingDist f g := by
  have := Internal.inner_add_two_hammingDist f g hf hg; linarith

/-- **Proposition 1.9b**: For Boolean-valued `f, g`,
    `⟪f, g⟫ = 1 - 2·dist(f, g)`. -/
theorem inner_eq_one_sub_two_dist (f g : BooleanFunction n)
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    ⟪f, g⟫ = 1 - 2 * hammingDist f g := by
  rw [inner_eq_agree_sub_disagree f g hf hg]; ring

/-- **Fact 1.12**: The mean of `f` equals its empty-set Fourier coefficient:
    `𝔼[f] = 𝓕 f ∅`. -/
theorem expect_eq_fourierCoeff_empty (f : BooleanFunction n) :
    𝔼[f] = 𝓕 f ∅ := by
  rw [fourierCoeff_eq_inner (f := f) (S := ∅), inner_eq_expect (f := f) (g := χ ∅)]
  simp [Internal.parityFun_empty]

/-- **Proposition 1.13**: The variance of `f` in terms of Fourier coefficients:
    `Var[f] = ∑_{S ≠ ∅} (𝓕 f S)²`. -/
theorem variance_eq_sum_fourierCoeff_sq (f : BooleanFunction n) :
    Var[f] = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅),
      (𝓕 f S) ^ 2 := by
  have hef : 𝔼[fun x => f x ^ 2] = ⟪f, f⟫ := by
    rw [inner_eq_expect]; congr 1; ext x; ring
  simp only [variance]
  rw [hef, parseval, expect_eq_fourierCoeff_empty]
  have := Finset.sum_erase_eq_sub (f := fun S => (fourierCoeff f S) ^ 2)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [← this]
  congr 1
  ext S; simp [Finset.mem_erase, Finset.mem_filter, and_comm]

/-- **Fact 1.14**: For Boolean-valued `f`,
    `Var[f] = 1 - 𝔼[f]² = 4·Pr[f=1]·Pr[f=-1] ∈ [0, 1]`. -/
theorem variance_boolean (f : BooleanFunction n) (hf : IsBooleanValued f) :
    Var[f] = 1 - (𝔼[f]) ^ 2 := by
  unfold variance
  have h1 : 𝔼[fun x => f x ^ 2] = 1 := by
    rw [expect_unfold (f := fun x : Cube n => f x ^ 2)]
    have : ∀ x : Cube n, f x ^ 2 = 1 := by
      intro x; rcases hf x with h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    simp [Fintype.card_fin, ZMod.card]
  linarith

/-- **Fact 1.14** (probability form): For Boolean-valued `f`,
    `Var[f] = 4 · Pr[f = 1] · Pr[f = -1]`. -/
theorem variance_boolean_prob (f : BooleanFunction n) (hf : IsBooleanValued f) :
    Var[f] = 4 * Pr[fun x => f x = 1] * Pr[fun x => f x = -1] := by
  rw [variance_boolean f hf, Internal.expect_boolean_eq_prob_diff f hf]
  have := Internal.prob_boolean_sum_one f hf
  nlinarith [sq_nonneg (Pr[fun x => f x = 1] - Pr[fun x => f x = -1])]

/-- **Fact 1.14** (lower bound): For Boolean-valued `f`, `0 ≤ Var[f]`. -/
theorem variance_boolean_nonneg (f : BooleanFunction n) (hf : IsBooleanValued f) :
    0 ≤ Var[f] := by
  rw [variance_boolean f hf]
  have hexp := Internal.expect_boolean_eq_prob_diff f hf
  have hsum := Internal.prob_boolean_sum_one f hf
  have hp1 : 0 ≤ Pr[fun x => f x = 1] := Internal.prob_nonneg _
  have hp2 : 0 ≤ Pr[fun x => f x = -1] := Internal.prob_nonneg _
  nlinarith [sq_nonneg (𝔼[f])]

/-- **Fact 1.14** (upper bound): For Boolean-valued `f`, `Var[f] ≤ 1`. -/
theorem variance_boolean_le_one (f : BooleanFunction n) (hf : IsBooleanValued f) :
    Var[f] ≤ 1 := by
  rw [variance_boolean f hf]; nlinarith [sq_abs (𝔼[f])]

/-- **Proposition 1.15**: For Boolean-valued `f`, `2ε ≤ Var[f] ≤ 4ε`
    where `ε = min(dist(f, 1), dist(f, -1))`.

    Here `1` and `-1` denote the constant functions. -/
theorem variance_dist_bounds (f : BooleanFunction n) (hf : IsBooleanValued f) :
    let ε := min (hammingDist f (fun _ => 1)) (hammingDist f (fun _ => -1))
    2 * ε ≤ Var[f] ∧ Var[f] ≤ 4 * ε := by
  rw [Internal.hammingDist_const_one f hf, Internal.hammingDist_const_neg_one f hf]
  rw [variance_boolean_prob f hf]
  exact Internal.variance_dist_bounds_arith
    (Pr[fun x => f x = 1]) (Pr[fun x => f x = -1])
    (Internal.prob_nonneg _) (Internal.prob_nonneg _)
    (Internal.prob_boolean_sum_one f hf)

/-- **Proposition 1.16**: The covariance in terms of Fourier coefficients:
    `Cov[f, g] = ∑_{S ≠ ∅} (𝓕 f S) · (𝓕 g S)`. -/
theorem covariance_eq_sum_fourierCoeff (f g : BooleanFunction n) :
    Cov[f, g] = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅),
      (𝓕 f S) * (𝓕 g S) := by
  rw [covariance, ← inner_eq_expect]
  rw [plancherel, expect_eq_fourierCoeff_empty, expect_eq_fourierCoeff_empty]
  have := Finset.sum_erase_eq_sub (f := fun S => fourierCoeff f S * fourierCoeff g S)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [← this]
  congr 1
  ext S; simp [Finset.mem_erase, Finset.mem_filter, and_comm]

/-! ### §1.4 Spectral sample distribution -/

/-- **Definition 1.18** (Spectral sample): For Boolean-valued `f`, the squared
    Fourier coefficients `(𝓕 f S)²` form a probability distribution on `2^[n]`,
    represented as a `PMF`. By Parseval's theorem, `∑_S (𝓕 f S)² = 1`. -/
noncomputable def spectralSample (f : BooleanFunction n) (hf : IsBooleanValued f) :
    PMF (Finset (Fin n)) :=
  PMF.ofFintype (fun S => ENNReal.ofReal (fourierWeight f S)) (by
    simp only [fourierWeight,
      ← ENNReal.ofReal_sum_of_nonneg (fun S _ => sq_nonneg (𝓕 f S))]
    rw [parseval_boolean f hf]; simp)

/-! ### §1.5 Probability densities and convolution -/

/-- **Fact 1.21**: `𝔼[f·g] = ⟪f, g⟫` for all `f, g`.

    The book states this for densities `φ`, interpreting `𝔼_{y ~ φ}[g(y)] = ⟪φ, g⟫`,
    but the identity holds for all functions since our inner product is defined as
    `⟪f, g⟫ = 𝔼[f·g]`. -/
theorem expect_mul_eq_inner (f g : BooleanFunction n) :
    𝔼[fun x => f x * g x] = ⟪f, g⟫ :=
  (inner_eq_expect f g).symm

/-- **Definition 1.22** (Set density is a density): For nonempty `A ⊆ 𝔽₂ⁿ`,
    the set density `φ_A` is a valid probability density. -/
theorem setDensity_isDensity (A : Finset (Cube n)) (hA : A.Nonempty) :
    IsDensity (setDensity A) :=
  Internal.setDensity_isDensity_proof A hA

/-- Convert a density on `𝔽₂ⁿ` to a Mathlib `PMF`, bridging the book's real-valued
    density convention with Mathlib's measure-theoretic probability API.

    The book's density satisfies `𝔼[φ] = (1/2ⁿ) · ∑_x φ(x) = 1`, so
    `∑_x φ(x) = 2ⁿ`. The PMF assigns mass `φ(x) / 2ⁿ` to each `x`. -/
noncomputable def IsDensity.toPMF {φ : BooleanFunction n} (hφ : IsDensity φ) :
    PMF (Cube n) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (φ x / 2 ^ n)) (by
    have hsum : ∑ x : Cube n, φ x / 2 ^ n = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul (s := Finset.univ) (f := fun x : Cube n => φ x)
        (a := ((2 : ℝ) ^ n)⁻¹)]
      have h := hφ.expect_one; rw [expect_unfold (f := φ)] at h
      have h2n : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
      rw [show (∑ x : Cube n, φ x) * (2 ^ n)⁻¹ = 1 / 2 ^ n * ∑ x, φ x from by ring]
      linarith
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
      div_nonneg (hφ.nonneg x) (by positivity)), hsum]
    simp)

/-- **Fact 1.23**: Every Fourier coefficient of `φ_{0}` is 1; i.e.,
    `φ_{0}(y) = ∑_S (χ S) y`. -/
theorem setDensity_singleton_zero :
    ∀ y : Cube n, setDensity ({0} : Finset (Cube n)) y =
      ∑ S : Finset (Fin n), (χ S) y :=
  Internal.setDensity_singleton_zero_proof

/-- **Fact 1.23** (Fourier coefficient form): Every Fourier coefficient of
    `φ_{0}` is `1`, i.e., `𝓕 φ_{0} S = 1` for all `S`. -/
theorem fourierCoeff_setDensity_singleton_zero (S : Finset (Fin n)) :
    𝓕 (setDensity ({0} : Finset (Cube n))) S = 1 :=
  Internal.fourierCoeff_setDensity_singleton_zero_proof S

/-- **Fact 1.23** (general form): The Fourier coefficients of the set density `φ_A`
    are `𝓕 φ_A S = (1/|A|) · ∑_{x ∈ A} χ_S(x)`, i.e., the uniform average of `χ_S`
    over `A`. -/
theorem fourierCoeff_setDensity (A : Finset (Cube n)) (hA : A.Nonempty)
    (S : Finset (Fin n)) :
    𝓕 (setDensity A) S = (1 / A.card) * ∑ x ∈ A, (χ S) x :=
  Internal.fourierCoeff_setDensity_proof A hA S

/-- **Proposition 1.25**: `(f ⊛ g)(x) = 𝔼_y[f(y)·g(x + y)]`.

    The book states this for densities, but our definition of convolution makes
    this hold definitionally for all functions. -/
theorem convolution_eq (f g : BooleanFunction n) (x : Cube n) :
    (f ⊛ g) x = 𝔼[fun y => f y * g (x + y)] := rfl

/-- **Proposition 1.26**: If `φ` and `ψ` are both densities, then `φ ⊛ ψ`
    is also a density. -/
theorem convolution_density_isDensity (φ ψ : BooleanFunction n)
    (hφ : IsDensity φ) (hψ : IsDensity ψ) :
    IsDensity (φ ⊛ ψ) :=
  Internal.convolution_density_isDensity_proof φ ψ hφ hψ

/-- **Theorem 1.27** (Convolution theorem):
    `𝓕 (f ⊛ g) S = (𝓕 f S) · (𝓕 g S)`. -/
theorem fourierCoeff_convolution (f g : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 (f ⊛ g) S = (𝓕 f S) * (𝓕 g S) :=
  Internal.fourierCoeff_convolution_proof f g S

/-! ### §1.6 Linearity characterizations -/

/-- **Definition 1.28** (equivalence): For Boolean-valued `f`, linearity is
    equivalent to multiplicativity:
    `f = χ S` for some `S` iff `f(x+y) = f(x)·f(y)` for all `x, y`. -/
theorem isLinear_iff_isMultiplicative (f : BooleanFunction n) (hf : IsBooleanValued f) :
    IsLinear f ↔ IsMultiplicative f :=
  Internal.isLinear_iff_isMultiplicative f hf

/-! ### §1.6 The BLR test -/

/-- **Equation 1.10**: The BLR acceptance probability in terms of Fourier coefficients:
    `Pr_{x,y}[f(x)·f(y) = f(x+y)] = 1/2 + 1/2 · ∑_S (𝓕 f S)³`. -/
theorem blrAcceptProb_eq (f : BooleanFunction n) (hf : IsBooleanValued f) :
    blrAcceptProb f = 1 / 2 + 1 / 2 * ∑ S : Finset (Fin n), (𝓕 f S) ^ 3 :=
  Internal.blrAcceptProb_eq_proof f hf

/-- **BLR completeness**: If `f` is linear (i.e., `f = χ_S` for some `S`),
    then the BLR test accepts with probability 1. -/
theorem blr_completeness (f : BooleanFunction n) (hf : IsLinear f) :
    blrAcceptProb f = 1 :=
  Internal.blr_completeness_proof f hf

/-- **Theorem 1.30** (BLR soundness): If the BLR test accepts `f` with
    probability `1 - ε`, then `f` is `ε`-close to being linear. -/
theorem blr_soundness (f : BooleanFunction n) (hf : IsBooleanValued f) (ε : ℝ)
    (hε : blrAcceptProb f ≥ 1 - ε) :
    IsCloseToProperty f IsLinear ε :=
  Internal.blr_soundness_proof f hf ε hε

/-- **Proposition 1.31** (Local correctability): If `f` is `ε`-close to the
    linear function `χ S`, then for every `x`, the algorithm
    "choose `y` uniformly, output `f(y) · f(x + y)`" outputs `(χ S) x`
    with probability at least `1 - 2ε`. -/
theorem local_correctability (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) (hclose : IsClose f (χ S) ε) (x : Cube n) :
    Pr[fun y => f y * f (x + y) = (χ S) x] ≥ 1 - 2 * ε :=
  Internal.local_correctability_proof f hf S ε hclose x

/-- **The degree-0 part is the mean.** The only coordinate set of size `0` is `∅`,
    and `χ_∅ ≡ 1`, so `f^{=0}` is the constant function `𝔼[f]`. -/
theorem degreePart_zero (f : BooleanFunction n) (x : Cube n) :
    degreePart f 0 x = 𝔼[f] := by
  have hfilter : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = 0)) = {∅} := by
    ext S
    simp [Finset.card_eq_zero]
  simp only [degreePart, hfilter, Finset.sum_singleton, parityFun, Finset.prod_empty, mul_one]
  exact (expect_eq_fourierCoeff_empty f).symm

/-! ### Linearity of the Fourier transform

The Fourier coefficient `𝓕 · S = ⟪·, χ S⟫` is linear in its function argument,
inherited directly from linearity of the inner product. -/

/-- Fourier coefficients are additive: `𝓕 (f + g) S = 𝓕 f S + 𝓕 g S`. -/
theorem fourierCoeff_add (f g : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 (f + g) S = 𝓕 f S + 𝓕 g S := by
  simp only [fourierCoeff, inner_add_left]

/-- Fourier coefficients are homogeneous: `𝓕 (c • f) S = c · 𝓕 f S`. -/
theorem fourierCoeff_smul (c : ℝ) (f : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 (c • f) S = c * 𝓕 f S := by
  simp only [fourierCoeff, real_inner_smul_left]

/-- The zero function has all Fourier coefficients zero. -/
@[simp] theorem fourierCoeff_zero (S : Finset (Fin n)) :
    𝓕 (0 : BooleanFunction n) S = 0 := by
  simp only [fourierCoeff, inner_zero_left]

/-- Fourier coefficients respect negation: `𝓕 (-f) S = -𝓕 f S`. -/
theorem fourierCoeff_neg (f : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 (-f) S = -𝓕 f S := by
  simp only [fourierCoeff, inner_neg_left]

/-- Fourier coefficients respect subtraction: `𝓕 (f - g) S = 𝓕 f S - 𝓕 g S`. -/
theorem fourierCoeff_sub (f g : BooleanFunction n) (S : Finset (Fin n)) :
    𝓕 (f - g) S = 𝓕 f S - 𝓕 g S := by
  simp only [fourierCoeff, inner_sub_left]

/-- **Fourier uniqueness.** Two functions with identical Fourier coefficients are
    equal: the difference has zero norm by Parseval. The convenient way to prove a
    functional identity `f = g` by checking spectra. -/
theorem fourierCoeff_ext {f g : BooleanFunction n} (h : ∀ S, 𝓕 f S = 𝓕 g S) : f = g := by
  have hzero : ‖f - g‖₂ ^ 2 = 0 := by
    rw [norm_sq_eq_sum_fourierCoeff_sq]
    apply Finset.sum_eq_zero
    intro S _
    rw [fourierCoeff_sub, h S]; ring
  exact sub_eq_zero.mp
    (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero))

/-- **A parity function is its own indicator in Fourier space.** By
    orthonormality, `𝓕 χ_S T = 1` if `T = S` and `0` otherwise — the parities are
    exactly the Fourier basis vectors. -/
theorem fourierCoeff_parityFun (S T : Finset (Fin n)) :
    𝓕 (χ S) T = if S = T then 1 else 0 := by
  rw [fourierCoeff_eq_inner, parityFun_orthonormal]

/-- **Multiplying by a parity shifts the frequency by symmetric difference**:
    `𝓕(χ_S · g, T) = 𝓕(g, S △ T)`. Since `χ_S · χ_T = χ_{S△T}`, multiplication by a
    character permutes the Fourier basis, so it relabels every coefficient of `g`. -/
theorem fourierCoeff_parityFun_mul (S : Finset (Fin n)) (g : BooleanFunction n)
    (T : Finset (Fin n)) :
    𝓕 (fun x => (χ S) x * g x) T = 𝓕 g (symmDiff S T) := by
  rw [fourierCoeff_eq_inner (f := fun x : Cube n => (χ S) x * g x) (S := T),
    inner_eq_expect (f := fun x : Cube n => (χ S) x * g x) (g := χ T),
    fourierCoeff_eq_inner (f := g) (S := symmDiff S T),
    inner_eq_expect (f := g) (g := χ (symmDiff S T))]
  refine Finset.expect_congr rfl fun x _ => ?_
  rw [← parityFun_mul]; ring

/-- The degree-`k` part is additive, inheriting linearity from the Fourier
    coefficients: `(f + g)^{=k} = f^{=k} + g^{=k}`. -/
theorem degreePart_add (f g : BooleanFunction n) (k : ℕ) (x : Cube n) :
    degreePart (f + g) k x = degreePart f k x + degreePart g k x := by
  simp only [degreePart, fourierCoeff_add, add_mul]
  rw [Finset.sum_add_distrib]

/-- The degree-`k` part is homogeneous: `(c • f)^{=k} = c · f^{=k}`. -/
theorem degreePart_smul (c : ℝ) (f : BooleanFunction n) (k : ℕ) (x : Cube n) :
    degreePart (c • f) k x = c * degreePart f k x := by
  simp only [degreePart, fourierCoeff_smul, mul_assoc]
  rw [← Finset.mul_sum]

/-- The degree-`k` part respects subtraction: `(f - g)^{=k} = f^{=k} - g^{=k}`. -/
theorem degreePart_sub (f g : BooleanFunction n) (k : ℕ) (x : Cube n) :
    degreePart (f - g) k x = degreePart f k x - degreePart g k x := by
  simp only [degreePart, fourierCoeff_sub, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- **Fourier coefficients of the degree-`k` projection.** The projection `f^{=k}`
    keeps exactly the level-`k` Fourier coefficients and zeroes the rest:
    `𝓕 f^{=k} T = 𝓕 f T` if `|T| = k`, and `0` otherwise. This is `f^{=k}`'s
    defining property as an orthogonal projection onto the degree-`k` subspace. -/
theorem fourierCoeff_degreePart (f : BooleanFunction n) (k : ℕ) (T : Finset (Fin n)) :
    𝓕 (degreePart f k) T = if T.card = k then 𝓕 f T else 0 := by
  have hdp : (degreePart f k) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k), (𝓕 f S) • (χ S) := by
    ext x
    simp only [degreePart, BooleanFunction.sum_apply, BooleanFunction.smul_apply]
  rw [fourierCoeff_eq_inner, hdp, sum_inner]
  simp only [real_inner_smul_left, parityFun_orthonormal, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Distinct degree parts are orthogonal.** For `j ≠ k` the projections `f^{=j}`
    and `g^{=k}` live in orthogonal Fourier subspaces, so `⟪f^{=j}, g^{=k}⟫ = 0`.
    This is what makes the degree decomposition `f = ∑ₖ f^{=k}` an *orthogonal*
    decomposition — the basis for Parseval-by-degree and degree concentration. -/
theorem degreePart_inner_eq_zero (f g : BooleanFunction n) {j k : ℕ} (hjk : j ≠ k) :
    ⟪degreePart f j, degreePart g k⟫ = 0 := by
  rw [plancherel]
  apply Finset.sum_eq_zero
  intro S _
  rw [fourierCoeff_degreePart, fourierCoeff_degreePart]
  by_cases hj : S.card = j
  · rw [ite_eq_right (show ¬ S.card = k by omega), mul_zero]
  · rw [ite_eq_right hj, zero_mul]

/-- **The degree-`k` weight is the squared length of the degree-`k` part.**
    `⟪f^{=k}, f^{=k}⟫ = 𝐖 f k = ∑_{|S|=k} (𝓕 f S)²` — Parseval restricted to level
    `k`. -/
theorem degreePart_self_inner (f : BooleanFunction n) (k : ℕ) :
    ⟪degreePart f k, degreePart f k⟫ = 𝐖 f k := by
  rw [plancherel, fourierWeightAtDegree, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  simp only [fourierCoeff_degreePart, fourierWeight]
  by_cases hS : S.card = k <;> simp [hS, pow_two]

/-- The L² norm form of `degreePart_self_inner`: `‖f^{=k}‖₂² = 𝐖 f k`. -/
theorem norm_sq_degreePart (f : BooleanFunction n) (k : ℕ) :
    ‖degreePart f k‖₂ ^ 2 = 𝐖 f k := by
  rw [norm_sq_eq_inner, degreePart_self_inner]

/-- **Parities are homogeneous.** The degree-`k` part of the parity `χ_S` is `χ_S`
    itself when `|S| = k`, and `0` otherwise — `χ_S` lives entirely in the
    degree-`|S|` subspace. -/
theorem degreePart_parityFun (S : Finset (Fin n)) (k : ℕ) (x : Cube n) :
    degreePart (χ S) k x = if S.card = k then (χ S) x else 0 := by
  simp only [degreePart, fourierCoeff_parityFun, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The function-level degree decomposition of the low-degree part:
    `f^{≤k} = ∑_{j≤k} f^{=j}` as `BooleanFunction`s (the pointwise
    `lowDegreePart_eq_sum_degreePart` promoted to a function equality). -/
theorem lowDegreePart_eq_sum (f : BooleanFunction n) (k : ℕ) :
    (lowDegreePart f k : BooleanFunction n)
      = ∑ j ∈ Finset.range (k + 1), degreePart f j := by
  ext x
  rw [BooleanFunction.sum_apply]
  exact lowDegreePart_eq_sum_degreePart f x k

/-- **Energy of the low-degree part.** By orthogonality of the degree parts, the
    squared length of `f^{≤k}` is the sum of the low-degree weights:
    `⟪f^{≤k}, f^{≤k}⟫ = ∑_{j≤k} 𝐖 f j`. -/
theorem lowDegreePart_self_inner (f : BooleanFunction n) (k : ℕ) :
    ⟪lowDegreePart f k, lowDegreePart f k⟫ = ∑ j ∈ Finset.range (k + 1), 𝐖 f j := by
  rw [lowDegreePart_eq_sum, sum_inner]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [inner_sum, Finset.sum_eq_single j
    (fun i _ hij => degreePart_inner_eq_zero f f (Ne.symm hij))
    (fun hj' => absurd hj hj')]
  exact degreePart_self_inner f j

/-- **The degree of an `n`-bit function is at most `n`.** Every coordinate set
    has size `≤ n`, so the supremum defining `deg(f)` is bounded by `n`. -/
theorem degree_le (f : BooleanFunction n) : degree f ≤ (n : WithBot ℕ) := by
  unfold degree
  apply Finset.sup_le
  intro S _
  exact WithBot.coe_le_coe.mpr (by simpa using Finset.card_le_univ S)

/-- The degree-0 Fourier weight is the squared mean coefficient:
    `𝐖 f 0 = (𝓕 f ∅)²` (the only size-`0` coordinate set is `∅`). -/
theorem fourierWeightAtDegree_zero (f : BooleanFunction n) : 𝐖 f 0 = (𝓕 f ∅) ^ 2 := by
  have hfilter : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = 0)) = {∅} := by
    ext S
    simp [Finset.card_eq_zero]
  simp only [fourierWeightAtDegree, hfilter, Finset.sum_singleton, fourierWeight]

/-- Each degree weight is at most the total energy: `𝐖 f k ≤ ⟪f, f⟫`. A trivial
    but useful spectral concentration bound (one level can hold no more mass than
    the whole). -/
theorem fourierWeightAtDegree_le_self_inner (f : BooleanFunction n) (k : ℕ) :
    𝐖 f k ≤ ⟪f, f⟫ := by
  by_cases hk : k ≤ n
  · rw [← sum_fourierWeightAtDegree]
    exact Finset.single_le_sum (fun j _ => fourierWeightAtDegree_nonneg f j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · rw [fourierWeightAtDegree_eq_zero_of_lt f (by omega)]
    exact inner_self_nonneg' f

/-- **Faithfulness of the Fourier transform.** A function is zero iff all of its
    Fourier coefficients vanish — the parities separate points, so the transform
    is injective. -/
theorem eq_zero_iff_fourierCoeff (f : BooleanFunction n) :
    f = 0 ↔ ∀ S, 𝓕 f S = 0 := by
  refine ⟨fun hf S => by rw [hf]; exact fourierCoeff_zero S, fun h => ?_⟩
  ext x
  rw [fourier_expansion f x]
  simp only [h, zero_mul, Finset.sum_const_zero, BooleanFunction.zero_apply]

/-- **The Fourier transform is injective.** Two functions are equal iff they have
    the same Fourier coefficients at every coordinate set. -/
theorem eq_iff_fourierCoeff (f g : BooleanFunction n) :
    f = g ↔ ∀ S, 𝓕 f S = 𝓕 g S := by
  rw [← sub_eq_zero, eq_zero_iff_fourierCoeff]
  simp only [fourierCoeff_sub, sub_eq_zero]

/-- **Distinct coordinate sets give distinct parities.** The map `S ↦ χ_S` is
    injective, so the parity functions are genuinely `2ⁿ` distinct basis vectors. -/
theorem parityFun_injective :
    Function.Injective (fun S : Finset (Fin n) => (χ S : BooleanFunction n)) := by
  intro S T h
  have hS : 𝓕 (χ S) S = 𝓕 (χ T) S := (eq_iff_fourierCoeff (χ S) (χ T)).mp h S
  simp only [fourierCoeff_parityFun] at hS
  split_ifs at hS with hSS hTS <;> simp_all

/-- **Parity functions are Boolean-valued.** Each `χ_S(x)` is a product of `±1`
    values, hence itself `±1`. -/
theorem isBooleanValued_parityFun (S : Finset (Fin n)) : IsBooleanValued (χ S) := by
  intro x
  simp only [parityFun]
  refine Finset.prod_induction _ (fun a => a = 1 ∨ a = -1) ?_ ?_ ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · left; rfl
  · intro i _
    unfold chi
    split
    · left; rfl
    · right; rfl

/-- **Variance is the non-constant energy.** `Var[f] = ⟪f, f⟫ - 𝐖 f 0`: total
    spectral energy minus the degree-0 (mean) weight. Splits the Parseval sum by
    removing the `∅` term. -/
theorem variance_eq_self_inner_sub_fourierWeightAtDegree_zero (f : BooleanFunction n) :
    Var[f] = ⟪f, f⟫ - 𝐖 f 0 := by
  have hsingle : (Finset.univ.filter (fun S : Finset (Fin n) => S = ∅)) = {∅} := by
    ext S; simp
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S => S = ∅) (fun S => (𝓕 f S) ^ 2)
  rw [hsingle, Finset.sum_singleton] at hsplit
  rw [variance_eq_sum_fourierCoeff_sq, parseval, fourierWeightAtDegree_zero,
    eq_sub_iff_add_eq, add_comm]
  exact hsplit

/-- **Variance is the weight above degree 0.** `Var[f] = ∑_{k≥1} 𝐖 f k` — the
    total Fourier weight at all positive degrees. -/
theorem variance_eq_sum_fourierWeightAtDegree_pos (f : BooleanFunction n) :
    Var[f] = ∑ k ∈ Finset.range n, 𝐖 f (k + 1) := by
  rw [variance_eq_self_inner_sub_fourierWeightAtDegree_zero, ← sum_fourierWeightAtDegree,
    Finset.sum_range_succ']
  ring

/-- **Variance is nonnegative** for every real-valued function on the cube (not
    only Boolean ones): it is a sum of nonnegative Fourier weights. -/
theorem variance_nonneg (f : BooleanFunction n) : 0 ≤ Var[f] := by
  rw [variance_eq_sum_fourierWeightAtDegree_pos]
  exact Finset.sum_nonneg (fun k _ => fourierWeightAtDegree_nonneg f (k + 1))

/-- For a Boolean-valued function, each degree weight is at most `1`, since the
    total weight `∑_k 𝐖 f k = ⟪f, f⟫ = 1`. -/
theorem fourierWeightAtDegree_le_one (f : BooleanFunction n) (hf : IsBooleanValued f)
    (k : ℕ) : 𝐖 f k ≤ 1 := by
  have h := fourierWeightAtDegree_le_self_inner f k
  rw [parseval, parseval_boolean f hf] at h
  exact h

/-- Every Fourier coefficient of a Boolean-valued function is bounded:
    `(𝓕 f S)² ≤ 1`, since it is one term of the Parseval sum `∑_T (𝓕 f T)² = 1`. -/
theorem fourierCoeff_sq_le_one (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) : (𝓕 f S) ^ 2 ≤ 1 := by
  rw [← parseval_boolean f hf]
  exact Finset.single_le_sum (fun T _ => sq_nonneg _) (Finset.mem_univ S)

/-- Every Fourier coefficient of a Boolean-valued function lies in `[-1, 1]`. -/
theorem abs_fourierCoeff_le_one (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) : |𝓕 f S| ≤ 1 := by
  have h := fourierCoeff_sq_le_one f hf S
  rw [abs_le]
  constructor
  · nlinarith [h, sq_nonneg (𝓕 f S + 1)]
  · nlinarith [h, sq_nonneg (𝓕 f S - 1)]

/-! ### §2.4 Noise stability (spectral definition)

The **noise stability** of `f` at correlation `ρ`, `Stabᵨ[f]`, measures how much
`f` agrees with itself under `ρ`-correlated inputs. Here it is defined directly by
its spectral formula `Stabᵨ[f] = ∑_S ρ^{|S|} 𝓕(f,S)²` (O'Donnell, Theorem 2.49),
which sidesteps the correlated-input distribution while capturing all the
first-order facts: at `ρ = 1` it is the total Fourier power `⟪f, f⟫`; at `ρ = 0`
it is the squared mean; and on `ρ ∈ [0, 1]` it interpolates monotonically between
them, bounded by `⟪f, f⟫` (which is `1` for Boolean `f`). -/

/-- The **noise stability** of `f` at correlation `ρ`, defined spectrally:
    `Stabᵨ[f] = ∑_S ρ^{|S|} · 𝓕(f, S)²`. -/
noncomputable def noiseStability (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  ∑ S : Finset (Fin n), ρ ^ S.card * (𝓕 f S) ^ 2

/-- At `ρ = 1`, noise stability is the total Fourier power `⟪f, f⟫` (Parseval). -/
theorem noiseStability_one (f : BooleanFunction n) : noiseStability 1 f = ⟪f, f⟫ := by
  simp only [noiseStability, one_pow, one_mul]
  rw [parseval]

/-- Noise stability is nonnegative for `0 ≤ ρ`. -/
theorem noiseStability_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (f : BooleanFunction n) :
    0 ≤ noiseStability ρ f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hρ _) (sq_nonneg _)

/-- For `ρ ∈ [0, 1]`, noise stability is bounded above by the total power `⟪f, f⟫`
    (each spectral weight is damped by `ρ^{|S|} ≤ 1`). -/
theorem noiseStability_le_self_inner {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (f : BooleanFunction n) : noiseStability ρ f ≤ ⟪f, f⟫ := by
  rw [parseval, noiseStability]
  refine Finset.sum_le_sum fun S _ => ?_
  calc ρ ^ S.card * (𝓕 f S) ^ 2 ≤ 1 * (𝓕 f S) ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hρ0 hρ1) (sq_nonneg _)
    _ = (𝓕 f S) ^ 2 := one_mul _

/-- At `ρ = 0`, only the empty-set term survives: `Stab₀[f] = 𝓕(f, ∅)²`. -/
theorem noiseStability_zero (f : BooleanFunction n) :
    noiseStability 0 f = (𝓕 f ∅) ^ 2 := by
  rw [noiseStability, Finset.sum_eq_single ∅]
  · simp
  · intro S _ hS
    have hc : S.card ≠ 0 := by simp [Finset.card_eq_zero, hS]
    rw [zero_pow hc, zero_mul]
  · intro h; simp at h

/-- At `ρ = 0`, noise stability is the squared mean `𝔼[f]²` (since `𝔼[f] = 𝓕(f, ∅)`). -/
theorem noiseStability_zero_eq_expect_sq (f : BooleanFunction n) :
    noiseStability 0 f = 𝔼[f] ^ 2 := by
  rw [noiseStability_zero, expect_eq_fourierCoeff_empty]

/-- For a Boolean-valued function and `ρ ∈ [0, 1]`, noise stability is at most `1`
    (its total power is `1`). -/
theorem noiseStability_boolean_le_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (f : BooleanFunction n) (hf : IsBooleanValued f) : noiseStability ρ f ≤ 1 := by
  have h := noiseStability_le_self_inner hρ0 hρ1 f
  rwa [parseval, parseval_boolean f hf] at h

/-- For `ρ ≥ 0`, noise stability is bounded below by the squared mean `𝔼[f]²` — the
    `S = ∅` term of the spectral sum, which survives with weight `ρ⁰ = 1`. -/
theorem sq_expect_le_noiseStability {ρ : ℝ} (hρ : 0 ≤ ρ) (f : BooleanFunction n) :
    𝔼[f] ^ 2 ≤ noiseStability ρ f := by
  rw [expect_eq_fourierCoeff_empty, noiseStability]
  have h := Finset.single_le_sum (f := fun S : Finset (Fin n) => ρ ^ S.card * (𝓕 f S) ^ 2)
    (fun S _ => mul_nonneg (pow_nonneg hρ _) (sq_nonneg _)) (Finset.mem_univ (∅ : Finset (Fin n)))
  simpa using h

/-- **Noise stability grouped by degree**: `Stabᵨ[f] = ∑_k ρ^k · 𝐖(f, k)`. Grouping
    the spectral sum by `|S| = k` factors out the common damping `ρ^k` on each
    degree, exhibiting `Stabᵨ` as the `ρ`-weighted generating function of the
    Fourier weight distribution. -/
theorem noiseStability_eq_sum_weight (ρ : ℝ) (f : BooleanFunction n) :
    noiseStability ρ f = ∑ k ∈ Finset.range (n + 1), ρ ^ k * 𝐖 f k := by
  have hle : ∀ S : Finset (Fin n), S.card ≤ n := fun S => by simpa using Finset.card_le_univ S
  rw [noiseStability, ← Finset.sum_fiberwise_of_maps_to
      (g := fun S => S.card) (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hle S)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourierWeightAtDegree, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_filter] at hS
  rw [fourierWeight, hS.2]

/-- The **noise operator** `T_ρ` (a.k.a. the Bonami–Beckner operator), defined
    spectrally: `T_ρ f = ∑_S ρ^{|S|} · 𝓕(f, S) · χ_S`. It damps each frequency by
    `ρ^{|S|}`, and is the operator behind noise stability. -/
noncomputable def noiseOp (ρ : ℝ) (f : BooleanFunction n) : BooleanFunction n :=
  ∑ S : Finset (Fin n), (ρ ^ S.card * 𝓕 f S) • (χ S)

/-- **Fourier formula for the noise operator**: `𝓕(T_ρ f, T) = ρ^{|T|} · 𝓕(f, T)`. -/
theorem fourierCoeff_noiseOp (ρ : ℝ) (f : BooleanFunction n) (T : Finset (Fin n)) :
    𝓕 (noiseOp ρ f) T = ρ ^ T.card * 𝓕 f T := by
  rw [noiseOp, fourierCoeff_eq_inner, sum_inner]
  simp only [real_inner_smul_left, ← fourierCoeff_eq_inner, fourierCoeff_parityFun]
  rw [Finset.sum_eq_single T]
  · rw [ite_eq_left rfl, mul_one]
  · intro S _ hST; rw [ite_eq_right hST, mul_zero]
  · intro h; exact absurd (Finset.mem_univ T) h

/-- **Noise stability is the correlation of `f` with its noised copy**:
    `Stabᵨ[f] = ⟪f, T_ρ f⟫` (Plancherel). This is the operator form of the spectral
    definition. -/
theorem noiseStability_eq_inner (ρ : ℝ) (f : BooleanFunction n) :
    noiseStability ρ f = ⟪f, noiseOp ρ f⟫ := by
  rw [plancherel]
  simp only [fourierCoeff_noiseOp, noiseStability]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- At `ρ = 1` the noise operator is the identity: `T_1 f = f` (no frequency is
    damped). -/
theorem noiseOp_one (f : BooleanFunction n) : noiseOp 1 f = f :=
  fourierCoeff_ext fun S => by rw [fourierCoeff_noiseOp, one_pow, one_mul]

/-- At `ρ = 0` the noise operator collapses `f` to its mean: `T_0 f = 𝔼[f] · 1`
    (only the empty frequency, with `0⁰ = 1`, survives). This is the constant function
    `𝔼[f]`, written as `𝔼[f] • χ_∅`. Complements `noiseOp_one`. -/
theorem noiseOp_zero (f : BooleanFunction n) :
    noiseOp 0 f = 𝔼[f] • (χ (∅ : Finset (Fin n))) :=
  fourierCoeff_ext fun S => by
    rw [fourierCoeff_noiseOp, fourierCoeff_smul, fourierCoeff_parityFun]
    by_cases hS : S = ∅
    · subst hS; rw [ite_eq_left rfl, expect_eq_fourierCoeff_empty]; simp
    · rw [ite_eq_right (Ne.symm hS)]
      have hc : S.card ≠ 0 := by simp [Finset.card_eq_zero, hS]
      rw [zero_pow hc]; ring

/-- Noise stability is monotone in the correlation `ρ` on `ρ ≥ 0`: more
    correlation can only increase agreement. -/
theorem noiseStability_mono {ρ₁ ρ₂ : ℝ} (h0 : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂)
    (f : BooleanFunction n) : noiseStability ρ₁ f ≤ noiseStability ρ₂ f :=
  Finset.sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h12 _) (sq_nonneg _)

/-- The **bilinear noise stability** of `f` and `g` at correlation `ρ`:
    `Stabᵨ[f, g] = ∑_S ρ^{|S|} · 𝓕(f,S) · 𝓕(g,S)`. It specializes to `noiseStability`
    on the diagonal and to the inner product at `ρ = 1`. -/
noncomputable def noiseStabilityBilin (ρ : ℝ) (f g : BooleanFunction n) : ℝ :=
  ∑ S : Finset (Fin n), ρ ^ S.card * (𝓕 f S * 𝓕 g S)

/-- On the diagonal, bilinear noise stability is ordinary noise stability. -/
theorem noiseStabilityBilin_self (ρ : ℝ) (f : BooleanFunction n) :
    noiseStabilityBilin ρ f f = noiseStability ρ f := by
  simp only [noiseStabilityBilin, noiseStability]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

/-- Bilinear noise stability is symmetric in its two arguments. -/
theorem noiseStabilityBilin_symm (ρ : ℝ) (f g : BooleanFunction n) :
    noiseStabilityBilin ρ f g = noiseStabilityBilin ρ g f := by
  simp only [noiseStabilityBilin]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

/-- At `ρ = 1`, bilinear noise stability is the inner product (Plancherel). -/
theorem noiseStabilityBilin_one (f g : BooleanFunction n) :
    noiseStabilityBilin 1 f g = ⟪f, g⟫ := by
  simp only [noiseStabilityBilin, one_pow, one_mul]
  rw [plancherel]

/-- **Bilinear noise stability is the correlation across the noise operator**:
    `Stabᵨ[f, g] = ⟪f, T_ρ g⟫`. Since `Stabᵨ` is symmetric, this also exhibits `T_ρ`
    as self-adjoint: `⟪f, T_ρ g⟫ = ⟪T_ρ f, g⟫`. -/
theorem noiseStabilityBilin_eq_inner (ρ : ℝ) (f g : BooleanFunction n) :
    noiseStabilityBilin ρ f g = ⟪f, noiseOp ρ g⟫ := by
  rw [plancherel]
  simp only [fourierCoeff_noiseOp, noiseStabilityBilin]
  exact Finset.sum_congr rfl fun S _ => by ring

/-! ### Hypercontractivity foundations

The `(2, 4)`-hypercontractive inequality `‖T_{1/√3} f‖₄ ≤ ‖f‖₂` is the analytic
engine behind the KKL theorem, Friedgut's junta theorem, and the Linial–Mansour–Nisan
`AC⁰` bound (roadmap L7). Its proof is an induction over coordinates whose base case
is the elementary single-bit inequality below; the tensorization step remains. -/

/-- **The two-point `(2, 4)`-hypercontractive inequality** (Bonami's base case). For a
    single-bit function `f(x) = a + b·x` on `x ∈ {−1, +1}`, the noised function
    `T_{1/√3} f = a + (b/√3)·x` satisfies `𝔼[(T_{1/√3} f)⁴] ≤ (𝔼[f²])² = (a² + b²)²`.
    The left side is `((a + b/√3)⁴ + (a − b/√3)⁴)/2`; the slack is `8b⁴/9 ≥ 0`. -/
theorem two_point_hypercontractive (a b : ℝ) :
    ((a + b / Real.sqrt 3) ^ 4 + (a - b / Real.sqrt 3) ^ 4) / 2 ≤ (a ^ 2 + b ^ 2) ^ 2 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set c := b / Real.sqrt 3 with hc
  have hc2 : c ^ 2 = b ^ 2 / 3 := by rw [hc, div_pow, h3]
  have hc4 : c ^ 4 = b ^ 4 / 9 := by
    have h : c ^ 4 = (c ^ 2) ^ 2 := by ring
    rw [h, hc2]; ring
  have expand : ((a + c) ^ 4 + (a - c) ^ 4) / 2 = a ^ 4 + 6 * a ^ 2 * c ^ 2 + c ^ 4 := by ring
  rw [expand]
  nlinarith [hc2, hc4, sq_nonneg (b ^ 2)]

/-! ### §2.3 Total influence (average sensitivity, spectral form)

The **total influence** `I[f]` (a.k.a. average sensitivity) measures how sensitive
`f` is to single-coordinate flips. Its spectral formula (O'Donnell, Theorem 2.38)
weights each Fourier level by its degree: `I[f] = ∑_S |S| · 𝓕(f,S)²`. Grouped by
degree it is `∑_k k · 𝐖(f,k)`, and it is bounded by `n · ⟪f, f⟫` (so by `n` for
Boolean `f`) — the fact that a function on `n` bits has average sensitivity at most
`n`. -/

/-- The **total influence** of `f`, spectral form: `I[f] = ∑_S |S| · 𝓕(f, S)²`. -/
noncomputable def totalInfluence (f : BooleanFunction n) : ℝ :=
  ∑ S : Finset (Fin n), (S.card : ℝ) * (𝓕 f S) ^ 2

/-- Total influence is nonnegative. -/
theorem totalInfluence_nonneg (f : BooleanFunction n) : 0 ≤ totalInfluence f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (sq_nonneg _)

/-- **Total influence grouped by degree**: `I[f] = ∑_k k · 𝐖(f, k)`. -/
theorem totalInfluence_eq_sum_weight (f : BooleanFunction n) :
    totalInfluence f = ∑ k ∈ Finset.range (n + 1), (k : ℝ) * 𝐖 f k := by
  have hle : ∀ S : Finset (Fin n), S.card ≤ n := fun S => by simpa using Finset.card_le_univ S
  rw [totalInfluence, ← Finset.sum_fiberwise_of_maps_to
      (g := fun S => S.card) (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hle S)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourierWeightAtDegree, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_filter] at hS
  rw [fourierWeight, hS.2]

/-- Total influence is bounded by `n · ⟪f, f⟫` (each degree is at most `n`). -/
theorem totalInfluence_le (f : BooleanFunction n) : totalInfluence f ≤ (n : ℝ) * ⟪f, f⟫ := by
  rw [parseval, Finset.mul_sum, totalInfluence]
  refine Finset.sum_le_sum fun S _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  exact_mod_cast hS

/-- For a Boolean-valued function, total influence is at most `n` (its total power
    is `1`). -/
theorem totalInfluence_boolean_le (f : BooleanFunction n) (hf : IsBooleanValued f) :
    totalInfluence f ≤ (n : ℝ) := by
  have h := totalInfluence_le f
  rw [parseval, parseval_boolean f hf] at h
  simpa using h

/-- **Low-degree functions have small total influence.** If `f` has degree at most
    `d` (all Fourier coefficients on sets larger than `d` vanish), then
    `I[f] ≤ d · ⟪f, f⟫`. -/
theorem totalInfluence_le_of_degree (f : BooleanFunction n) (d : ℕ)
    (hd : ∀ S : Finset (Fin n), d < S.card → 𝓕 f S = 0) :
    totalInfluence f ≤ (d : ℝ) * ⟪f, f⟫ := by
  rw [parseval, Finset.mul_sum, totalInfluence]
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases h : S.card ≤ d
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)
  · rw [not_le] at h
    rw [hd S h]; simp

/-- For a Boolean-valued function of degree at most `d`, total influence is at most
    `d`. -/
theorem totalInfluence_boolean_le_of_degree (f : BooleanFunction n) (hf : IsBooleanValued f)
    (d : ℕ) (hd : ∀ S : Finset (Fin n), d < S.card → 𝓕 f S = 0) :
    totalInfluence f ≤ (d : ℝ) := by
  have h := totalInfluence_le_of_degree f d hd
  rw [parseval, parseval_boolean f hf] at h
  simpa using h

/-- The **influence of coordinate `i`** on `f`, spectral form: the Fourier weight
    carried by sets containing `i`, `Infᵢ[f] = ∑_{S ∋ i} 𝓕(f, S)²`. -/
noncomputable def influence (i : Fin n) (f : BooleanFunction n) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), (𝓕 f S) ^ 2

/-- Coordinate influence is nonnegative. -/
theorem influence_nonneg (i : Fin n) (f : BooleanFunction n) : 0 ≤ influence i f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Total influence is the sum of the coordinate influences**:
    `I[f] = ∑_i Infᵢ[f]`. Each set `S` contributes its weight `𝓕(f,S)²` once for
    every coordinate it contains, i.e. `|S|` times — swapping the order of
    summation turns the degree weighting into a sum over coordinates. -/
theorem totalInfluence_eq_sum_influence (f : BooleanFunction n) :
    totalInfluence f = ∑ i : Fin n, influence i f := by
  simp only [totalInfluence, influence, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- Each coordinate influence is at most the total influence. -/
theorem influence_le_totalInfluence (i : Fin n) (f : BooleanFunction n) :
    influence i f ≤ totalInfluence f := by
  rw [totalInfluence_eq_sum_influence]
  exact Finset.single_le_sum (fun j _ => influence_nonneg j f) (Finset.mem_univ i)

/-- A coordinate's influence is at most the total power `⟪f, f⟫`. -/
theorem influence_le_self_inner (i : Fin n) (f : BooleanFunction n) :
    influence i f ≤ ⟪f, f⟫ := by
  rw [parseval, influence]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun S _ _ => sq_nonneg _)

/-- For a Boolean-valued function, every coordinate influence is at most `1`. -/
theorem influence_boolean_le_one (i : Fin n) (f : BooleanFunction n) (hf : IsBooleanValued f) :
    influence i f ≤ 1 := by
  have h := influence_le_self_inner i f
  rwa [parseval, parseval_boolean f hf] at h

/-- **Average sensitivity of a parity.** The parity `χ_S` has total influence
    exactly `|S|`: each of its `|S|` relevant coordinates is fully influential
    (a concrete check of the average-sensitivity theory on the Fourier basis). -/
theorem totalInfluence_parityFun (S : Finset (Fin n)) :
    totalInfluence (χ S) = (S.card : ℝ) := by
  simp only [totalInfluence, fourierCoeff_parityFun]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hT; rw [ite_eq_right (Ne.symm hT)]; simp
  · intro h; exact absurd (Finset.mem_univ S) h

/-- **Coordinate influence of a parity.** Coordinate `i` influences `χ_S` fully
    when `i ∈ S`, and not at all otherwise. -/
theorem influence_parityFun (i : Fin n) (S : Finset (Fin n)) :
    influence i (χ S) = if i ∈ S then 1 else 0 := by
  have hsq : ∀ T : Finset (Fin n),
      ((if S = T then (1 : ℝ) else 0)) ^ 2 = if S = T then 1 else 0 := by
    intro T; by_cases h : S = T <;> simp [h]
  simp only [influence, fourierCoeff_parityFun, hsq]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_filter]

/-- The squared degree-1 coefficient at `i` is a lower bound for the influence of `i`:
    `𝓕(f, {i})² ≤ Infᵢ[f]`. It is the `S = {i}` term of the spectral sum defining the
    influence, and all other terms are nonnegative. -/
theorem fourierCoeff_singleton_sq_le_influence (i : Fin n) (f : BooleanFunction n) :
    (𝓕 f {i}) ^ 2 ≤ influence i f := by
  rw [influence]
  apply Finset.single_le_sum (f := fun S => (𝓕 f S) ^ 2) (fun S _ => sq_nonneg _)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self i⟩

/-- **Degree-1 weight is bounded by total influence**: `W¹[f] ≤ I[f]`. Each degree-1
    frequency contributes its weight once to `W¹` but `|S| = 1` times (i.e. also once)
    to `I`, and higher-degree frequencies only add to `I`. -/
theorem fourierWeightAtDegree_one_le_totalInfluence (f : BooleanFunction n) :
    𝐖 f 1 ≤ totalInfluence f := by
  rw [fourierWeightAtDegree, totalInfluence]
  have hcongr : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = 1),
      fourierWeight f S = (S.card : ℝ) * (𝓕 f S) ^ 2 := by
    intro S hS; rw [Finset.mem_filter] at hS
    rw [fourierWeight, hS.2]; simp
  rw [Finset.sum_congr rfl hcongr]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun S _ _ => mul_nonneg (by positivity) (sq_nonneg _))

/-- **Level-1 inequality (coordinate form).** The total weight on the degree-1
    coefficients is at most the total influence: `∑_i 𝓕(f, {i})² ≤ I[f]`. Immediate by
    summing `fourierCoeff_singleton_sq_le_influence` over the coordinates. -/
theorem sum_fourierCoeff_singleton_sq_le_totalInfluence (f : BooleanFunction n) :
    ∑ i : Fin n, (𝓕 f {i}) ^ 2 ≤ totalInfluence f := by
  rw [totalInfluence_eq_sum_influence]
  exact Finset.sum_le_sum fun i _ => fourierCoeff_singleton_sq_le_influence i f

/-- The coordinate sum of squared degree-1 coefficients **is** the degree-1 weight:
    `∑_i 𝓕(f, {i})² = W¹[f]`. The singletons `{i}` are exactly the cardinality-1
    frequencies, so the coordinate sum and the degree-1 weight coincide. -/
theorem sum_fourierCoeff_singleton_sq_eq_fourierWeightAtDegree_one (f : BooleanFunction n) :
    ∑ i : Fin n, (𝓕 f {i}) ^ 2 = 𝐖 f 1 := by
  rw [fourierWeightAtDegree]
  have himg : (Finset.univ.filter (fun S : Finset (Fin n) => S.card = 1))
      = Finset.univ.image (fun i => ({i} : Finset (Fin n))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [Finset.card_eq_one]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  rw [himg, Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  exact Finset.sum_congr rfl fun i _ => by rw [fourierWeight]

/-- Flip coordinate `i` of a point of the Hamming cube. -/
def flipCoord (i : Fin n) (x : Cube n) : Cube n := Function.update x i (x i + 1)

/-- The character `χ` negates under a bit flip: `χ(b + 1) = -χ(b)`. -/
theorem chi_add_one (b : ZMod 2) : chi (b + 1) = - chi b := by
  fin_cases b
  · show chi 1 = - chi 0; simp [chi]
  · show chi 0 = - chi 1; simp [chi]

/-- **A parity under a coordinate flip.** `χ_S` flips sign exactly when the flipped
    coordinate is one of its inputs: `χ_S(x with coordinate i flipped) = (−1)^{[i∈S]}
    · χ_S(x)`. This is the key step toward reading coordinate influence as the
    probability that `f` is sensitive at `i`. -/
theorem parityFun_flipCoord (i : Fin n) (S : Finset (Fin n)) (x : Cube n) :
    (χ S) (flipCoord i x) = (if i ∈ S then -1 else 1) * (χ S) x := by
  simp only [parityFun, flipCoord]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, ← Finset.prod_erase_mul S _ hi, ← Finset.prod_erase_mul S _ hi,
      Function.update_self]
    have hrest : ∀ j ∈ S.erase i, chi (Function.update x i (x i + 1) j) = chi (x j) := by
      intro j hj; rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [Finset.prod_congr rfl hrest, chi_add_one]; ring
  · rw [ite_eq_right hi, one_mul]
    apply Finset.prod_congr rfl
    intro j hj; rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

/-- Flipping coordinate `i` twice is the identity (`ZMod 2` has characteristic two). -/
theorem flipCoord_flipCoord (i : Fin n) (x : Cube n) : flipCoord i (flipCoord i x) = x := by
  simp only [flipCoord, Function.update_self, Function.update_idem]
  rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero, Function.update_eq_self]

/-- Flipping coordinate `i` is an involutive equivalence of the Hamming cube. -/
def flipEquiv (i : Fin n) : Cube n ≃ Cube n :=
  ⟨flipCoord i, flipCoord i, flipCoord_flipCoord i, flipCoord_flipCoord i⟩

/-- The uniform expectation is invariant under a coordinate flip: `flipCoord i` is a
    measure-preserving bijection of the cube. -/
theorem expect_flipCoord (i : Fin n) (g : Cube n → ℝ) :
    (𝔼[fun x => g (flipCoord i x)]) = 𝔼[g] := by
  simp only [expect]
  exact Finset.expect_equiv (flipEquiv i) (by simp) (fun x _ => rfl)

/-- **Fourier coefficient of `f` precomposed with a coordinate flip.** Flipping
    coordinate `i` negates exactly the frequencies containing `i`:
    `𝓕(f ∘ flipᵢ, T) = (−1)^[i∈T] · 𝓕(f, T)`. -/
theorem fourierCoeff_comp_flipCoord (i : Fin n) (f : BooleanFunction n) (T : Finset (Fin n)) :
    𝓕 (fun x => f (flipCoord i x)) T = (if i ∈ T then -1 else 1) * 𝓕 f T := by
  rw [fourierCoeff_eq_inner (f := fun x : Cube n => f (flipCoord i x)) (S := T),
    inner_eq_expect (f := fun x : Cube n => f (flipCoord i x)) (g := χ T),
    ← expect_flipCoord i (fun x => f (flipCoord i x) * (χ T) x)]
  simp only [flipCoord_flipCoord, parityFun_flipCoord]
  rw [fourierCoeff_eq_inner, inner_eq_expect]
  simp only [expect]
  rw [Finset.mul_expect]
  exact Finset.expect_congr rfl (fun x _ => by ring)

/-- The **discrete derivative** `D_i f` of `f` in the direction of coordinate `i`,
    defined spectrally: `D_i f = ∑_{S ∋ i} 𝓕(f, S) · χ_{S∖{i}}`. It strips
    coordinate `i` from every frequency that contains it. -/
noncomputable def derivative (i : Fin n) (f : BooleanFunction n) : BooleanFunction n :=
  ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), (𝓕 f S) • (χ (S.erase i))

/-- **Fourier formula for the derivative**: `𝓕(D_i f, T) = 𝓕(f, T ∪ {i})` when
    `i ∉ T`, and `0` when `i ∈ T`. -/
theorem fourierCoeff_derivative (i : Fin n) (f : BooleanFunction n) (T : Finset (Fin n)) :
    𝓕 (derivative i f) T = if i ∈ T then 0 else 𝓕 f (insert i T) := by
  rw [derivative, fourierCoeff_eq_inner, sum_inner]
  simp only [real_inner_smul_left, ← fourierCoeff_eq_inner, fourierCoeff_parityFun]
  by_cases hiT : i ∈ T
  · rw [ite_eq_left hiT]
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    have hne : S.erase i ≠ T := fun h => (Finset.mem_erase.mp (h ▸ hiT)).1 rfl
    rw [ite_eq_right hne, mul_zero]
  · rw [ite_eq_right hiT, Finset.sum_eq_single (insert i T)]
    · rw [Finset.erase_insert hiT, ite_eq_left rfl, mul_one]
    · intro S hS hSne
      rw [Finset.mem_filter] at hS
      have hne : S.erase i ≠ T := fun h => hSne (by rw [← h, Finset.insert_erase hS.2])
      rw [ite_eq_right hne, mul_zero]
    · intro h
      exact absurd (Finset.mem_filter.mpr
        ⟨Finset.mem_univ (insert i T), Finset.mem_insert_self i T⟩) h

/-- **Influence is the squared norm of the derivative**: `Infᵢ[f] = ‖D_i f‖²`. This
    is the analytic form of coordinate influence — the standard bridge to the
    combinatorial "probability `f` is sensitive at `i`" (O'Donnell §2.2). -/
theorem influence_eq_norm_sq_derivative (i : Fin n) (f : BooleanFunction n) :
    influence i f = ‖derivative i f‖₂ ^ 2 := by
  rw [norm_sq_eq_sum_fourierCoeff_sq, influence,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun T => i ∈ T)]
  have h1 : ∑ T ∈ Finset.univ.filter (fun T => i ∈ T), (𝓕 (derivative i f) T) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    rw [Finset.mem_filter] at hT
    rw [fourierCoeff_derivative, ite_eq_left hT.2]; simp
  rw [h1, zero_add]
  apply Finset.sum_nbij' (fun S => S.erase i) (fun T => insert i T)
  · intro S hS; rw [Finset.mem_filter] at hS ⊢; exact ⟨Finset.mem_univ _, by simp⟩
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢; exact ⟨Finset.mem_univ _, Finset.mem_insert_self i T⟩
  · intro S hS; rw [Finset.mem_filter] at hS; rw [Finset.insert_erase hS.2]
  · intro T hT; rw [Finset.mem_filter] at hT; rw [Finset.erase_insert hT.2]
  · intro S hS
    rw [Finset.mem_filter] at hS
    rw [fourierCoeff_derivative, ite_eq_right (by simp : i ∉ S.erase i), Finset.insert_erase hS.2]

/-- The **sensitivity operator** `Lᵢ f` at coordinate `i`, the point-value analogue of
    the derivative: `(Lᵢ f)(x) = (f(x) − f(x ⊕ eᵢ)) / 2`. It vanishes exactly where `f`
    is insensitive to coordinate `i`, and equals `±1` where flipping `i` flips `f`. -/
noncomputable def sensitivityOp (i : Fin n) (f : BooleanFunction n) : BooleanFunction n :=
  fun x => (f x - f (flipCoord i x)) / 2

/-- **Fourier formula for the sensitivity operator**: `Lᵢ` keeps the frequencies
    containing `i` and kills the rest — `𝓕(Lᵢ f, T) = 𝓕(f, T)` if `i ∈ T`, else `0`.
    (Contrast the derivative `Dᵢ`, which additionally strips `i` from each frequency.) -/
theorem fourierCoeff_sensitivityOp (i : Fin n) (f : BooleanFunction n) (T : Finset (Fin n)) :
    𝓕 (sensitivityOp i f) T = if i ∈ T then 𝓕 f T else 0 := by
  have key : 𝓕 (sensitivityOp i f) T
      = (1 / 2) * 𝓕 f T - (1 / 2) * 𝓕 (fun x => f (flipCoord i x)) T := by
    rw [fourierCoeff_eq_inner (f := sensitivityOp i f) (S := T),
      inner_eq_expect (f := sensitivityOp i f) (g := χ T),
      fourierCoeff_eq_inner (f := f) (S := T), inner_eq_expect (f := f) (g := χ T),
      fourierCoeff_eq_inner (f := fun x : Cube n => f (flipCoord i x)) (S := T),
      inner_eq_expect (f := fun x : Cube n => f (flipCoord i x)) (g := χ T)]
    simp only [expect, sensitivityOp]
    rw [Finset.mul_expect, Finset.mul_expect, ← Finset.expect_sub_distrib]
    exact Finset.expect_congr rfl (fun x _ => by ring)
  rw [key, fourierCoeff_comp_flipCoord]
  by_cases h : i ∈ T
  · rw [ite_eq_left h, ite_eq_left h]; ring
  · rw [ite_eq_right h, ite_eq_right h]; ring

/-- **Influence is the squared norm of the sensitivity operator**: `Infᵢ[f] = ‖Lᵢ f‖²`.
    A second analytic form of coordinate influence, complementing
    `influence_eq_norm_sq_derivative`. -/
theorem influence_eq_norm_sq_sensitivityOp (i : Fin n) (f : BooleanFunction n) :
    influence i f = ‖sensitivityOp i f‖₂ ^ 2 := by
  rw [norm_sq_eq_sum_fourierCoeff_sq, influence, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_sensitivityOp]
  by_cases h : i ∈ S
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]; ring

/-- **The sensitivity operator is the parity-twisted derivative**: `Lᵢ f = χ_{i} · Dᵢ f`.
    Both strip coordinate `i` from the surviving frequencies, but `Lᵢ` twists each back
    by `χ_{i}`; since `|χ_{i}| = 1` this is why `‖Lᵢ f‖ = ‖Dᵢ f‖` and the two influence
    formulas agree. -/
theorem sensitivityOp_eq_parityFun_mul_derivative (i : Fin n) (f : BooleanFunction n) :
    sensitivityOp i f = fun x => (χ ({i} : Finset (Fin n))) x * (derivative i f) x := by
  have hins : ∀ T : Finset (Fin n), i ∈ T →
      insert i (symmDiff ({i} : Finset (Fin n)) T) = T := by
    intro T h; ext a
    simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨rfl, _⟩ | ⟨ha, _⟩)
      · exact h
      · exact h
      · exact ha
    · intro ha; by_cases hai : a = i
      · exact Or.inl hai
      · exact Or.inr (Or.inr ⟨ha, hai⟩)
  apply fourierCoeff_ext
  intro T
  rw [fourierCoeff_sensitivityOp, fourierCoeff_parityFun_mul, fourierCoeff_derivative]
  by_cases hiT : i ∈ T
  · rw [ite_eq_left hiT]
    have h1 : i ∉ symmDiff ({i} : Finset (Fin n)) T := by simp [Finset.mem_symmDiff, hiT]
    rw [ite_eq_right h1, hins T hiT]
  · rw [ite_eq_right hiT]
    have h2 : i ∈ symmDiff ({i} : Finset (Fin n)) T := by simp [Finset.mem_symmDiff, hiT]
    rw [ite_eq_left h2]

/-- **Average sensitivity as a probability.** For a Boolean-valued `f`, the influence of
    coordinate `i` is the probability that flipping `i` flips the output:
    `Infᵢ[f] = Pr_x[f(x) ≠ f(x ⊕ eᵢ)]` (O'Donnell §2.2). Summed over `i`, this reads
    total influence as the expected number of pivotal coordinates — the combinatorial
    meaning of "average sensitivity". -/
theorem influence_boolean_eq_expect_sensitive (i : Fin n) (f : BooleanFunction n)
    (hf : IsBooleanValued f) :
    influence i f = 𝔼[fun x => if f x ≠ f (flipCoord i x) then 1 else 0] := by
  rw [influence_eq_norm_sq_sensitivityOp, norm_sq_eq_inner, inner_eq_expect]
  refine Finset.expect_congr rfl fun x _ => ?_
  simp only [sensitivityOp]
  rcases hf x with hx | hx <;> rcases hf (flipCoord i x) with hy | hy <;>
    simp only [hx, hy] <;> norm_num

/-- **Total influence is the expected number of pivotal coordinates.** For a
    Boolean-valued `f`, summing the per-coordinate sensitivity probabilities over all
    coordinates gives `I[f] = 𝔼ₓ[#{i : f(x) ≠ f(x ⊕ eᵢ)}]` — the literal meaning of
    "average sensitivity" (average, over a uniform input, of the number of coordinates
    whose flip changes the output). -/
theorem totalInfluence_boolean_eq_expect_sensitive (f : BooleanFunction n)
    (hf : IsBooleanValued f) :
    totalInfluence f
      = 𝔼[fun x => ∑ i : Fin n, if f x ≠ f (flipCoord i x) then (1 : ℝ) else 0] := by
  rw [totalInfluence_eq_sum_influence]
  simp_rw [influence_boolean_eq_expect_sensitive _ f hf]
  simp only [expect]
  exact (Finset.expect_sum_comm _ _ _).symm

/-- Elementary inequality `1 - ρ^k ≤ (1 - ρ) · k` for `ρ ∈ [0, 1]` (a telescoping /
    Bernoulli bound), used to control noise-stability decay by total influence. -/
private theorem one_sub_pow_le_mul {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (k : ℕ) :
    1 - ρ ^ k ≤ (1 - ρ) * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpk : ρ ^ k ≤ 1 := pow_le_one₀ h0 h1
    have hrw : (1 : ℝ) - ρ ^ (k + 1) = (1 - ρ ^ k) + ρ ^ k * (1 - ρ) := by ring
    rw [hrw, Nat.cast_succ, mul_add, mul_one]
    have h2 : ρ ^ k * (1 - ρ) ≤ 1 * (1 - ρ) := mul_le_mul_of_nonneg_right hpk (by linarith)
    linarith [ih, h2]

/-- **Stability decay is controlled by total influence.** For `ρ ∈ [0, 1]`, the
    loss of noise stability relative to the full power `⟪f, f⟫` is at most
    `(1 - ρ)` times the total influence: `⟪f, f⟫ - Stabᵨ[f] ≤ (1 - ρ) · I[f]`. This
    is the spectral form of the standard bound `NS_δ[f] ≤ δ · I[f]` on noise
    sensitivity. -/
theorem noiseStability_one_sub_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (f : BooleanFunction n) :
    ⟪f, f⟫ - noiseStability ρ f ≤ (1 - ρ) * totalInfluence f := by
  rw [parseval, noiseStability, totalInfluence, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  have key : (1 - ρ ^ S.card) * (𝓕 f S) ^ 2 ≤ ((1 - ρ) * S.card) * (𝓕 f S) ^ 2 :=
    mul_le_mul_of_nonneg_right (one_sub_pow_le_mul h0 h1 S.card) (sq_nonneg _)
  nlinarith [key]

/-- **The Poincaré inequality**: the variance of `f` is at most its total
    influence, `Var[f] ≤ I[f]`. Spectrally, `Var[f] = ∑_{S ≠ ∅} 𝓕(f,S)²` while
    `I[f] = ∑_S |S| 𝓕(f,S)²`, and each nonempty `S` has `|S| ≥ 1`, so influence
    dominates variance term by term. -/
theorem variance_le_totalInfluence (f : BooleanFunction n) : Var[f] ≤ totalInfluence f := by
  rw [variance_eq_sum_fourierCoeff_sq, totalInfluence]
  calc ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅), (𝓕 f S) ^ 2
      ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S ≠ ∅),
          (S.card : ℝ) * (𝓕 f S) ^ 2 := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [Finset.mem_filter] at hS
        have h1 : 1 ≤ S.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS.2)
        nlinarith [sq_nonneg (𝓕 f S), (by exact_mod_cast h1 : (1 : ℝ) ≤ S.card)]
    _ ≤ ∑ S : Finset (Fin n), (S.card : ℝ) * (𝓕 f S) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S _ _ => ?_
        exact mul_nonneg (by positivity) (sq_nonneg _)

/-- The **noise sensitivity** of `f` at correlation `ρ`, defined from noise
    stability as `NSᵨ[f] = (⟪f, f⟫ - Stabᵨ[f]) / 2` — the amount of Fourier power
    lost to the `ρ`-damping, i.e. the propensity of `f` to disagree with itself
    under noise. -/
noncomputable def noiseSensitivity (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  (⟪f, f⟫ - noiseStability ρ f) / 2

/-- Noise sensitivity is nonnegative for `ρ ∈ [0, 1]`. -/
theorem noiseSensitivity_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : BooleanFunction n) :
    0 ≤ noiseSensitivity ρ f := by
  rw [noiseSensitivity]
  have := noiseStability_le_self_inner hρ0 hρ1 f
  linarith

/-- At full correlation `ρ = 1`, noise sensitivity vanishes. -/
theorem noiseSensitivity_one (f : BooleanFunction n) : noiseSensitivity 1 f = 0 := by
  rw [noiseSensitivity, noiseStability_one]; ring

/-- **Noise sensitivity is controlled by total influence**: `NSᵨ[f] ≤ (1-ρ)/2 · I[f]`
    (the spectral form of `NS_δ[f] ≤ δ · I[f]`). -/
theorem noiseSensitivity_le_influence {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (f : BooleanFunction n) : noiseSensitivity ρ f ≤ (1 - ρ) / 2 * totalInfluence f := by
  rw [noiseSensitivity,
    show (1 - ρ) / 2 * totalInfluence f = ((1 - ρ) * totalInfluence f) / 2 from by ring]
  have := noiseStability_one_sub_le hρ0 hρ1 f
  linarith

/-- **Stability–sensitivity decomposition**: `Stabᵨ[f] + 2·NSᵨ[f] = ⟪f, f⟫`. The
    total Fourier power splits into the retained (stability) and lost (twice
    sensitivity) parts. -/
theorem noiseStability_add_two_noiseSensitivity (ρ : ℝ) (f : BooleanFunction n) :
    noiseStability ρ f + 2 * noiseSensitivity ρ f = ⟪f, f⟫ := by
  rw [noiseSensitivity]; ring

/-- Noise sensitivity is antitone in the correlation `ρ` (more correlation, less
    disagreement) — dual to the monotonicity of noise stability. -/
theorem noiseSensitivity_antitone {ρ₁ ρ₂ : ℝ} (h0 : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂)
    (f : BooleanFunction n) : noiseSensitivity ρ₂ f ≤ noiseSensitivity ρ₁ f := by
  simp only [noiseSensitivity]
  have := noiseStability_mono h0 h12 f
  linarith

end BooleanAnalysis

end Complexity

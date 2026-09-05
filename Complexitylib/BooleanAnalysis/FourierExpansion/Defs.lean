/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# Chapter 1: Boolean functions and the Fourier expansion — Definitions

This file contains the core definitions for Fourier analysis of Boolean functions
following Chapter 1 of "Analysis of Boolean Functions" by Ryan O'Donnell.

We work with the Hamming cube modeled as `Fin n → ZMod 2`, with the encoding
`χ : ZMod 2 → ℝ` sending `0 ↦ 1` and `1 ↦ -1`. This corresponds to the book's
convention of representing the cube as `{-1, 1}^n` via the map `b ↦ (-1)^b`.

The space `BooleanFunction n` of real-valued functions on the Boolean cube carries
the uniform-measure L² inner product `⟪f, g⟫ = 𝔼[f·g] = (1/2ⁿ) · ∑_x f(x)·g(x)`
(Definition 1.3), realized as a Mathlib `InnerProductSpace ℝ`. The `def` (rather
than `abbrev`) for `BooleanFunction` blocks typeclass resolution from seeing through
to `Cube n → ℝ`, avoiding a norm diamond with Mathlib's Pi-type sup norm.

## Notation

Within the `BooleanAnalysis` namespace, we provide notation that mirrors
the book's conventions:

* `𝔼[f]` — uniform expectation over the Hamming cube
* `⟪f, g⟫` — inner product `𝔼[f·g]` (Mathlib's `inner` on `BooleanFunction n`)
* `‖f‖₂` — L² norm `√⟪f, f⟫` (Mathlib's `norm` on `BooleanFunction n`)
* `χ S` — parity function on set `S`
* `𝓕 f S` — Fourier coefficient of `f` on `S`
* `𝐖 f k` — Fourier weight of `f` at degree `k`
* `Var[f]` — variance of `f`
* `Cov[f, g]` — covariance of `f` and `g`
* `f ⊛ g` — convolution
* `𝟙 P` — indicator function of predicate `P`
* `Pr[P]` — uniform probability `𝔼[𝟙 P]`
* `Pr₂[P]` — joint uniform probability over pairs
-/


@[expose] public section

namespace Complexity

namespace BooleanAnalysis

open Finset BigOperators Classical

variable {n : ℕ}

/-! ### Basic types -/

/-- The Hamming cube `𝔽₂ⁿ` is `Fin n → ZMod 2`. -/
abbrev Cube (n : ℕ) := Fin n → ZMod 2

/-- `BooleanFunction n` is the space of real-valued functions on the Boolean cube `𝔽₂ⁿ`,
    equipped with the uniform-measure L² inner product `⟪f, g⟫ = 𝔼[f·g]`
    (Definition 1.3 in O'Donnell).

    The `def` (rather than `abbrev`) blocks typeclass resolution from seeing through
    to `Cube n → ℝ`, preventing a norm diamond with Mathlib's Pi-type sup norm
    while still allowing the kernel to see through for type checking. -/
def BooleanFunction (n : ℕ) := Cube n → ℝ

namespace BooleanFunction

noncomputable instance : CommRing (BooleanFunction n) := inferInstanceAs (CommRing (Cube n → ℝ))
noncomputable instance : Module ℝ (BooleanFunction n) :=
  inferInstanceAs (Module ℝ (Cube n → ℝ))
noncomputable instance : Algebra ℝ (BooleanFunction n) :=
  inferInstanceAs (Algebra ℝ (Cube n → ℝ))
instance : Inhabited (BooleanFunction n) := inferInstanceAs (Inhabited (Cube n → ℝ))

instance : FunLike (BooleanFunction n) (Cube n) ℝ where
  coe f := f
  coe_injective f g h := show (f : Cube n → ℝ) = g from h

@[ext]
theorem ext {f g : BooleanFunction n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem zero_apply (x : Cube n) : (0 : BooleanFunction n) x = 0 := rfl
@[simp] theorem add_apply (f g : BooleanFunction n) (x : Cube n) : (f + g) x = f x + g x := rfl
@[simp] theorem neg_apply (f : BooleanFunction n) (x : Cube n) : (-f) x = -(f x) := rfl
@[simp] theorem sub_apply (f g : BooleanFunction n) (x : Cube n) : (f - g) x = f x - g x := rfl
@[simp] theorem smul_apply (r : ℝ) (f : BooleanFunction n) (x : Cube n) :
    (r • f) x = r * f x := rfl
@[simp] theorem mul_apply (f g : BooleanFunction n) (x : Cube n) : (f * g) x = f x * g x := rfl
@[simp] theorem one_apply (x : Cube n) : (1 : BooleanFunction n) x = 1 := rfl

/-- Evaluate a `Finset` sum of `BooleanFunction`s pointwise. -/
@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (g : ι → BooleanFunction n)
    (x : Cube n) : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x :=
  Finset.sum_apply x s g

/-- Coerce a plain function `Cube n → ℝ` to `BooleanFunction n`. -/
def ofFun (f : Cube n → ℝ) : BooleanFunction n := f

/-- Extract the underlying function from a `BooleanFunction`. -/
def toFun (f : BooleanFunction n) : Cube n → ℝ := f

@[simp] theorem toFun_ofFun (f : Cube n → ℝ) : toFun (ofFun f) = f := rfl
@[simp] theorem ofFun_toFun (f : BooleanFunction n) : ofFun (toFun f) = f := rfl

/-! ### Inner product space structure

The inner product on `BooleanFunction n` is the uniform-measure inner product
`⟪f, g⟫ = (1/2ⁿ) · ∑_x f(x)·g(x)`, matching O'Donnell's Definition 1.3.
This is the expectation `𝔼[f·g]` under the uniform distribution on `𝔽₂ⁿ`. -/

/-- The uniform-measure inner product: `⟪f, g⟫ = (1/2ⁿ) · ∑_x f(x)·g(x)`. -/
noncomputable instance instInner : Inner ℝ (BooleanFunction n) where
  inner f g := (1 / (2 : ℝ) ^ n) * ∑ x : Cube n, f x * g x

theorem inner_def (f g : BooleanFunction n) :
    @inner ℝ _ instInner f g = (1 / (2 : ℝ) ^ n) * ∑ x : Cube n, f x * g x := rfl

private theorem inner_comm (f g : BooleanFunction n) :
    @inner ℝ _ instInner f g = @inner ℝ _ instInner g f := by
  simp only [inner_def]; congr 1; apply Finset.sum_congr rfl; intro x _; ring

private theorem inner_add_left (f g h : BooleanFunction n) :
    @inner ℝ _ instInner (f + g) h = @inner ℝ _ instInner f h + @inner ℝ _ instInner g h := by
  simp only [inner_def, add_apply, add_mul, Finset.sum_add_distrib, mul_add]

private theorem inner_smul_left (r : ℝ) (f g : BooleanFunction n) :
    @inner ℝ _ instInner (r • f) g = r * @inner ℝ _ instInner f g := by
  simp only [inner_def, smul_apply, Finset.mul_sum]; ring_nf

private theorem inner_self_nonneg' (f : BooleanFunction n) :
    0 ≤ @inner ℝ _ instInner f f := by
  simp only [inner_def]
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg; intro x _; exact mul_self_nonneg (f x)

private theorem inner_self_eq_zero {f : BooleanFunction n}
    (h : @inner ℝ _ instInner f f = 0) : f = 0 := by
  simp only [inner_def] at h
  have h2n : (0 : ℝ) < 1 / 2 ^ n := by positivity
  have hsum : ∑ x : Cube n, f x * f x = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · exact h1
  ext x
  have : f x * f x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg (f x))).mp hsum
      x (Finset.mem_univ x)
  simpa [mul_self_eq_zero] using this

noncomputable instance instCore : PreInnerProductSpace.Core ℝ (BooleanFunction n) where
  toInner := instInner
  conj_inner_symm f g := by simp [inner_comm f g]
  re_inner_nonneg f := by simp [inner_self_nonneg' f]
  add_left := by exact inner_add_left
  smul_left f g r := by rw [inner_smul_left]; simp

-- `instFullCore` adds the definiteness axiom (`‖f‖ = 0 → f = 0`) needed to upgrade
-- from `SeminormedAddCommGroup` to `NormedAddCommGroup`. The `NormedAddCommGroup`
-- instance must be declared before `InnerProductSpace.ofCore` so that `ofCore` uses
-- it (rather than installing its own `SeminormedAddCommGroup`). Both derive the norm
-- from the same inner product, so there is no diamond.
noncomputable instance instFullCore : InnerProductSpace.Core ℝ (BooleanFunction n) where
  toCore := instCore
  definite := by exact @inner_self_eq_zero n

noncomputable instance : NormedAddCommGroup (BooleanFunction n) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ instFullCore

noncomputable instance innerProductSpace : InnerProductSpace ℝ (BooleanFunction n) :=
  InnerProductSpace.ofCore instCore

end BooleanFunction

/-! ### Notation

The book uses `⟪f, g⟫` for the inner product (Definition 1.3) and `‖f‖₂` for the
L² norm (§1.3, page 24). These map to Mathlib's `inner` and `norm` on
`BooleanFunction n`. -/

/-- `⟪f, g⟫` — the inner product `𝔼[f·g]` on `BooleanFunction n` (Definition 1.3). -/
scoped notation "⟪" f ", " g "⟫" => @inner ℝ _ _ f g

/-- `‖f‖₂` — the L² norm `√⟪f, f⟫` on `BooleanFunction n` (§1.3, page 24).

    This equals Mathlib's `‖f‖` since the `InnerProductSpace` instance makes
    `norm` the L² norm. We use the subscript to match the book's convention
    and to distinguish from other norms that may appear in later chapters. -/
scoped notation "‖" f "‖₂" => @norm _ _ f

/-- `⟪f, g⟫ = (1/2ⁿ) · ∑_x f(x)·g(x)` — unfold the inner product to the
    explicit sum form. -/
theorem inner_def (f g : BooleanFunction n) :
    ⟪f, g⟫ = (1 / (2 : ℝ) ^ n) * ∑ x : Cube n, f x * g x :=
  BooleanFunction.inner_def f g

/-! ### §1.2 The encoding and parity functions -/

/-- A function `f : 𝔽₂ⁿ → ℝ` is Boolean-valued if its range is `{-1, 1}`.
    In the ±1 encoding, this means `f(x) = ±1` for all `x`. -/
def IsBooleanValued (f : BooleanFunction n) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

/-- The encoding `χ : ZMod 2 → ℝ` defined by `χ(b) = (-1)^b`.
    Concretely, `χ(0) = 1` and `χ(1) = -1`. (Book §1.2) -/
def chi : ZMod 2 → ℝ :=
  fun b => if b = 0 then 1 else -1

/-- The parity function `χ S : 𝔽₂ⁿ → ℝ` for `S ⊆ [n]`, defined by
    `(χ S)(x) = ∏_{i ∈ S} χ(xᵢ) = (-1)^(∑_{i ∈ S} xᵢ)`. (Definition 1.2) -/
noncomputable def parityFun (S : Finset (Fin n)) : BooleanFunction n :=
  fun x => ∏ i ∈ S, chi (x i)

/-- `χ S` — the parity function on the coordinate set `S`. -/
scoped prefix:max "χ" => parityFun

/-! ### §1.3–1.4 Expectation, Fourier coefficients -/

/-- The uniform expectation `𝔼[f] = 2⁻ⁿ · ∑_x f(x)`. -/
noncomputable def expect (f : BooleanFunction n) : ℝ :=
  Finset.univ.expect f

/-- `𝔼[f]` — the uniform expectation of `f` over the Hamming cube. -/
scoped notation "𝔼[" f "]" => expect f

/-- The Fourier coefficient `𝓕 f S = ⟪f, χ S⟫`.
    (Proposition 1.8 / our definition) -/
noncomputable def fourierCoeff (f : BooleanFunction n) (S : Finset (Fin n)) : ℝ :=
  ⟪f, χ S⟫

/-- `𝓕 f S` — the Fourier coefficient of `f` on the coordinate set `S`. -/
scoped notation "𝓕" => fourierCoeff

/-! ### Bridge lemmas -/

/-- Unfold `𝔼[f]` to the explicit sum form `1/2^n · ∑_x f(x)`. -/
theorem expect_unfold (f : BooleanFunction n) :
    𝔼[f] = 1 / 2 ^ n * ∑ x : Cube n, f x := by
  rw [expect, Finset.expect_eq_sum_div_card (f := (f : Cube n → ℝ))]
  simp [Finset.card_univ, ZMod.card]; ring

/-- The inner product equals the expectation of the product.
    This is the book's Definition 1.3: `⟪f, g⟫ = 𝔼[f·g]`. -/
theorem inner_eq_expect (f g : BooleanFunction n) :
    ⟪f, g⟫ = 𝔼[fun x => f x * g x] := by
  simp [inner_def, expect, Finset.expect_eq_sum_div_card, div_eq_inv_mul]

/-! ### §1.4 Mean, variance, covariance -/

/-- A function `f : 𝔽₂ⁿ → ℝ` is *unbiased* (or *balanced*) if `𝔼[f] = 0`.
    (Definition 1.11) -/
def IsUnbiased (f : BooleanFunction n) : Prop := 𝔼[f] = 0

/-- The variance of `f : 𝔽₂ⁿ → ℝ`, defined as
    `Var[f] = 𝔼[f²] - 𝔼[f]²`. (Proposition 1.13) -/
noncomputable def variance (f : BooleanFunction n) : ℝ :=
  𝔼[fun x => f x ^ 2] - (𝔼[f]) ^ 2

/-- `Var[f]` — the variance of `f`. -/
scoped notation "Var[" f "]" => variance f

/-- The covariance of `f, g : 𝔽₂ⁿ → ℝ`, defined as
    `Cov[f, g] = 𝔼[f·g] - 𝔼[f]·𝔼[g]`. (Proposition 1.16) -/
noncomputable def covariance (f g : BooleanFunction n) : ℝ :=
  𝔼[fun x => f x * g x] - 𝔼[f] * 𝔼[g]

/-- `Cov[f, g]` — the covariance of `f` and `g`. -/
scoped notation "Cov[" f ", " g "]" => covariance f g

/-- The 0-1 indicator function of a predicate `P` on `𝔽₂ⁿ`.
    `(𝟙 P)(x) = 1` if `P x`, else `0`.

    The book (Definition 1.22) defines `𝟙_A` for a set `A ⊆ 𝔽₂ⁿ`. We generalize
    to predicates so that probability expressions like `Pr_x[P(x)] = 𝔼[𝟙 P]`
    read cleanly without `Finset.univ.filter` boilerplate. For the set version,
    use `𝟙 (· ∈ A)`. -/
noncomputable def indicator (P : Cube n → Prop) : BooleanFunction n :=
  fun x => if P x then 1 else 0

/-- `𝟙 P` — the 0-1 indicator function of predicate `P`. -/
scoped prefix:max "𝟙" => indicator

/-- The uniform probability `Pr_x[P(x)] = 𝔼[𝟙 P]`. -/
noncomputable def prob (P : Cube n → Prop) : ℝ := 𝔼[𝟙 P]

/-- `Pr[P]` — the uniform probability of predicate `P`. -/
scoped notation "Pr[" P "]" => prob P

/-- The joint uniform probability `Pr_{x,y}[P(x,y)] = 𝔼_x[𝔼_y[𝟙 (P x)]]`.
    Equivalent to the uniform probability over the product space by Fubini. -/
noncomputable def prob₂ (P : Cube n → Cube n → Prop) : ℝ :=
  𝔼[fun x => 𝔼[𝟙 (P x)]]

/-- `Pr₂[P]` — the joint uniform probability of `P` over pairs. -/
scoped notation "Pr₂[" P "]" => prob₂ P

/-- The relative Hamming distance between functions `f` and `g`,
    `dist(f, g) = Pr_x[f(x) ≠ g(x)]`. (Definition 1.10) -/
noncomputable def hammingDist (f g : BooleanFunction n) : ℝ :=
  Pr[fun x => f x ≠ g x]

/-! ### §1.4 Fourier weight distribution -/

/-- The Fourier weight of `f` on set `S`, defined as `(𝓕 f S)²`.
    (Definition 1.17) -/
noncomputable def fourierWeight (f : BooleanFunction n) (S : Finset (Fin n)) : ℝ :=
  𝓕 f S ^ 2

/-- The Fourier weight of `f` at degree `k`:
    `𝐖 f k = ∑_{|S|=k} (𝓕 f S)²`. (Definition 1.19) -/
noncomputable def fourierWeightAtDegree (f : BooleanFunction n) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
    fourierWeight f S

/-- `𝐖 f k` — the Fourier weight of `f` at degree `k`. -/
scoped notation "𝐖" => fourierWeightAtDegree

/-- The degree-k part of `f`: `f^{=k} = ∑_{|S|=k} 𝓕 f S · χ S`.
    (Definition 1.19) -/
noncomputable def degreePart (f : BooleanFunction n) (k : ℕ) : BooleanFunction n :=
  fun x => ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
    𝓕 f S * (χ S) x

/-- The degree-at-most-k part of `f`: `f^{≤k} = ∑_{|S|≤k} 𝓕 f S · χ S`.
    (Definition 1.19) -/
noncomputable def lowDegreePart (f : BooleanFunction n) (k : ℕ) : BooleanFunction n :=
  fun x => ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ k),
    𝓕 f S * (χ S) x

/-- The Fourier weight of `f` at degrees above `k`:
    `𝐖^{>k}[f] = ∑_{|S|>k} (𝓕 f S)²`. (Definition 1.19) -/
noncomputable def fourierWeightAbove (f : BooleanFunction n) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card > k),
    fourierWeight f S

/-- The *(real) degree* of `f : 𝔽₂ⁿ → ℝ`:
    `deg(f) = max { |S| : 𝓕 f S ≠ 0 }`. (Exercise 1.10, referenced in main text)

    Returns `⊥` for the zero function (which has no nonzero Fourier coefficients).
    The book leaves the degree undefined in this case. We use `WithBot ℕ` so that
    degree comparisons integrate cleanly with Mathlib's order theory. -/
noncomputable def degree (f : BooleanFunction n) : WithBot ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin n) => 𝓕 f S ≠ 0)).sup
    (fun S => (S.card : WithBot ℕ))

/-! ### §1.5 Probability densities and convolution -/

/-- A probability density on `𝔽₂ⁿ` is a nonneg function with
    `𝔼[φ] = 1`. (Definition 1.20) -/
structure IsDensity (φ : BooleanFunction n) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  expect_one : 𝔼[φ] = 1

/-- The density function associated to a nonempty set `A ⊆ 𝔽₂ⁿ`:
    `φ_A = (1 / 𝔼[𝟙 A]) · 𝟙 A`. (Definition 1.22)

    **Warning**: This definition is junk when `A = ∅`, since it divides by
    `𝔼[𝟙 ∅] = 0`. The book requires `A` to be nonempty. Theorems using
    `setDensity` should include a hypothesis `A.Nonempty` where needed. -/
noncomputable def setDensity (A : Finset (Cube n)) : BooleanFunction n :=
  fun x => (1 / 𝔼[𝟙 (· ∈ A)]) * (𝟙 (· ∈ A)) x

/-- The convolution of `f, g : 𝔽₂ⁿ → ℝ`, defined by
    `(f ⊛ g)(x) = 𝔼_y[f(y)·g(x + y)]`. (Definition 1.24) -/
noncomputable def convolution (f g : BooleanFunction n) : BooleanFunction n :=
  fun x => 𝔼[fun y => f y * g (x + y)]

/-- `f ⊛ g` — the convolution of `f` and `g`. -/
scoped infixl:70 " ⊛ " => convolution

/-! ### §1.6 Linearity and the BLR test -/

/-- A function `f : 𝔽₂ⁿ → 𝔽₂` (encoded as `BooleanFunction n` with ±1 values)
    is *linear* if it equals some parity function `χ S`. (Definition 1.28) -/
def IsLinear (f : BooleanFunction n) : Prop :=
  ∃ S : Finset (Fin n), ∀ x, f x = (χ S) x

/-- A function `f : 𝔽₂ⁿ → ℝ` is *multiplicative* if `f(x+y) = f(x)·f(y)` for all
    `x, y`. This generalizes property (1) from Definition 1.28 to real-valued
    functions; the equivalence with `IsLinear` requires `IsBooleanValued`
    (see `isLinear_iff_isMultiplicative`). -/
def IsMultiplicative (f : BooleanFunction n) : Prop :=
  ∀ x y, f (x + y) = f x * f y

/-- Two Boolean-valued functions are `ε`-close if `dist(f, g) ≤ ε`.
    (Definition 1.29) -/
def IsClose (f g : BooleanFunction n) (ε : ℝ) : Prop :=
  hammingDist f g ≤ ε

/-- A Boolean-valued function is `ε`-close to a property `P` if there
    exists `g` satisfying `P` with `dist(f, g) ≤ ε`. (Definition 1.29) -/
def IsCloseToProperty (f : BooleanFunction n)
    (P : BooleanFunction n → Prop) (ε : ℝ) : Prop :=
  ∃ g, P g ∧ IsClose f g ε

/-- The BLR acceptance probability: `Pr_{x,y}[f(x)·f(y) = f(x+y)]`,
    which equals `1/2 + 1/2 · ∑_S 𝓕 f S ^ 3`. -/
noncomputable def blrAcceptProb (f : BooleanFunction n) : ℝ :=
  Pr₂[fun x y => f x * f y = f (x + y)]

end BooleanAnalysis

end Complexity

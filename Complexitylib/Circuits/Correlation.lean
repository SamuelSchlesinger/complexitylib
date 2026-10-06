/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Defs
public import Complexitylib.Circuits.Correlation.Internal.Asymptotics
public import Complexitylib.Circuits.Frontier.Layouts
import Mathlib.Tactic

/-!
# Exponentially small correlation with quadratic forms

Fan-in-two circuits over any basis with at most `c n` gates of positive arity, for any
`c < c* = 1 + 1/(2A) ≈ 2.78125`, have correlation `2^{-Ω(n)}` with every family of quadratic
forms over `GF(2)` whose bisection cut rank is `⌊n/2⌋ - o(n)`. Here `A = 2p ≈ 0.2807` is the
Gaussian layout coefficient of the frontier method (`Frontier.layoutBound_gaussian`). The
circuit model, the gate count (`Cslib.Circuits.Circuit.innerSize`), and the agreement measure
are those of the frontier method's average-case theorem `Frontier.averageCase_abs`, so the
bounds are directly comparable. The best previously published average-case bounds for the full
binary basis are `2.5 n` (Chen–Kabanets, COCOON 2015, for an explicit affine extractor) and
`2.6 n` (Golovnev–Kulikov–Smal–Tamaki, MFCS 2016, for non-explicit quadratic extractors).

## The argument

For a quadratic form `f` and a cut `X` of the coordinates, Lindsey's lemma bounds the signed sum
of `(-1)^f` over every rectangle `R` for `X` by `√(|R| 2^{n - ρ(X)})`, where the cut rank
`ρ(X)` is the rank of the block of the polar matrix with rows `X` and columns `Xᶜ`. Partition
the inputs into `K` rectangle classes for one cut on which the circuit is constant;
Cauchy–Schwarz over the classes gives `correlation² ≤ K · 2^{-ρ(X)}`. Two partitions apply:

* if the circuit leaves the inputs `D` unread, its two output classes are rectangles for `D`
  (`correlation_sq_le_of_unread`);
* along a layout of the compiled constraint network of width `w`, the output and the values on
  the frontier when exactly `⌊n/2⌋` inputs have been read give `2 · 2^w` rectangle classes
  (`correlation_sq_le_of_layout`).

If every set of `⌊n/2⌋` coordinates has cut rank at least `⌊n/2⌋ - τ n`, balancing the two at
`θ n` unread inputs, with `θ = (1/2 - A (c - 1))/(1 + A)`, gives the rate
`(c* - c)/(2L) - τ/2` with `L = 1 + 1/A` (`eventually_correlation_le`), and
`(c* - c)/(2L)` for a sublinear deficiency (`eventually_correlation_le_of_isLittleO`,
`eventually_correlation_le_gaussian`).

## Main results

* `correlation_sq_mul_two_pow_cutRank_le`: correlation through rectangle classes.
* `correlation_sq_le_of_unread`, `correlation_sq_le_of_layout`: the finite bounds.
* `eventually_correlation_le`, `eventually_correlation_le_of_isLittleO`,
  `eventually_correlation_le_gaussian`: correlation `2^{-γ n}` for every family of quadratic
  forms whose bisection cut rank is `⌊n/2⌋ - o(n)`.
-/

@[expose] public section

namespace Complexity.Correlation

open Set Filter Asymptotics Complexity.Frontier

universe v

/-! ### Rectangle classes -/

/-- **Correlation through rectangle classes.** Let `g` be constant on the classes of `msg`, and
let every class be a rectangle for one cut `X` of the coordinates. Then the correlation of `g`
with the quadratic form of `Q` satisfies `correlation² · 2^{cutRank Q X} ≤ |M|`, where `M` is
the type of messages. This is Lindsey's lemma on each class and Cauchy–Schwarz over the
classes. -/
theorem correlation_sq_mul_two_pow_cutRank_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (ZMod 2)) (g : (ι → Bool) → Bool) {M : Type*} [Fintype M]
    [DecidableEq M] (msg : (ι → Bool) → M) (X : Set ι)
    (hg : ∀ x y, msg x = msg y → g x = g y)
    (hrect : ∀ x₀, ∃ (A : Set (X → Bool)) (B : Set (↥Xᶜ → Bool)),
      {x | msg x = msg x₀} = rectangle X A B) :
    correlation (quadForm Q) g ^ 2 * 2 ^ cutRank Q X ≤ Fintype.card M := by
  rw [correlation, sq_abs]
  exact sq_two_mul_agreement_sub_one_mul_le Q g msg X hg hrect

/-! ### Finite bounds for circuits -/

/-- **Unread inputs.** If every set of `⌊n/2⌋` coordinates has cut rank at least
`⌊n/2⌋ - e`, a circuit that leaves at least `k ≤ ⌊n/2⌋` inputs unread has
`correlation² ≤ 2^{1 + e - k}` with the quadratic form. -/
theorem correlation_sq_le_of_unread {σ : Cslib.Circuits.Signature} {n : ℕ}
    (I : Cslib.Circuits.Interpretation σ Bool) (c : Cslib.Circuits.Circuit σ n 1)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ cutRank Q U + e)
    {k : ℕ} (hk : k ≤ n / 2) (hkd : k ≤ (constraintNetwork I {true} c).readᶜ.ncard) :
    correlation (quadForm Q) (fun x => c.eval I x 0) ^ 2 ≤ (2 : ℝ) ^ (1 + e - k) := by
  rw [correlation, sq_abs]
  exact sq_corr_le_of_unread I c Q hQ hk hkd

/-- **The frontier bound.** If every set of `⌊n/2⌋` coordinates has cut rank at least
`⌊n/2⌋ - e`, a circuit that reads at least `⌊n/2⌋` inputs, whose compiled constraint network
has a layout with every frontier of at most `w` edges, has
`correlation² ≤ 2^{1 + w + e - ⌊n/2⌋}` with the quadratic form. -/
theorem correlation_sq_le_of_layout {σ : Cslib.Circuits.Signature} {n : ℕ}
    (I : Cslib.Circuits.Interpretation σ Bool) (c : Cslib.Circuits.Circuit σ n 1)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ cutRank Q U + e)
    (π : Layout (Compiler.Vertex c.program c.outputs)) {w : ℕ}
    (hw : ∀ t, ((constraintNetwork I {true} c).frontier π t).ncard ≤ w)
    (hread : n / 2 ≤ (constraintNetwork I {true} c).read.ncard) :
    correlation (quadForm Q) (fun x => c.eval I x 0) ^ 2 ≤
      (2 : ℝ) ^ (1 + w + e - (n / 2 : ℕ)) := by
  rw [correlation, sq_abs]
  exact sq_corr_le_of_layout I c Q hQ π hw hread

/-! ### Asymptotic bounds for families of quadratic forms -/

theorem two_mul_rate_eq {A c : ℝ} (hA : 0 < A) :
    2 * ((1 + 1 / (2 * A) - c) / (2 * (1 + 1 / A))) = (1 / 2 - A * (c - 1)) / (1 + A) := by
  field_simp
  ring

/-- **Exponentially small correlation.** Under the layout hypothesis with coefficient `A`,
let every set of `⌊n/2⌋` coordinates have cut rank at least `⌊n/2⌋ - τ n` for all large `n`.
Then for every `c ≥ 1/2` and every `γ < (c* - c)/(2L) - τ/2`, where `c* = 1 + 1/(2A)` and
`L = 1 + 1/A`, for all large `n` every fan-in-two circuit over any basis with at most `c n` gates
of positive arity has correlation at most `2^{-γ n}` with the quadratic form. -/
theorem eventually_correlation_le {A c τ γ : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hc : 1 / 2 ≤ c) (hγ : γ < (1 + 1 / (2 * A) - c) / (2 * (1 + 1 / A)) - τ / 2)
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ cutRank (Q n) U + τ * n) :
    ∀ᶠ n in atTop, ∀ (σ : Cslib.Circuits.Signature.{v})
      (I : Cslib.Circuits.Interpretation σ Bool) (C : Cslib.Circuits.Circuit σ n 1),
      C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        correlation (quadForm (Q n)) (fun x => C.eval I x 0) ≤ (2 : ℝ) ^ (-γ * n) := by
  have h2γ : 2 * γ < (1 / 2 - A * (c - 1)) / (1 + A) - τ := by
    rw [← two_mul_rate_eq hA]
    linarith
  exact eventually_abs_corr_le hA hlayout hc h2γ Q hQ

/-- **Exponentially small correlation, sublinear deficiency.** Under the layout hypothesis with
coefficient `A`, if every set of `⌊n/2⌋` coordinates has cut rank at least `⌊n/2⌋ - o(n)`,
then for every `c ≥ 1/2` and every `γ < (c* - c)/(2L)`, for all large `n` every fan-in-two
circuit with at most `c n` gates of positive arity has correlation at most `2^{-γ n}` with the
quadratic form. -/
theorem eventually_correlation_le_of_isLittleO {A c γ : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound 3 A) (hc : 1 / 2 ≤ c)
    (hγ : γ < (1 + 1 / (2 * A) - c) / (2 * (1 + 1 / A)))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ cutRank (Q n) U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Cslib.Circuits.Signature.{v})
      (I : Cslib.Circuits.Interpretation σ Bool) (C : Cslib.Circuits.Circuit σ n 1),
      C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        correlation (quadForm (Q n)) (fun x => C.eval I x 0) ≤ (2 : ℝ) ^ (-γ * n) := by
  have h2γ : 2 * γ < (1 / 2 - A * (c - 1)) / (1 + A) := by
    rw [← two_mul_rate_eq hA]
    linarith
  exact eventually_abs_corr_le_of_isLittleO hA hlayout hc h2γ Q e he hQ

/-- The Gaussian threshold and rate constants in closed form. -/
theorem gaussian_rate_eq (c : ℝ) :
    (1 + 1 / (2 * (2 * Gaussian.gaussianCoefficient)) - c) /
        (2 * (1 + 1 / (2 * Gaussian.gaussianCoefficient))) =
      (1 + Real.pi / (6 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - c) /
        (2 * (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)))) := by
  have h := Gaussian.one_add_inv_two_mul_gaussianCoefficient
  have h' : 1 / (2 * Gaussian.gaussianCoefficient) =
      Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by linarith
  have h4 : 1 / (2 * (2 * Gaussian.gaussianCoefficient)) =
      Real.pi / (6 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
    have hp := Gaussian.gaussianCoefficient_pos
    have e1 : 1 / (2 * (2 * Gaussian.gaussianCoefficient)) =
        1 / (2 * Gaussian.gaussianCoefficient) / 2 := by
      field_simp
    rw [e1, h']
    ring
  rw [h4, h']

/-- **Exponentially small correlation below `2.78 n` gates.** If every set of `⌊n/2⌋`
coordinates has cut rank at least `⌊n/2⌋ - o(n)`, then for every `c ≥ 1/2` and every
`γ < (c* - c)/(2L)`, with `c* = 1 + π/(6 arccos((1 + 2√2)/4)) ≈ 2.78125` and
`L = 1 + π/(3 arccos((1 + 2√2)/4)) ≈ 4.5625`, for all large `n` every fan-in-two circuit over
any basis with at most `c n` gates of positive arity has correlation at most `2^{-γ n}` with the
quadratic form. -/
theorem eventually_correlation_le_gaussian {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ < (1 + Real.pi / (6 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - c) /
      (2 * (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)))))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ cutRank (Q n) U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Cslib.Circuits.Signature.{v})
      (I : Cslib.Circuits.Interpretation σ Bool) (C : Cslib.Circuits.Circuit σ n 1),
      C.FanInAtMost 2 → (C.innerSize : ℝ) ≤ c * n →
        correlation (quadForm (Q n)) (fun x => C.eval I x 0) ≤ (2 : ℝ) ^ (-γ * n) := by
  have hA : 0 < 2 * Gaussian.gaussianCoefficient :=
    mul_pos two_pos Gaussian.gaussianCoefficient_pos
  refine eventually_correlation_le_of_isLittleO hA layoutBound_gaussian hc ?_ Q e he hQ
  rwa [gaussian_rate_eq]

end Complexity.Correlation

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts
public import Complexitylib.Circuits.Frontier.Linear.LowerBound
public import Mathlib.Algebra.CharZero.Infinite

/-!
# Unconditional lower bounds for linear maps

Combining the lower bound for linear maps (`Frontier.lowerBound_linear`) with the layout bound
for subcubic graphs (`Frontier.layoutBound_gaussian`) gives, with
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`:

* **Finite fields, any basis** (`Frontier.linear_finite_gaussian`): every circuit of fan-in two
  computing a totally regular map `F^N → F^N` has more than `(L - ε) N` inner gates, uniformly in
  the finite field `F`.
* **Infinite fields, polynomial operations** (`Frontier.linear_polynomial_gaussian`): the same,
  for operations of fan-in two given by polynomials of any degree with any coefficients.
* **Arithmetic circuits** (`Frontier.arith_cauchy_gaussian`): over every field of characteristic
  zero, in particular over `ℚ`, `ℝ`, and `ℂ`, every circuit of additions, multiplications, and
  constants computing the Cauchy map `x ↦ (∑_j x_j / (i - N - j))_i` uses more than `(L - ε) N`
  additions and multiplications. Constants are free.
* **Prime fields** (`Frontier.cauchyZMod_gaussian`): the same Cauchy matrices over `ZMod q`,
  for every prime `q ≥ 2 N`, need more than `(L - ε) N` gates in every basis of fan-in two.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Filter Matrix

universe u v

/-- The coefficient of the Gaussian layout bound. -/
private theorem one_add_one_div_gaussian :
    1 + 1 / (2 * Gaussian.gaussianCoefficient) =
      1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) :=
  Gaussian.one_add_inv_two_mul_gaussianCoefficient

private theorem two_gaussian_pos : 0 < 2 * Gaussian.gaussianCoefficient :=
  mul_pos two_pos Gaussian.gaussianCoefficient_pos

/-- **Totally regular maps over finite fields**, for every basis of fan-in two. -/
theorem linear_finite_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        TotallyRegular M → c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
            c.innerSize := by
  filter_upwards [lowerBound_linear_finite.{u, v} le_rfl two_gaussian_pos layoutBound_gaussian
    hε] with N hN
  intro F _ _ σ I M c hM hfan hc
  have h := hN F σ I M c hM hfan hc
  rw [one_add_one_div_gaussian] at h
  norm_num at h ⊢
  exact h

/-- **Totally regular maps over infinite fields**, for every basis of fan-in two whose
operations are polynomials. -/
theorem linear_polynomial_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), IsPolynomial I → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), TotallyRegular M → c.FanInAtMost 2 →
          c.Computes I (fun x => M *ᵥ x) →
            (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
              c.innerSize := by
  filter_upwards [lowerBound_linear_polynomial.{u, v} le_rfl two_gaussian_pos
    layoutBound_gaussian hε] with N hN
  intro F _ _ σ I hI M c hM hfan hc
  have h := hN F σ I hI M c hM hfan hc
  rw [one_add_one_div_gaussian] at h
  norm_num at h ⊢
  exact h

/-- Arithmetic circuits have fan-in at most two. -/
theorem fanInAtMost_two_arith {F : Type u} {n s : ℕ} :
    ∀ p : Program (arithSignature F) n s, p.FanInAtMost 2
  | .empty => trivial
  | .gate p line => ⟨fanInAtMost_two_arith p, by rcases line with ⟨_ | _ | _, _⟩ <;> simp⟩

/-- **Arithmetic circuits for Cauchy maps.** Over every field of characteristic zero, every
arithmetic circuit computing `x ↦ (∑_j x_j / (i - N - j))_i` uses more than `(L - ε) N` additions
and multiplications, for all large `N`. -/
theorem arith_cauchy_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [CharZero F] (c : Circuit (arithSignature F) N N),
      c.Computes (arithInterpretation F) (fun x => cauchyNat F N *ᵥ x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
          c.innerSize := by
  filter_upwards [linear_polynomial_gaussian.{u, u} hε] with N hN
  intro F _ _ c hc
  exact hN F _ _ isPolynomial_arithInterpretation _ c (totallyRegular_cauchyNat N)
    (fanInAtMost_two_arith c.program) hc

/-- **Cauchy maps over prime fields.** For every prime `q ≥ 2 N`, every circuit of fan-in two,
over any basis on `ZMod q`, computing `x ↦ (∑_j x_j / (i - N - j))_i` has more than `(L - ε) N`
inner gates, for all large `N`, uniformly in `q`. -/
theorem cauchyZMod_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q → ∀ (σ : Signature.{v})
      (I : Interpretation σ (ZMod q)) (c : Circuit σ N N), c.FanInAtMost 2 →
        c.Computes I (fun x => cauchyNat (ZMod q) N *ᵥ x) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
            c.innerSize := by
  filter_upwards [linear_finite_gaussian.{0, v} hε] with N hN
  intro q _ hq σ I c hfan hc
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  exact hN (ZMod q) σ I _ c (totallyRegular_cauchyZMod q N hq) hfan hc

/-- Totally regular maps over finite fields also have the ternary `7N/4 - o(N)` bound. -/
theorem linear_finite_fanInThree {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        TotallyRegular M → c.FanInAtMost 3 → c.Computes I (fun x => M *ᵥ x) →
          (7 / 4 - ε) * N < c.innerSize := by
  filter_upwards [lowerBound_linear_finite.{u, v} (by norm_num : 2 ≤ 3)
    (by norm_num : (0 : ℝ) < 2 / 5) layoutBound_two_fifths
    (show 0 < 2 * ε by positivity)] with N hN
  intro F _ _ σ I M c hM hfan hc
  have H := hN F σ I M c hM hfan hc
  norm_num at H
  linarith

/-- **Every fixed fan-in over finite fields**, with the Gaussian degree coefficient. -/
theorem linear_finite_degree {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        TotallyRegular M → c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * N <
            (r - 1) * c.innerSize :=
  lowerBound_linear_finite hr (Gaussian.degreeCoefficient_pos (by lia))
    (layoutBound_degree (by lia)) hε

/-- **Every fixed fan-in over infinite fields**, for polynomial operations. -/
theorem linear_polynomial_degree {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), IsPolynomial I → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), TotallyRegular M → c.FanInAtMost r →
          c.Computes I (fun x => M *ᵥ x) →
            (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * N <
              (r - 1) * c.innerSize :=
  lowerBound_linear_polynomial hr (Gaussian.degreeCoefficient_pos (by lia))
    (layoutBound_degree (by lia)) hε

/-- The ternary bound over infinite fields with polynomial operations. -/
theorem linear_polynomial_fanInThree {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), IsPolynomial I → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), TotallyRegular M → c.FanInAtMost 3 →
          c.Computes I (fun x => M *ᵥ x) → (7 / 4 - ε) * N < c.innerSize := by
  filter_upwards [lowerBound_linear_polynomial.{u, v} (by norm_num : 2 ≤ 3)
    (by norm_num : (0 : ℝ) < 2 / 5) layoutBound_two_fifths
    (show 0 < 2 * ε by positivity)] with N hN
  intro F _ _ σ I hI M c hM hfan hc
  have H := hN F σ I hI M c hM hfan hc
  norm_num at H
  linarith

end Complexity.Frontier

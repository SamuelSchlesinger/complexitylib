/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Cauchy
public import Complexitylib.Algebraic.Basis.Arithmetic
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Arithmetic.Internal

/-!
# Arithmetic lower bounds with free constants

Addition and multiplication are polynomial operations. More strongly, every
arithmetic circuit whose outputs are nonconstant can absorb all its constant
gates into polynomial coefficients, emitting exactly one gate per original
addition or multiplication. The Gaussian lower bound therefore applies to
`Arithmetic.gateCost`, where arbitrary constant gates are free.
-/

public section

namespace Algebraic.Cutwidth.MultiOutput.Polynomial

open Filter Matrix

/-- Addition, multiplication, and any family of constants are polynomial operations. -/
theorem isPolynomial_arithmetic {F K : Type*} [CommSemiring F] (constant : K → F) :
    IsPolynomial (σ := Arithmetic.signature K) (Arithmetic.interpretation constant) := by
  intro op
  cases op with
  | add =>
      refine ⟨MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2), ?_⟩
      intro x
      change x (0 : Fin 2) + x (1 : Fin 2) = MvPolynomial.eval (fun i : Fin 2 => x i)
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
      simp
  | mul =>
      refine ⟨MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2), ?_⟩
      intro x
      change x (0 : Fin 2) * x (1 : Fin 2) = MvPolynomial.eval (fun i : Fin 2 => x i)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
      simp
  | constant c =>
      exact ⟨MvPolynomial.C (constant c), fun _ => (MvPolynomial.eval_C _).symm⟩

/-- Constant elimination preserves all outputs and exactly the number of arithmetic operations. -/
theorem exists_polynomial_circuit_of_nonconstant {F K : Type*} [CommSemiring F]
    {n m : ℕ} (hn : 0 < n) (constant : K → F)
    (c : Circuit (Arithmetic.signature K) n m)
    (nonconstant : ∀ j, ∃ x y,
      c.eval (Arithmetic.interpretation constant) x j ≠
        c.eval (Arithmetic.interpretation constant) y j) :
    ∃ d : Circuit (signature F) n m,
      d.size = c.cost Arithmetic.gateCost ∧ d.FanInAtMost 2 ∧
      ∀ x, d.eval (interpretation F) x = c.eval (Arithmetic.interpretation constant) x :=
  ArithmeticInternal.exists_circuit hn constant c nonconstant

universe u v

/-- Totally regular maps need the Gaussian coefficient in additions and multiplications,
with arbitrary constants free, over any field. -/
theorem eventually_lt_arithmeticCost_of_totallyRegular {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin N) (Fin N) F),
      TotallyRegular M → ∀ (K : Type v) (constant : K → F)
      (c : Circuit (Arithmetic.signature K) N N),
      c.Computes (Arithmetic.interpretation constant) (fun x => M *ᵥ x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
          c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_size.{u} hε, eventually_gt_atTop 0] with N bound positive
  intro F _ M regular K constant c computes
  obtain ⟨d, size, fan, agrees⟩ := exists_polynomial_circuit_of_nonconstant positive constant c
    (ArithmeticInternal.outputs_nonconstant positive constant c regular computes)
  have result := bound F M regular d fan (fun x => (agrees x).trans (computes x))
  simpa only [size] using result

/-- The explicit rational Cauchy family has the same lower bound with free arithmetic constants. -/
theorem eventually_lt_arithmeticCost_cauchyCharZero {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] [CharZero F],
      ∀ (K : Type v) (constant : K → F) (c : Circuit (Arithmetic.signature K) N N),
      c.Computes (Arithmetic.interpretation constant) (fun x => cauchyCharZero F N *ᵥ x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
          c.cost Arithmetic.gateCost := by
  filter_upwards [eventually_lt_arithmeticCost_of_totallyRegular.{u, v} hε] with N bound
  intro F _ _ K constant c computes
  exact bound F (cauchyCharZero F N) (totallyRegular_cauchyCharZero F N) K constant c computes

end Algebraic.Cutwidth.MultiOutput.Polynomial

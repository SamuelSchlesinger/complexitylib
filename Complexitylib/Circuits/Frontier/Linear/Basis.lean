/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Upstream
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul

/-!
# Affine, polynomial, and arithmetic bases

Three ways of computing over a field `F`:

* the *affine basis* (`Frontier.affineSignature`), whose operations of arity `k` are the affine
  maps `x ↦ a₀ x₀ + ... + a_{k-1} x_{k-1} + b`;
* *polynomial interpretations* (`Frontier.IsPolynomial`), in which every operation of a
  signature is a polynomial in its arguments, with any coefficients and of any degree;
* the *arithmetic basis* (`Frontier.arithSignature`): addition, multiplication, and a constant
  gate for each element of `F`.

Arithmetic circuits are polynomial. Over a finite field every operation is polynomial, so the
distinction matters only over infinite fields, where it is essential: an infinite field admits
bijections `F × F → F`, through which a single wire can carry any amount of information.

In arithmetic circuits the constants are leaves, and `Cslib.Circuits.Circuit.innerSize` counts
exactly the additions and multiplications.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits

universe u

variable (F : Type u)

/-- The *affine basis* over `F`: an operation of arity `k` is a coefficient vector and a
constant. -/
abbrev affineSignature : Signature.{u} where
  Op := Σ k : ℕ, (Fin k → F) × F
  Arity o := o.1

/-- An affine operation computes `x ↦ ∑ i, a i * x i + b`. -/
def affineInterpretation [Semiring F] : Interpretation (affineSignature F) F :=
  fun o x => ∑ i, o.2.1 i * x i + o.2.2

/-- The operations of the arithmetic basis. -/
inductive ArithOp : Type u
  /-- Addition. -/
  | add
  /-- Multiplication. -/
  | mul
  /-- A constant. -/
  | const (c : F)

/-- The arity of an arithmetic operation. -/
abbrev ArithOp.arity : ArithOp F → ℕ
  | .add => 2
  | .mul => 2
  | .const _ => 0

/-- The *arithmetic basis*: addition and multiplication of arity two, and constants of arity
zero. -/
abbrev arithSignature : Signature.{u} where
  Op := ArithOp F
  Arity := ArithOp.arity F

/-- Addition, multiplication, and constants. -/
def arithInterpretation [Semiring F] : Interpretation (arithSignature F) F
  | .add, x => x 0 + x 1
  | .mul, x => x 0 * x 1
  | .const c, _ => c

variable {F}

/-- An interpretation is *polynomial* when every operation is given by a polynomial in its
arguments. -/
def IsPolynomial [CommSemiring F] {σ : Signature} (I : Interpretation σ F) : Prop :=
  ∀ o, ∃ P : MvPolynomial (Fin (σ.Arity o)) F, ∀ x, I o x = MvPolynomial.eval x P

/-- Arithmetic circuits are polynomial. -/
theorem isPolynomial_arithInterpretation [CommSemiring F] :
    IsPolynomial (arithInterpretation F) := by
  rintro (_ | _ | c)
  · exact ⟨.X 0 + .X 1, fun x => by simp [arithInterpretation]⟩
  · exact ⟨.X 0 * .X 1, fun x => by simp [arithInterpretation]⟩
  · exact ⟨.C c, fun x => by simp [arithInterpretation]⟩

/-- The affine basis is polynomial. -/
theorem isPolynomial_affineInterpretation [CommSemiring F] :
    IsPolynomial (affineInterpretation F) := by
  rintro ⟨k, a, b⟩
  exact ⟨∑ i, .C (a i) * .X i + .C b, fun x => by simp [affineInterpretation]⟩

end Complexity.Frontier

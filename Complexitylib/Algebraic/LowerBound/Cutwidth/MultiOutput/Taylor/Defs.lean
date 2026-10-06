/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Circuit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Polynomial gates over commutative algebras: definitions

A program whose gates are polynomials with coefficients in a commutative ring `K` can be run
over every commutative `K`-algebra `A`: each operation substitutes its arguments into its gate
polynomial. This file fixes the notation for that formal semantics.

* `algebraInterpretation P A`: the interpretation over `A` in which the operation `op`
  substitutes its arguments into the polynomial `P op`.
* `wirePolynomial P p w`: the polynomial in the inputs carried by the wire `w`, the value of `w`
  over the polynomial ring `K[X₀, …, X_{n-1}]` at the variables.
* `FormallyComputes P c f`: every output wire of `c` carries the polynomial `f o`. This is the
  usual notion of an arithmetic circuit computing a polynomial; over an infinite field it agrees
  with computing the polynomial function.
* `jacobian f a` and `hessian g a`: the matrices of first partial derivatives of a family of
  polynomials and of second partial derivatives of one polynomial, evaluated at a point `a` of
  a `K`-algebra `L`.

The gate polynomials may be arbitrary: any degree, any coefficients, any arity.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Taylor

variable {K : Type*} [CommSemiring K] {σ : Signature} {n s m : ℕ}

/-- The interpretation over a commutative `K`-algebra `A` in which each operation `op`
substitutes its arguments into its gate polynomial `P op`. -/
noncomputable def algebraInterpretation (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
    (A : Type*) [CommSemiring A] [Algebra K A] : Interpretation σ A :=
  fun op x => MvPolynomial.aeval x (P op)

/-- The polynomial carried by each input or gate wire: its value over the polynomial ring at
the variables. -/
noncomputable def wirePolynomial (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
    (p : Program σ n s) : Wire n s → MvPolynomial (Fin n) K :=
  p.trace (algebraInterpretation P (MvPolynomial (Fin n) K)) MvPolynomial.X

/-- A circuit with gate polynomials `P` formally computes the polynomials `f` when its output
`o` carries the polynomial `f o`. -/
def FormallyComputes (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
    (c : Circuit σ n m) (f : Fin m → MvPolynomial (Fin n) K) : Prop :=
  ∀ o, wirePolynomial P c.program (c.outputs o) = f o

/-- The Jacobian matrix of a family of polynomials at a point `a`: the entry in row `o` and
column `j` is `∂ f o / ∂ X j` evaluated at `a`. -/
noncomputable def jacobian {ι L : Type*} [CommSemiring L] [Algebra K L]
    (f : ι → MvPolynomial (Fin n) K) (a : Fin n → L) : Matrix ι (Fin n) L :=
  Matrix.of fun o j => MvPolynomial.aeval a (MvPolynomial.pderiv j (f o))

/-- The Hessian matrix of a polynomial at a point `a`: the entry in row `i` and column `j` is
`∂² g / ∂ X i ∂ X j` evaluated at `a`. -/
noncomputable def hessian {L : Type*} [CommSemiring L] [Algebra K L]
    (g : MvPolynomial (Fin n) K) (a : Fin n → L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j =>
    MvPolynomial.aeval a (MvPolynomial.pderiv i (MvPolynomial.pderiv j g))

end Algebraic.Cutwidth.MultiOutput.Taylor

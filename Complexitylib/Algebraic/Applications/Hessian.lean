/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian

/-!
# Applying the Hessian multiplication bound

The endpoint uses the natural rank of the evaluated Hessian matrix and an
ordinary polynomial evaluation equality. No Fusion problem, rank certificate,
or cardinal arithmetic is needed at the call site. Constants and additions
are free; every multiplication, including multiplication by a scalar, costs one.

The computation premise is equality of formal polynomials. Agreement of
polynomial functions on a finite field is a different premise and does not
suffice for this theorem.
-/

@[expose] public section

namespace Algebraic.Applications

open Fusion.Arithmetic.Interaction

/-- Half the Hessian rank, rounded up, lower-bounds the multiplication count
of a circuit computing a formal polynomial. -/
theorem hessianRank_lowerBound
    {K C : Type} [Field K]
    (constant : C → K)
    (point : Fin n → K)
    (polynomial : MvPolynomial (Fin n) K)
    (circuit : Circuit (Arithmetic.signature C) n g 1)
    (computes : circuit.eval
      (Arithmetic.interpretation (MvPolynomial.C ∘ constant)) MvPolynomial.X 0 = polynomial) :
    (Hessian.matrix point polynomial).rank ⌈/⌉ 2 ≤
      circuit.cost Arithmetic.multiplicationCost := by
  have rankBound : ((Hessian.matrix point polynomial).rank : Cardinal) ≤
      LinearMap.rank (Hessian.linearMap point polynomial) := by
    simp only [Matrix.rank, Hessian.linearMap, Matrix.toLin'_apply']
    exact (Module.finrank_eq_rank _ _).le
  exact Hessian.polynomial_circuit_multiplication_lowerBound
    constant point polynomial _ rankBound circuit computes

end Algebraic.Applications

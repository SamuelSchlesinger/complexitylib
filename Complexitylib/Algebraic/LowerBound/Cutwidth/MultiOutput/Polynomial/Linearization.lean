/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Internal

/-!
# Polynomial gates preserve local linear realizations

Taking formal derivatives at zero assigns a coefficient vector to every original
wire. The vector at a gate lies in the span of its argument vectors, irrespective
of the gate polynomial's degree or constant term. Thus the original program graph
supports a linear realization. Over an infinite field, computing a linear map as
a function guarantees that the output vectors are exactly its matrix rows.

The infinite-field hypothesis is needed only for the output identification, since
distinct polynomials can agree on every point of a finite field.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Polynomial

open Matrix

variable {F : Type*} [Field F] {σ : Signature} {n s m : ℕ}

/-- Every polynomial interpretation gives a local linear realization on the same graph. -/
noncomputable def realization {I : Interpretation σ F} (hI : IsPolynomial I)
    (p : Program σ n s) : Linear.Realization p F where
  value := fun w => linearPart (hI.wirePolynomial p w)
  input := fun j => Internal.linearPart_X j
  gate := Internal.linearPart_wirePolynomial_gate hI p

/-- A polynomial circuit computing a linear map over an infinite field has the exact
target rows at the outputs of its local linear realization. -/
theorem realization_output [Infinite F] {I : Interpretation σ F}
    (hI : IsPolynomial I) (c : Circuit σ n m) (M : Matrix (Fin m) (Fin n) F)
    (hc : c.Computes I fun x => M *ᵥ x) (i : Fin m) :
    (realization hI c.program).value (c.outputs i) = M i := by
  change linearPart (hI.wirePolynomial c.program (c.outputs i)) = M i
  rw [Internal.wirePolynomial_output hI c M hc, Internal.linearPart_linearPolynomial]

end Algebraic.Cutwidth.MultiOutput.Polynomial

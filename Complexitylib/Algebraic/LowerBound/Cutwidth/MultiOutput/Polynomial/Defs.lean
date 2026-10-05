/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Circuit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Linear.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Polynomial interpretations and their formal wire values

An interpretation is polynomial when each gate operation agrees everywhere with a
multivariate polynomial in its argument slots. The signature may contain arbitrarily
many operations and constants, with no degree bound. Formal substitution assigns a
polynomial to every original circuit wire. Its degree-one coefficient vector will
provide a local linear realization without changing the program graph.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Polynomial

variable {F : Type*} [CommSemiring F] {σ : Signature} {n s : ℕ}

/-- Every operation is represented by a polynomial in its argument slots. -/
def IsPolynomial (I : Interpretation σ F) : Prop :=
  ∀ op, ∃ q : MvPolynomial (Fin (σ.Arity op)) F,
    ∀ x, I op x = MvPolynomial.eval x q

/-- The signature containing every finite-arity polynomial over the coefficient field. -/
def signature (F : Type*) [CommSemiring F] : Signature where
  Op := (arity : ℕ) × MvPolynomial (Fin arity) F
  Arity := Sigma.fst

/-- A polynomial operation evaluates its displayed polynomial. -/
noncomputable def interpretation (F : Type*) [CommSemiring F] :
    Interpretation (signature F) F :=
  fun op x => MvPolynomial.eval x op.2

/-- The full polynomial signature has a polynomial interpretation. -/
theorem isPolynomial_interpretation : IsPolynomial (interpretation F) :=
  fun op => ⟨op.2, fun _ => rfl⟩

/-- A chosen polynomial representing one operation. -/
noncomputable def IsPolynomial.gatePolynomial {I : Interpretation σ F}
    (hI : IsPolynomial I) (op : σ.Op) : MvPolynomial (Fin (σ.Arity op)) F :=
  (hI op).choose

/-- Formal substitution of wire polynomials into each gate polynomial. -/
noncomputable def IsPolynomial.formalInterpretation {I : Interpretation σ F}
    (hI : IsPolynomial I) (n : ℕ) : Interpretation σ (MvPolynomial (Fin n) F) :=
  fun op args => MvPolynomial.aeval args (hI.gatePolynomial op)

/-- The polynomial carried by each original input or gate wire. -/
noncomputable def IsPolynomial.wirePolynomial {I : Interpretation σ F}
    (hI : IsPolynomial I) (p : Program σ n s) :
    Wire n s → MvPolynomial (Fin n) F :=
  p.trace (hI.formalInterpretation n) MvPolynomial.X

/-- The linear coefficient vector, computed by formal differentiation at zero. -/
noncomputable def linearPart {F : Type*} [CommRing F]
    (q : MvPolynomial (Fin n) F) : Fin n → F :=
  fun i => MvPolynomial.eval (fun _ => 0) (MvPolynomial.pderiv i q)

/-- The formal linear polynomial with the given coefficient row. -/
noncomputable def linearPolynomial (row : Fin n → F) : MvPolynomial (Fin n) F :=
  ∑ i, MvPolynomial.C (row i) * MvPolynomial.X i

end Algebraic.Cutwidth.MultiOutput.Polynomial

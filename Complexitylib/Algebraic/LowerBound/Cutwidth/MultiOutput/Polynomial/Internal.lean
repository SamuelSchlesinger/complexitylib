/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Defs
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Formal linearization of polynomial gate computations

The derivative-at-zero vector of a substitution lies in the span of the substituted
polynomials' vectors. Polynomial induction proves this directly using the product rule.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Polynomial.Internal

open Matrix

variable {F : Type*} [Field F] {σ : Signature} {n s m : ℕ}

theorem linearPart_C (a : F) : linearPart (n := n) (MvPolynomial.C a) = 0 := by
  ext i
  simp [linearPart]

theorem linearPart_add (p q : MvPolynomial (Fin n) F) :
    linearPart (p + q) = linearPart p + linearPart q := by
  ext i
  simp [linearPart]

theorem linearPart_mul (p q : MvPolynomial (Fin n) F) :
    linearPart (p * q) =
      MvPolynomial.eval (fun _ => 0) q • linearPart p +
        MvPolynomial.eval (fun _ => 0) p • linearPart q := by
  ext i
  simp [linearPart, add_comm]

theorem linearPart_X (j : Fin n) :
    linearPart (MvPolynomial.X j : MvPolynomial (Fin n) F) = Pi.single j 1 := by
  ext i
  by_cases h : i = j
  · subst i
    simp [linearPart]
  · simp [linearPart, MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]

theorem linearPart_aeval_mem_span {arity : ℕ}
    (args : Fin arity → MvPolynomial (Fin n) F) (q : MvPolynomial (Fin arity) F) :
    linearPart (MvPolynomial.aeval args q) ∈
      Submodule.span F (Set.range fun i => linearPart (args i)) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simpa only [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, linearPart_C] using
      (Submodule.zero_mem (Submodule.span F (Set.range fun i => linearPart (args i))))
  | add p q hp hq =>
    simpa only [map_add, linearPart_add] using Submodule.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X, linearPart_mul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hp)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem gatePolynomial_eval {I : Interpretation σ F} (hI : IsPolynomial I)
    (op : σ.Op) (x : Fin (σ.Arity op) → F) :
    MvPolynomial.eval x (hI.gatePolynomial op) = I op x :=
  ((hI op).choose_spec x).symm

/-- Evaluating formal wire polynomials commutes with every original gate operation. -/
def evaluationHom {I : Interpretation σ F} (hI : IsPolynomial I) (x : Fin n → F) :
    Cslib.Circuits.Homomorphism (hI.formalInterpretation n) I where
  map := MvPolynomial.eval x
  homomorphic := by
    intro op args
    change MvPolynomial.eval x (MvPolynomial.aeval args (hI.gatePolynomial op)) = _
    rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply,
      MvPolynomial.aeval_eq_eval, gatePolynomial_eval]
    rfl

theorem wirePolynomial_eval {I : Interpretation σ F} (hI : IsPolynomial I)
    (p : Program σ n s) (x : Fin n → F) (w : Wire n s) :
    MvPolynomial.eval x (hI.wirePolynomial p w) = p.trace I x w := by
  have h := congrFun (p.map_trace (evaluationHom hI x) MvPolynomial.X) w
  simpa only [evaluationHom, IsPolynomial.wirePolynomial, Function.comp_def,
    MvPolynomial.eval_X] using h

theorem linearPart_wirePolynomial_gate {I : Interpretation σ F} (hI : IsPolynomial I)
    (p : Program σ n s) (g : Fin s) :
    linearPart (hI.wirePolynomial p (.gate g)) ∈ Submodule.span F
      (Set.range fun i => linearPart (hI.wirePolynomial p ((p.lines g).wires i))) := by
  have h := p.lines_eval (hI.formalInterpretation n) MvPolynomial.X g
  change MvPolynomial.aeval (hI.wirePolynomial p ∘ (p.lines g).wires)
    (hI.gatePolynomial (p.lines g).op) = hI.wirePolynomial p (.gate g) at h
  rw [← h]
  exact linearPart_aeval_mem_span _ _

theorem eval_linearPolynomial (row x : Fin n → F) :
    MvPolynomial.eval x (linearPolynomial row) = dotProduct row x := by
  simp [linearPolynomial, dotProduct]

theorem linearPart_linearPolynomial (row : Fin n → F) :
    linearPart (linearPolynomial row) = row := by
  ext i
  simp [linearPart, linearPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]

theorem wirePolynomial_output [Infinite F] {I : Interpretation σ F}
    (hI : IsPolynomial I) (c : Circuit σ n m) (M : Matrix (Fin m) (Fin n) F)
    (hc : c.Computes I fun x => M *ᵥ x) (i : Fin m) :
    hI.wirePolynomial c.program (c.outputs i) = linearPolynomial (M i) := by
  apply MvPolynomial.funext
  intro x
  rw [wirePolynomial_eval, eval_linearPolynomial]
  exact congrFun (hc x) i

end Algebraic.Cutwidth.MultiOutput.Polynomial.Internal

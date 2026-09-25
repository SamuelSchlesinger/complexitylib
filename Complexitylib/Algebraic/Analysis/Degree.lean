/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation
public import Mathlib.Data.Fintype.BigOperators

/-!
# Syntactic degree propagation

A degree policy classifies each operation as constant, maximum-like (such as
addition), or sum-like (such as multiplication). Inputs start in degree one.
The resulting interpretation is a compositional abstract analysis; relating it
to semantic polynomial degree only requires a separate soundness proof for the
chosen concrete signature.
-/

@[expose] public section

namespace Algebraic

/-- Local rule used to propagate a degree bound through an operation. -/
inductive DegreeMode
  | constant
  | maximum
  | sum
  deriving DecidableEq

/-- Evaluate a local degree-propagation rule. -/
def DegreeMode.eval
    (mode : DegreeMode)
    {arity : Nat}
    (input : Fin arity → Nat) : Nat :=
  match mode with
  | .constant => 0
  | .maximum =>
      Fin.foldl arity (fun degree argument => max degree (input argument)) 0
  | .sum => ∑ argument, input argument

/-- Degree interpretation induced by a local rule for every operation. -/
def _root_.Cslib.Circuits.Signature.degreeInterpretation
    (σ : Signature)
    (mode : σ.Op → DegreeMode) : Interpretation σ Nat :=
  fun op input => (mode op).eval input

export Cslib.Circuits (Signature.degreeInterpretation)

/-- Degree profile of a circuit when every original input has degree one. -/
def _root_.Cslib.Circuits.Circuit.degreeProfile
    (circuit : Circuit σ n m)
    (mode : σ.Op → DegreeMode) : Fin m → Nat :=
  circuit.eval (σ.degreeInterpretation mode) (fun _ => 1)

export Cslib.Circuits (Circuit.degreeProfile)

/-- Translation gives exact degree propagation using the derived source
operation rules implemented by the target gadgets. -/
theorem Translation.compile_degreeProfile
    (translation : Translation σ τ)
    (circuit : Circuit σ n m)
    (targetMode : τ.Op → DegreeMode) :
    (translation.compile circuit).degreeProfile targetMode =
      circuit.eval
        (translation.pull (τ.degreeInterpretation targetMode))
        (fun _ => 1) := by
  exact translation.compile_eval circuit (τ.degreeInterpretation targetMode)
    (fun _ => 1)

end Algebraic

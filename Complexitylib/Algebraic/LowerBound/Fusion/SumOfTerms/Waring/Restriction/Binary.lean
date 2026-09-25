/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Power
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Restriction
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring.Translation.Binary

/-!
# Critical-layer restriction for binary-compiled Waring circuits

Binary powering visits a sparse sequence of exponents rather than every
intermediate exponent.  The generic arithmetic power-atom theorem identifies
each emitted multiplication as a bounded power; this module interprets that
fact in the Waring critical layer.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Waring
namespace Restriction
namespace Binary

noncomputable section

open Arithmetic.Interaction.Polynomial.Catalecticant

variable {K : Type}

/-- Any bounded power of a Waring linear form is either outside the critical
degree or is itself one charged Waring term. -/
theorem criticalLayerOrPower_linearForm_pow
    [Field K]
    (n : Nat)
    (term : Term K n)
    (exponent : Nat)
    (_bounded : exponent ≤ 2 * n) :
    CriticalLayerOrPower n (linearForm term ^ exponent) := by
  by_cases full : exponent = 2 * n
  · let powerTerm : Term K n :=
      { scale := 1
        coefficients := term.coefficients }
    have powerValue : linearForm term ^ exponent = termValue powerTerm := by
      rw [full]
      simp [termValue, powerTerm, linearForm]
    rw [powerValue]
    exact criticalLayerOrPower_termValue powerTerm
  · apply criticalLayerOrPower_of_isHomogeneous_ne n exponent
    · simpa using
        (Algebraic.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Degree.linearForm_isHomogeneous
          term).pow exponent
    · exact full

/-- Every multiplication atom in a binary power circuit is a bounded power
of the input linear form, hence satisfies the critical-layer restriction. -/
theorem powerCircuit_multiplicationAtomProperty
    [Field K]
    (n : Nat)
    (term : Term K n)
    (exponent : Nat)
    (bounded : exponent ≤ 2 * n)
    (atom : Atom (Algebraic.Arithmetic.signature K)
      (MvPolynomial (Fin (2 * n)) K))
    (present : atom ∈ circuitAtoms
      (Algebraic.Arithmetic.Power.binaryCircuit (K := K) exponent)
      (Algebraic.Arithmetic.interpretation
        (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K))
      (fun _ : Fin 1 ↦ linearForm term)) :
    MultiplicationAtomProperty n atom := by
  intro arguments atomEqual
  obtain ⟨power, powerLe, result⟩ :=
    Algebraic.Fusion.Arithmetic.Power.binaryCircuit_multiplicationPowerAtMost
      (MvPolynomial.C : K → MvPolynomial (Fin (2 * n)) K)
      MvPolynomial.C_1 (fun _ : Fin 1 ↦ linearForm term) exponent atom
      present arguments atomEqual
  rw [result]
  exact criticalLayerOrPower_linearForm_pow n term power
    (powerLe.trans bounded)

end
end Binary
end Restriction
end Waring
end SumOfTerms
end Fusion
end Algebraic

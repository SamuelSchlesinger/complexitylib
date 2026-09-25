/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic.Power
public import Complexitylib.Algebraic.LowerBound.Fusion.Framework

/-!
# Fusion atoms of binary power circuits

The implementation-independent semantic contract needed by local Fusion
arguments: every multiplication atom emitted while computing `x^d` produces
`x^e` for some `e ≤ d`.  Polynomial degree arguments are downstream
instances of this generic arithmetic fact.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Power

variable {K R : Type}

/-- A multiplication atom's result is a bounded natural power of `base`. -/
def MultiplicationPowerAtMost
    [Mul R]
    [Pow R Nat]
    (base : R)
    (bound : Nat)
    (atom : Atom (Algebraic.Arithmetic.signature K) R) : Prop :=
  ∀ arguments : Fin 2 → R,
    atom = (⟨.mul, arguments⟩ : Atom
      (Algebraic.Arithmetic.signature K) R) →
    ∃ exponent, exponent ≤ bound ∧
      arguments (0 : Fin 2) * arguments (1 : Fin 2) = base ^ exponent

/-- Every multiplication atom of the shared binary-power circuit computes a
power bounded by the requested exponent. -/
theorem binaryCircuit_multiplicationPowerAtMost
    [Semiring R]
    [One K]
    (constant : K → R)
    (mapsOne : constant 1 = 1)
    (input : Fin 1 → R)
    (exponent : Nat)
    (atom : Atom (Algebraic.Arithmetic.signature K) R)
    (present : atom ∈ circuitAtoms
      (Algebraic.Arithmetic.Power.binaryCircuit (K := K) exponent).2
      (Algebraic.Arithmetic.interpretation constant) input) :
    MultiplicationPowerAtMost (K := K) (input 0) exponent atom := by
  induction exponent using Nat.binaryRecFromOne generalizing atom with
  | zero =>
      intro arguments atomEqual
      rw [atomEqual,
        Algebraic.Arithmetic.Power.binaryCircuit_zero] at present
      simp [circuitAtoms, Algebraic.Arithmetic.Expression.circuit,
        Algebraic.Arithmetic.Expression.compile, lineAtom] at present
      have operationEqual := congrArg Atom.op present
      contradiction
  | one =>
      intro arguments atomEqual
      rw [atomEqual,
        Algebraic.Arithmetic.Power.binaryCircuit_one] at present
      simp [circuitAtoms, Circuit.id] at present
  | bit bit prior nonzero inductionHypothesis =>
      rw [Algebraic.Arithmetic.Power.binaryCircuit_bit bit prior nonzero]
        at present
      cases bit with
      | false =>
          change atom ∈ circuitAtoms
            (Algebraic.Arithmetic.Power.squareCircuit
              (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2)
            _ _ at present
          simp only [circuitAtoms, Algebraic.Arithmetic.Power.squareCircuit,
            programAtoms_gate] at present
          rcases List.mem_append.mp present with inPrior | inSquare
          · intro arguments atomEqual
            obtain ⟨power, powerLe, result⟩ :=
              inductionHypothesis atom inPrior arguments atomEqual
            exact ⟨power, powerLe.trans (by
              simp only [Nat.bit_false_apply]
              omega), result⟩
          · intro arguments atomEqual
            rw [atomEqual] at inSquare
            have atomEq := List.mem_singleton.mp inSquare
            have resultEq := congrArg
              (fun candidate : Atom (Algebraic.Arithmetic.signature K) R ↦
                candidate.result
                  (Algebraic.Arithmetic.interpretation constant))
              atomEq
            refine ⟨prior + prior, ?_, ?_⟩
            · simp only [Nat.bit_false_apply]
              omega
            · change
                ((⟨.mul, arguments⟩ : Atom
                  (Algebraic.Arithmetic.signature K) R).result
                    (Algebraic.Arithmetic.interpretation constant)) = _
              rw [resultEq]
              change
                ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                    (Algebraic.Arithmetic.interpretation constant) input 0) *
                  ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                    (Algebraic.Arithmetic.interpretation constant) input 0) = _
              rw [Algebraic.Arithmetic.Power.binaryCircuit_eval constant mapsOne,
                ← pow_add]
      | true =>
          change atom ∈ circuitAtoms
            (Algebraic.Arithmetic.Power.multiplyInputCircuit
              (Algebraic.Arithmetic.Power.squareCircuit
                (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2))
            _ _ at present
          simp only [circuitAtoms,
            Algebraic.Arithmetic.Power.multiplyInputCircuit,
            programAtoms_gate] at present
          rcases List.mem_append.mp present with inSquareCircuit | inOdd
          · change atom ∈ circuitAtoms
              (Algebraic.Arithmetic.Power.squareCircuit
                (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2)
              _ _ at inSquareCircuit
            simp only [circuitAtoms,
              Algebraic.Arithmetic.Power.squareCircuit,
              programAtoms_gate] at inSquareCircuit
            rcases List.mem_append.mp inSquareCircuit with inPrior | inSquare
            · intro arguments atomEqual
              obtain ⟨power, powerLe, result⟩ :=
                inductionHypothesis atom inPrior arguments atomEqual
              exact ⟨power, powerLe.trans (by
                simp only [Nat.bit_true_apply]
                omega), result⟩
            · intro arguments atomEqual
              rw [atomEqual] at inSquare
              have atomEq := List.mem_singleton.mp inSquare
              have resultEq := congrArg
                (fun candidate : Atom (Algebraic.Arithmetic.signature K) R ↦
                  candidate.result
                    (Algebraic.Arithmetic.interpretation constant))
                atomEq
              refine ⟨prior + prior, ?_, ?_⟩
              · simp only [Nat.bit_true_apply]
                omega
              · change
                  ((⟨.mul, arguments⟩ : Atom
                    (Algebraic.Arithmetic.signature K) R).result
                      (Algebraic.Arithmetic.interpretation constant)) = _
                rw [resultEq]
                change
                  ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                      (Algebraic.Arithmetic.interpretation constant) input 0) *
                    ((Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2.eval
                      (Algebraic.Arithmetic.interpretation constant) input 0) = _
                rw [Algebraic.Arithmetic.Power.binaryCircuit_eval constant mapsOne,
                  ← pow_add]
          · intro arguments atomEqual
            rw [atomEqual] at inOdd
            have atomEq := List.mem_singleton.mp inOdd
            have resultEq := congrArg
              (fun candidate : Atom (Algebraic.Arithmetic.signature K) R ↦
                candidate.result
                  (Algebraic.Arithmetic.interpretation constant))
              atomEq
            refine ⟨prior + prior + 1, ?_, ?_⟩
            · simp only [Nat.bit_true_apply]
              omega
            · change
                ((⟨.mul, arguments⟩ : Atom
                  (Algebraic.Arithmetic.signature K) R).result
                    (Algebraic.Arithmetic.interpretation constant)) = _
              rw [resultEq]
              change
                (Algebraic.Arithmetic.Power.squareCircuit
                    (Algebraic.Arithmetic.Power.binaryCircuit (K := K) prior).2).eval
                    (Algebraic.Arithmetic.interpretation constant) input 0 *
                  input 0 = _
              rw [Algebraic.Arithmetic.Power.squareCircuit_eval,
                Algebraic.Arithmetic.Power.binaryCircuit_eval constant mapsOne,
                ← pow_add, ← pow_succ]

end Power
end Arithmetic
end Fusion
end Algebraic

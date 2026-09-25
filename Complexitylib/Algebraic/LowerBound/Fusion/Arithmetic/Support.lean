/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.FiniteSupport
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.BoundedFailure

/-!
# Finite-support fusion for arbitrary-depth monotone arithmetic circuits

This module interprets arithmetic circuits directly on finite monomial
supports.  Addition is union and multiplication is pairwise monomial product,
so multiplication gates may be nested to arbitrary depth.

Witnesses are target monomials absent from the generators and named constants.
Addition preserves absence.  A multiplication can fail only on target
monomials appearing in its product support, which is bounded by the product of
the two input-support cardinalities.

The final theorem is deliberately circuit-local: if every multiplication gate
actually occurring in a constructing circuit has input supports of size at
most `width`, then the circuit needs at least
`ceil(target.card / (width * width))` multiplications.  This is a restricted
monotone-support result, not a lower bound for unrestricted arithmetic
circuits with cancellation.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Support

/-- Construct a target support from the supplied input supports. -/
abbrev problem
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M) : Problem (FiniteSupport M) where
  inputCount := n
  inputs := inputs
  target := ⟨target⟩

/-- Fusion model recording which target monomials remain absent. -/
abbrev model
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials) :
    Model (Algebraic.Arithmetic.multiplicationCost (K := K))
      (Algebraic.Arithmetic.interpretation constantSupport)
      (problem inputs target) where
  Witness := ↥target
  reference _ _ := True
  observed witness support := witness.1 ∉ support.monomials
  input_sound := by
    intro witness input _
    exact inputAvoid witness input
  target_reference := by
    intro _
    trivial
  target_not_observed := by
    intro witness avoids
    exact avoids witness.2

noncomputable instance witnessFintype
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials) :
    Fintype (model constantSupport inputs target inputAvoid).Witness := by
  change Fintype ↥target
  infer_instance

theorem witness_card
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials) :
    Fintype.card (model constantSupport inputs target inputAvoid).Witness =
      target.card := by
  change Fintype.card ↥target = target.card
  simp

/-- Union preserves absence of every target monomial. -/
theorem add_preserved
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (arguments : Fin 2 → FiniteSupport M)
    (witness : (model constantSupport inputs target inputAvoid).Witness) :
    (⟨.add, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K) (FiniteSupport M)).PreservedBy
        (model constantSupport inputs target inputAvoid) witness := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result,
    Algebraic.Arithmetic.interpretation, true_implies]
  intro argumentsAvoid
  simp only [FiniteSupport.mem_add, not_or]
  exact ⟨argumentsAvoid (0 : Fin 2), argumentsAvoid (1 : Fin 2)⟩

/-- Named constants preserve absence when their supports avoid the target. -/
theorem constant_preserved
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (constantAvoid : ∀ witness : ↥target, ∀ scalar,
      witness.1 ∉ (constantSupport scalar).monomials)
    (scalar : K)
    (arguments : Fin (Algebraic.Arithmetic.arity (.constant scalar)) →
      FiniteSupport M)
    (witness : (model constantSupport inputs target inputAvoid).Witness) :
    (⟨.constant scalar, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K) (FiniteSupport M)).PreservedBy
        (model constantSupport inputs target inputAvoid) witness := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result,
    Algebraic.Arithmetic.interpretation, true_implies]
  intro _
  exact constantAvoid witness scalar

/-- Failure of a multiplication implies that its result support contains the
failed target monomial. -/
theorem mem_mul_of_not_preserved
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (arguments : Fin 2 → FiniteSupport M)
    (witness : (model constantSupport inputs target inputAvoid).Witness)
    (failure : ¬
      (⟨.mul, arguments⟩ :
        Atom (Algebraic.Arithmetic.signature K)
          (FiniteSupport M)).PreservedBy
            (model constantSupport inputs target inputAvoid) witness) :
    witness.1 ∈
      (arguments (0 : Fin 2) * arguments (1 : Fin 2)).monomials := by
  classical
  simp only [Atom.PreservedBy, Model.Sound, Atom.result,
    Algebraic.Arithmetic.interpretation, true_implies] at failure
  exact (Classical.not_imp.mp failure).2 |> Classical.not_not.mp

/-- A multiplication fails on no more witnesses than the cardinality of its
pairwise product support. -/
theorem mul_failure_card_le_productSupport
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (arguments : Fin 2 → FiniteSupport M) :
    ((⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K)
        (FiniteSupport M)).failures
          (model constantSupport inputs target inputAvoid)).card ≤
      (arguments (0 : Fin 2) * arguments (1 : Fin 2)).monomials.card := by
  classical
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro witness present
    have failure : ¬
        (⟨.mul, arguments⟩ :
          Atom (Algebraic.Arithmetic.signature K)
            (FiniteSupport M)).PreservedBy
              (model constantSupport inputs target inputAvoid) witness := by
      have presentFinset : witness ∈
          ((⟨.mul, arguments⟩ :
            Atom (Algebraic.Arithmetic.signature K)
              (FiniteSupport M)).failures
                (model constantSupport inputs target inputAvoid)) := present
      exact (Atom.mem_failures
        (⟨.mul, arguments⟩ :
          Atom (Algebraic.Arithmetic.signature K) (FiniteSupport M))
        (model constantSupport inputs target inputAvoid) witness).mp
          presentFinset
    exact mem_mul_of_not_preserved constantSupport inputs target inputAvoid
      arguments witness failure
  · intro left _ right _ equal
    exact Subtype.ext equal

/-- The elementary product-width bound on failed target witnesses. -/
theorem mul_failure_card_le
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (arguments : Fin 2 → FiniteSupport M) :
    ((⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K)
        (FiniteSupport M)).failures
          (model constantSupport inputs target inputAvoid)).card ≤
      (arguments (0 : Fin 2)).monomials.card *
        (arguments (1 : Fin 2)).monomials.card :=
  (mul_failure_card_le_productSupport constantSupport inputs target
    inputAvoid arguments).trans
      (FiniteSupport.card_mul_le _ _)

/-- Every multiplication atom in a list receives supports of cardinality at
most `width`. -/
def MultiplicationWidthAtMost
    (atoms : List (Atom (Algebraic.Arithmetic.signature K)
      (FiniteSupport M)))
    (width : Nat) : Prop :=
  ∀ (arguments : Fin 2 → FiniteSupport M),
    (⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K) (FiniteSupport M)) ∈ atoms →
    ∀ input, (arguments input).monomials.card ≤ width

/-- A support-width promise gives the required local failure estimate on the
atoms that actually occur. -/
theorem local_failure_card_le
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (constantAvoid : ∀ witness : ↥target, ∀ scalar,
      witness.1 ∉ (constantSupport scalar).monomials)
    (atoms : List (Atom (Algebraic.Arithmetic.signature K)
      (FiniteSupport M)))
    (width : Nat)
    (widthBound : MultiplicationWidthAtMost atoms width) :
    ∀ atom ∈ atoms,
      (atom.failures
        (model constantSupport inputs target inputAvoid)).card ≤
      (width * width) *
        atom.cost (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  classical
  intro atom present
  cases atom with
  | mk op arguments =>
      cases op with
      | add =>
          change Fin 2 → FiniteSupport M at arguments
          have noFailures :
              ((⟨.add, arguments⟩ :
                Atom (Algebraic.Arithmetic.signature K)
                  (FiniteSupport M)).failures
                    (model constantSupport inputs target inputAvoid)) = ∅ := by
            ext witness
            constructor
            · intro failed
              rw [Atom.mem_failures] at failed
              exact (failed (add_preserved constantSupport inputs target
                inputAvoid arguments witness)).elim
            · simp
          rw [noFailures]
          simp [Atom.cost]
      | mul =>
          change Fin 2 → FiniteSupport M at arguments
          calc
            ((⟨.mul, arguments⟩ :
                Atom (Algebraic.Arithmetic.signature K)
                  (FiniteSupport M)).failures
                    (model constantSupport inputs target inputAvoid)).card ≤
                (arguments (0 : Fin 2)).monomials.card *
                  (arguments (1 : Fin 2)).monomials.card :=
              mul_failure_card_le constantSupport inputs target inputAvoid
                arguments
            _ ≤ width * width := Nat.mul_le_mul
              (widthBound arguments present (0 : Fin 2))
              (widthBound arguments present (1 : Fin 2))
            _ = (width * width) *
                (⟨.mul, arguments⟩ :
                  Atom (Algebraic.Arithmetic.signature K)
                    (FiniteSupport M)).cost
                      (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
              simp [Atom.cost]
      | constant scalar =>
          have noFailures :
              ((⟨.constant scalar, arguments⟩ :
                Atom (Algebraic.Arithmetic.signature K)
                  (FiniteSupport M)).failures
                    (model constantSupport inputs target inputAvoid)) = ∅ := by
            ext witness
            constructor
            · intro failed
              rw [Atom.mem_failures] at failed
              exact (failed (constant_preserved constantSupport inputs target
                inputAvoid constantAvoid scalar arguments witness)).elim
            · simp
          rw [noFailures]
          simp [Atom.cost]

/-- Arbitrary-depth monotone support circuits of multiplication-input width
`width` need at least `ceil(target.card / width^2)` multiplication gates. -/
theorem circuit_multiplication_lowerBound
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (constantAvoid : ∀ witness : ↥target, ∀ scalar,
      witness.1 ∉ (constantSupport scalar).monomials)
    (width : Nat)
    (positive : 0 < width)
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n 1)
    (constructs : (problem inputs target).Constructs circuit
      (Algebraic.Arithmetic.interpretation constantSupport))
    (widthBound : MultiplicationWidthAtMost
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation constantSupport) inputs)
      width) :
    target.card ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  let supportModel := model constantSupport inputs target inputAvoid
  have capacityPositive : 0 < width * width := Nat.mul_pos positive positive
  simpa [supportModel] using
    supportModel.ceilDiv_witnessCard_le_circuitCost_of_local
      (width * width) capacityPositive circuit constructs
      (local_failure_card_le constantSupport inputs target inputAvoid
        constantAvoid _ width widthBound)

/-- In the singleton-width case, every target monomial costs a distinct
multiplication gate. -/
theorem circuit_multiplication_lowerBound_of_singletonWidth
    [DecidableEq M]
    [Mul M]
    (constantSupport : K → FiniteSupport M)
    (inputs : Fin n → FiniteSupport M)
    (target : Finset M)
    (inputAvoid : ∀ witness : ↥target, ∀ input,
      witness.1 ∉ (inputs input).monomials)
    (constantAvoid : ∀ witness : ↥target, ∀ scalar,
      witness.1 ∉ (constantSupport scalar).monomials)
    (circuit : Circuit (Algebraic.Arithmetic.signature K) n 1)
    (constructs : (problem inputs target).Constructs circuit
      (Algebraic.Arithmetic.interpretation constantSupport))
    (widthBound : MultiplicationWidthAtMost
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation constantSupport) inputs)
      1) :
    target.card ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  simpa using circuit_multiplication_lowerBound constantSupport inputs target
    inputAvoid constantAvoid 1 (by decide) circuit constructs widthBound

end Support
end Arithmetic
end Fusion
end Algebraic

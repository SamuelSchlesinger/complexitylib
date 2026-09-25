/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Counting
public import Complexitylib.Algebraic.Basis.SumOfTerms
public import Complexitylib.Algebraic.Basis.FiniteSupport

/-!
# Coverage fusion for finite monomial supports

This is the support-theoretic counterpart of the rank certificate.  Semantic
values are finite sets of monomials, addition is union, and a charged term
contributes a prescribed finite support.  A witness is one monomial in the
target support.  Union preserves non-membership, while a term fails precisely
on the target monomials it covers.

If every allowed term covers at most `r` target monomials, every circuit whose
union is the target uses at least `ceil(target.card / r)` charged terms.  The
local coverage estimate can come from separated monomials, rectangle bounds,
or other monotone-support arguments.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace SumOfTerms
namespace Coverage

/-- Compatibility name for the reusable finite-support carrier. -/
abbrev FiniteSupport (M : Type u) := Algebraic.FiniteSupport M

@[simp] theorem monomials_add
    [DecidableEq M]
    (left right : FiniteSupport M) :
    (left + right).monomials = left.monomials ∪ right.monomials :=
  Algebraic.FiniteSupport.monomials_add left right

theorem mem_add
    [DecidableEq M]
    (monomial : M)
    (left right : FiniteSupport M) :
    monomial ∈ (left + right).monomials ↔
      monomial ∈ left.monomials ∨ monomial ∈ right.monomials := by
  exact Algebraic.FiniteSupport.mem_add monomial left right

/-- Construct a target support from charged terms, with no free inputs. -/
abbrev problem
    (target : Finset M) : Problem (FiniteSupport M) where
  inputCount := 0
  inputs := fun input => Fin.elim0 input
  target := ⟨target⟩

/-- Fusion model whose observations say that a target monomial remains
uncovered. -/
abbrev model
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M) :
    Model (Algebraic.SumOfTerms.termCost (T := T))
      (Algebraic.SumOfTerms.interpretation termSupport) (problem target) where
  Witness := ↥target
  reference _ _ := True
  observed witness support := witness.1 ∉ support.monomials
  input_sound := by
    intro _ input
    exact Fin.elim0 input
  target_reference := by
    intro _
    trivial
  target_not_observed := by
    intro witness avoids
    exact avoids witness.2

noncomputable instance witnessFintype
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M) :
    Fintype (model target termSupport).Witness := by
  unfold model
  infer_instance

theorem witness_card
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M) :
    Fintype.card (model target termSupport).Witness = target.card := by
  change Fintype.card ↥target = target.card
  simp

/-- Union preserves non-membership of every target monomial. -/
theorem add_preserved
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M)
    (arguments : Fin 2 → FiniteSupport M)
    (witness : (model target termSupport).Witness) :
    (⟨.add, arguments⟩ :
      Atom (Algebraic.SumOfTerms.signature T) (FiniteSupport M)).PreservedBy
        (model target termSupport) witness := by
  simp only [Atom.PreservedBy, Model.Sound, Atom.result,
    Algebraic.SumOfTerms.interpretation, true_implies]
  intro argumentsAvoid
  simp only [mem_add, not_or]
  exact ⟨argumentsAvoid (0 : Fin 2), argumentsAvoid (1 : Fin 2)⟩

/-- A term preserves a witness exactly when it does not cover that monomial. -/
theorem term_preserved_iff
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M)
    (term : T)
    (arguments : Fin (Algebraic.SumOfTerms.arity (.term term)) →
      FiniteSupport M)
    (witness : (model target termSupport).Witness) :
    (⟨.term term, arguments⟩ :
      Atom (Algebraic.SumOfTerms.signature T) (FiniteSupport M)).PreservedBy
        (model target termSupport) witness ↔
      witness.1 ∉ (termSupport term).monomials := by
  simp [Atom.PreservedBy, Model.Sound, Atom.result,
    Algebraic.SumOfTerms.interpretation]

/-- Target witnesses covered by one dictionary term. -/
noncomputable def coveredWitnesses
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M)
    (term : T) : Finset ↥target := by
  classical
  exact target.attach.filter fun witness =>
    witness.1 ∈ (termSupport term).monomials

@[simp] theorem mem_coveredWitnesses
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M)
    (term : T)
    (witness : ↥target) :
    witness ∈ coveredWitnesses target termSupport term ↔
      witness.1 ∈ (termSupport term).monomials := by
  classical
  simp [coveredWitnesses]

/-- A local bound on how many target monomials one term can cover. -/
structure Bound
    [DecidableEq M]
    (target : Finset M)
    (termSupport : T → FiniteSupport M) where
  /-- Maximum target coverage of one term. -/
  capacity : Nat
  /-- The combinatorial coverage estimate for every allowed term. -/
  covered_card_le : ∀ term,
    (coveredWitnesses target termSupport term).card ≤ capacity

/-- Coverage bounds compile to the generic finite-witness failure bound. -/
noncomputable def Bound.failureBound
    [DecidableEq M]
    {target : Finset M}
    {termSupport : T → FiniteSupport M}
    (bound : Bound target termSupport) :
    FailureBound (model target termSupport) where
  capacity := bound.capacity
  failure_card_le := by
    classical
    intro atom
    cases atom with
    | mk op arguments =>
        cases op with
        | add =>
            change Fin 2 → FiniteSupport M at arguments
            have noFailures :
                ((⟨.add, arguments⟩ :
                  Atom (Algebraic.SumOfTerms.signature T)
                    (FiniteSupport M)).failures (model target termSupport)) = ∅ := by
              ext witness
              constructor
              · intro failed
                rw [Atom.mem_failures] at failed
                exact (failed
                  (add_preserved target termSupport arguments witness)).elim
              · simp
            rw [noFailures]
            simp [Atom.cost]
        | term term =>
            have failuresEqual :
                ((⟨.term term, arguments⟩ :
                  Atom (Algebraic.SumOfTerms.signature T)
                    (FiniteSupport M)).failures (model target termSupport)) =
                  coveredWitnesses target termSupport term := by
              ext witness
              rw [Atom.mem_failures,
                mem_coveredWitnesses target termSupport term witness]
              simp [term_preserved_iff target termSupport term arguments witness]
            rw [failuresEqual]
            simpa [Atom.cost] using bound.covered_card_le term

@[simp] theorem Bound.failureBound_capacity
    [DecidableEq M]
    {target : Finset M}
    {termSupport : T → FiniteSupport M}
    (bound : Bound target termSupport) :
    bound.failureBound.capacity = bound.capacity := rfl

/-- A positive coverage capacity gives the expected circuit lower bound. -/
theorem Bound.circuit_lowerBound
    [DecidableEq M]
    {target : Finset M}
    {termSupport : T → FiniteSupport M}
    (bound : Bound target termSupport)
    (positive : 0 < bound.capacity)
    (circuit : Circuit (Algebraic.SumOfTerms.signature T) 0 1)
    (constructs : (problem target).Constructs circuit
      (Algebraic.SumOfTerms.interpretation termSupport)) :
    target.card ⌈/⌉ bound.capacity ≤
      circuit.cost (Algebraic.SumOfTerms.termCost (T := T)) := by
  simpa using bound.failureBound.ceilDiv_witnessCard_le_circuitCost
    (by simpa using positive) circuit constructs

/-- The separated case: each term covers at most one target monomial. -/
theorem circuit_lowerBound_of_separated
    [DecidableEq M]
    {target : Finset M}
    {termSupport : T → FiniteSupport M}
    (separated : ∀ term,
      (coveredWitnesses target termSupport term).card ≤ 1)
    (circuit : Circuit (Algebraic.SumOfTerms.signature T) 0 1)
    (constructs : (problem target).Constructs circuit
      (Algebraic.SumOfTerms.interpretation termSupport)) :
    target.card ≤
      circuit.cost (Algebraic.SumOfTerms.termCost (T := T)) := by
  let bound : Bound target termSupport := {
    capacity := 1
    covered_card_le := separated
  }
  have positive : 0 < bound.capacity := by
    change 0 < 1
    exact Nat.zero_lt_succ 0
  simpa [bound] using bound.circuit_lowerBound positive circuit constructs

end Coverage
end SumOfTerms
end Fusion
end Algebraic

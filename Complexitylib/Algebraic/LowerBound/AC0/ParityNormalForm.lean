/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Parity
public import Complexitylib.Algebraic.LowerBound.AC0.Duality

/-!
# Normal-form width lower bounds for restricted parity

This module proves the final structural obstruction in the standard parity
lower-bound argument. If a DNF computes parity after a restriction with at
least one live variable, some term contains every live variable. Dually, if a
CNF computes that restricted parity, some clause contains every live variable.
Consequently either normal form has width at least the live count.

The proof uses sensitivity rather than counting formulas. Starting from an
input on which restricted parity has the relevant truth value, a witnessing
term or falsified clause must mention every live variable: otherwise flipping
an absent live variable would preserve the witness while changing parity.
This is uniform in the arity and contains no finite search.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Parity

/-- A Boolean function is parity up to a possible output negation. This is
the invariant preserved while following a chain of internal NOT gates. -/
def UpToNegation (candidate : ScalarFunction Bool n) : Prop :=
  candidate = function n ∨
    candidate = fun input => !(function n input)

/-- Parity itself is parity up to output negation. -/
theorem upToNegation_self : UpToNegation (function n) :=
  Or.inl rfl

/-- The parity-up-to-negation predicate is closed under output negation. -/
theorem UpToNegation.negate
    {candidate : ScalarFunction Bool n}
    (phase : UpToNegation candidate) :
    UpToNegation (fun input => !(candidate input)) := by
  rcases phase with computes | computes
  · right
    funext input
    rw [computes]
  · left
    funext input
    rw [computes]
    simp

/-- Output negation does not change whether a function is parity up to
negation. -/
@[simp] theorem upToNegation_negate_iff
    (candidate : ScalarFunction Bool n) :
    UpToNegation (fun input => !(candidate input)) ↔
      UpToNegation candidate := by
  constructor
  · intro phase
    have twice := phase.negate
    simpa only [Bool.not_not] using twice
  · exact UpToNegation.negate

/-- Restricted parity attains true whenever at least one selected coordinate
is live. -/
theorem exists_restrict_eq_true_of_live
    (rho : PartialAssignment n)
    (selected : Fin n)
    (live : selected ∈ rho.liveVariables) :
    ∃ input : Fin n → Bool,
      (function n).restrict rho input = true := by
  let input : Fin n → Bool := fun _ => false
  cases baseValue : (function n).restrict rho input with
  | true => exact ⟨input, baseValue⟩
  | false =>
      refine ⟨flip input selected, ?_⟩
      have changed := restrict_ne_flip_of_live rho selected live input
      cases flippedValue : (function n).restrict rho (flip input selected) with
      | false =>
          exfalso
          apply changed
          rw [flippedValue, baseValue]
      | true => rfl

/-- Restricted parity attains false whenever at least one selected coordinate
is live. -/
theorem exists_restrict_eq_false_of_live
    (rho : PartialAssignment n)
    (selected : Fin n)
    (live : selected ∈ rho.liveVariables) :
    ∃ input : Fin n → Bool,
      (function n).restrict rho input = false := by
  let input : Fin n → Bool := fun _ => false
  cases baseValue : (function n).restrict rho input with
  | false => exact ⟨input, baseValue⟩
  | true =>
      refine ⟨flip input selected, ?_⟩
      have changed := restrict_ne_flip_of_live rho selected live input
      cases flippedValue : (function n).restrict rho (flip input selected) with
      | false => rfl
      | true =>
          exfalso
          apply changed
          rw [flippedValue, baseValue]

end Parity

namespace DNF

/-- Every DNF computing nonconstant restricted parity contains a term whose
support covers all live variables. -/
theorem exists_term_covering_liveVariables_of_computes_parity
    (formula : DNF n)
    (rho : PartialAssignment n)
    (liveNonempty : rho.liveVariables.Nonempty)
    (computes : ∀ input,
      formula.eval input = (Parity.function n).restrict rho input) :
    ∃ term,
      term ∈ formula.terms ∧ rho.liveVariables ⊆ term.support := by
  obtain ⟨selected, selectedLive⟩ := liveNonempty
  obtain ⟨input, parityTrue⟩ :=
    Parity.exists_restrict_eq_true_of_live rho selected selectedLive
  have formulaTrue : formula.eval input = true :=
    (computes input).trans parityTrue
  obtain ⟨term, present, satisfied⟩ :=
    (DNF.eval_eq_true formula input).1 formulaTrue
  refine ⟨term, present, ?_⟩
  intro coordinate coordinateLive
  by_contra absent
  have flippedSatisfied :
      term.SatisfiedBy (Parity.flip input coordinate) := by
    intro index value requirement
    have indexPresent : index ∈ term.support := by
      rw [LiteralSet.mem_support]
      simp [requirement]
    have different : index ≠ coordinate := by
      intro equal
      subst index
      exact absent indexPresent
    rw [Parity.flip_other input coordinate index different]
    exact satisfied index value requirement
  have formulaFlipTrue :
      formula.eval (Parity.flip input coordinate) = true :=
    (DNF.eval_eq_true formula (Parity.flip input coordinate)).2
      ⟨term, present, flippedSatisfied⟩
  have parityFlipTrue :
      (Parity.function n).restrict rho (Parity.flip input coordinate) = true :=
    (computes (Parity.flip input coordinate)).symm.trans formulaFlipTrue
  exact Parity.restrict_ne_flip_of_live rho coordinate coordinateLive input
    (parityFlipTrue.trans parityTrue.symm)

/-- A bounded-width DNF computing restricted parity leaves no more live
variables than its width. -/
theorem liveCount_le_width_of_computes_parity
    (formula : DNF n)
    (rho : PartialAssignment n)
    (bound : Nat)
    (bounded : formula.WidthAtMost bound)
    (computes : ∀ input,
      formula.eval input = (Parity.function n).restrict rho input) :
    rho.liveCount ≤ bound := by
  by_cases noLive : rho.liveCount = 0
  · simp [noLive]
  · have liveNonempty : rho.liveVariables.Nonempty :=
      Finset.card_pos.mp (by
        simpa [PartialAssignment.liveCount] using Nat.pos_of_ne_zero noLive)
    obtain ⟨term, present, covers⟩ :=
      exists_term_covering_liveVariables_of_computes_parity
        formula rho liveNonempty computes
    calc
      rho.liveCount = rho.liveVariables.card := rfl
      _ ≤ term.support.card := Finset.card_le_card covers
      _ = term.width := rfl
      _ ≤ bound := bounded term present

end DNF

namespace CNF

/-- Every CNF computing nonconstant restricted parity contains a clause whose
support covers all live variables. -/
theorem exists_clause_covering_liveVariables_of_computes_parity
    (formula : CNF n)
    (rho : PartialAssignment n)
    (liveNonempty : rho.liveVariables.Nonempty)
    (computes : ∀ input,
      formula.eval input = (Parity.function n).restrict rho input) :
    ∃ clause,
      clause ∈ formula.clauses ∧ rho.liveVariables ⊆ clause.support := by
  obtain ⟨selected, selectedLive⟩ := liveNonempty
  obtain ⟨input, parityFalse⟩ :=
    Parity.exists_restrict_eq_false_of_live rho selected selectedLive
  have formulaFalse : formula.eval input = false :=
    (computes input).trans parityFalse
  change formula.clauses.all (fun clause => Clause.eval clause input) =
    false at formulaFalse
  obtain ⟨clause, present, clauseFalse⟩ :=
    List.all_eq_false.mp formulaFalse
  refine ⟨clause, present, ?_⟩
  intro coordinate coordinateLive
  by_contra absent
  have changed :=
    Parity.restrict_ne_flip_of_live rho coordinate coordinateLive input
  have parityFlipTrue :
      (Parity.function n).restrict rho (Parity.flip input coordinate) = true := by
    cases flippedValue :
        (Parity.function n).restrict rho (Parity.flip input coordinate) with
    | false =>
        exfalso
        apply changed
        rw [flippedValue, parityFalse]
    | true => rfl
  have formulaFlipTrue :
      formula.eval (Parity.flip input coordinate) = true :=
    (computes (Parity.flip input coordinate)).trans parityFlipTrue
  have clauseSatisfied :
      clause.SatisfiedBy (Parity.flip input coordinate) :=
    (CNF.eval_eq_true formula (Parity.flip input coordinate)).1
      formulaFlipTrue clause present
  obtain ⟨index, value, requirement, flippedValue⟩ := clauseSatisfied
  have indexPresent : index ∈ clause.support := by
    rw [LiteralSet.mem_support]
    simp [requirement]
  have different : index ≠ coordinate := by
    intro equal
    subst index
    exact absent indexPresent
  have inputValue : input index = value := by
    rw [Parity.flip_other input coordinate index different] at flippedValue
    exact flippedValue
  apply clauseFalse
  exact (Clause.eval_eq_true clause input).2
    ⟨index, value, requirement, inputValue⟩

/-- A bounded-width CNF computing restricted parity leaves no more live
variables than its width. -/
theorem liveCount_le_width_of_computes_parity
    (formula : CNF n)
    (rho : PartialAssignment n)
    (bound : Nat)
    (bounded : formula.WidthAtMost bound)
    (computes : ∀ input,
      formula.eval input = (Parity.function n).restrict rho input) :
    rho.liveCount ≤ bound := by
  by_cases noLive : rho.liveCount = 0
  · simp [noLive]
  · have liveNonempty : rho.liveVariables.Nonempty :=
      Finset.card_pos.mp (by
        simpa [PartialAssignment.liveCount] using Nat.pos_of_ne_zero noLive)
    obtain ⟨clause, present, covers⟩ :=
      exists_clause_covering_liveVariables_of_computes_parity
        formula rho liveNonempty computes
    calc
      rho.liveCount = rho.liveVariables.card := rfl
      _ ≤ clause.support.card := Finset.card_le_card covers
      _ = clause.width := rfl
      _ ≤ bound := bounded clause present

end CNF

namespace DNF

/-- The width obstruction is insensitive to complementing parity's output. -/
theorem liveCount_le_width_of_computes_parityUpToNegation
    (formula : DNF n)
    (rho : PartialAssignment n)
    (bound : Nat)
    (bounded : formula.WidthAtMost bound)
    (candidate : ScalarFunction Bool n)
    (phase : Parity.UpToNegation candidate)
    (computes : ∀ input,
      formula.eval input = candidate.restrict rho input) :
    rho.liveCount ≤ bound := by
  rcases phase with parity | complement
  · apply formula.liveCount_le_width_of_computes_parity rho bound bounded
    intro input
    simpa [parity] using computes input
  · apply formula.negate.liveCount_le_width_of_computes_parity
      rho bound bounded.negate
    intro input
    rw [DNF.eval_negate, computes input, ScalarFunction.restrict_apply,
      complement]
    simp

end DNF

namespace CNF

/-- The width obstruction is insensitive to complementing parity's output. -/
theorem liveCount_le_width_of_computes_parityUpToNegation
    (formula : CNF n)
    (rho : PartialAssignment n)
    (bound : Nat)
    (bounded : formula.WidthAtMost bound)
    (candidate : ScalarFunction Bool n)
    (phase : Parity.UpToNegation candidate)
    (computes : ∀ input,
      formula.eval input = candidate.restrict rho input) :
    rho.liveCount ≤ bound := by
  rcases phase with parity | complement
  · apply formula.liveCount_le_width_of_computes_parity rho bound bounded
    intro input
    simpa [parity] using computes input
  · apply formula.negate.liveCount_le_width_of_computes_parity
      rho bound bounded.negate
    intro input
    rw [CNF.eval_negate, computes input, ScalarFunction.restrict_apply,
      complement]
    simp

end CNF

end AC0
end Algebraic

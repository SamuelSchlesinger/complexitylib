/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Switching
public import Complexitylib.Circuits.AC0.Switching.Parity.Internal
public import Complexitylib.Circuits.RandomRestriction
public import Complexitylib.Circuits.XOR.Restriction

/-!
# Switching lemmas against parity

This module connects the width-sensitive switching encoding to the exact
decision-tree lower bound for parity under a finite restriction. If a CNF or
DNF computes `N`-bit parity, then every restriction leaving at least
`queryCount` variables free belongs to its switching bad event.

The resulting cardinality inequality is division-free and applies to arbitrary
formulas: contradictory DNF terms and tautological CNF clauses are cleaned
without changing semantics or increasing width.
-/

@[expose] public section

namespace Complexity

namespace DNF

/-- A DNF switching tree for restricted parity must have depth at least the
number of variables left free by the restriction. -/
theorem freeVariables_card_le_switchingDepth_of_xorBool
    (formula : DNF N) (restriction : Restriction.On N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input) :
    restriction.freeVariables.card ≤
      (formula.switchingDecisionTreeUnder restriction).depth :=
  freeVariables_card_le_switchingDepth_of_xorBool_internal
    formula restriction computes

/-- Every restriction leaving at least `queryCount` variables free is bad for
a DNF that computes parity. -/
theorem freeVariables_atLeast_implies_switchingBad
    (formula : DNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (queryCount : ℕ) (restriction : Restriction.On N)
    (hfree :
      queryCount ≤ restriction.freeVariables.card) :
    switchingBad formula queryCount restriction :=
  freeVariables_atLeast_implies_switchingBad_internal
    formula computes queryCount restriction hfree

/-- The count of restrictions leaving many variables free is bounded by the
DNF switching bad-event count. -/
theorem freeVariables_eventCount_le_switchingBad
    (formula : DNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
        (fun restriction : Restriction.On N =>
          queryCount ≤ restriction.freeVariables.card) ≤
      RandomRestriction.eventCount (q := q)
        (switchingBad formula queryCount) :=
  freeVariables_eventCount_le_switchingBad_internal
    formula computes q queryCount

/-- Width-sensitive finite counting obstruction for any DNF computing parity.

The formula is cleaned internally, so no consistency hypothesis is required
and the displayed width is that of the original DNF. -/
theorem switchingParity_width_counting_bound
    (formula : DNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
        (fun restriction : Restriction.On N =>
          queryCount ≤ restriction.freeVariables.card) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount :=
  switchingParity_width_counting_bound_internal
    formula computes q queryCount

/-- Explicit one-surviving-variable specialization of the DNF switching
obstruction. The event count has been evaluated exactly. -/
theorem switchingParity_width_one_free_bound
    (formula : DNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q : ℕ) :
    ((2 * q + 1) ^ N - (2 * q) ^ N) * q ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) :=
  switchingParity_width_one_free_bound_internal
    formula computes q

end DNF

namespace CNF

/-- A CNF switching tree for restricted parity must have depth at least the
number of variables left free by the restriction. -/
theorem freeVariables_card_le_switchingDepth_of_xorBool
    (formula : CNF N) (restriction : Restriction.On N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input) :
    restriction.freeVariables.card ≤
      (formula.switchingDecisionTreeUnder restriction).depth :=
  freeVariables_card_le_switchingDepth_of_xorBool_internal
    formula restriction computes

/-- Every restriction leaving at least `queryCount` variables free is bad for
a CNF that computes parity. -/
theorem freeVariables_atLeast_implies_switchingBad
    (formula : CNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (queryCount : ℕ) (restriction : Restriction.On N)
    (hfree :
      queryCount ≤ restriction.freeVariables.card) :
    switchingBad formula queryCount restriction :=
  freeVariables_atLeast_implies_switchingBad_internal
    formula computes queryCount restriction hfree

/-- The count of restrictions leaving many variables free is bounded by the
CNF switching bad-event count. -/
theorem freeVariables_eventCount_le_switchingBad
    (formula : CNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
        (fun restriction : Restriction.On N =>
          queryCount ≤ restriction.freeVariables.card) ≤
      RandomRestriction.eventCount (q := q)
        (switchingBad formula queryCount) :=
  freeVariables_eventCount_le_switchingBad_internal
    formula computes q queryCount

/-- Width-sensitive finite counting obstruction for any CNF computing parity.

The formula is cleaned internally, so no consistency hypothesis is required
and the displayed width is that of the original CNF. -/
theorem switchingParity_width_counting_bound
    (formula : CNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
        (fun restriction : Restriction.On N =>
          queryCount ≤ restriction.freeVariables.card) *
        q ^ queryCount ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) ^ queryCount :=
  switchingParity_width_counting_bound_internal
    formula computes q queryCount

/-- Explicit one-surviving-variable specialization of the CNF switching
obstruction. The event count has been evaluated exactly. -/
theorem switchingParity_width_one_free_bound
    (formula : CNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q : ℕ) :
    ((2 * q + 1) ^ N - (2 * q) ^ N) * q ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) :=
  switchingParity_width_one_free_bound_internal
    formula computes q

end CNF

end Complexity

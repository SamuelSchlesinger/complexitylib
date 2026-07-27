/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.Switching.Internal
public import Complexitylib.Circuits.XOR.Restriction.Internal

/-!
# Switching lemmas against parity -- proof internals
-/

@[expose] public section

namespace Complexity

namespace DNF

theorem freeVariables_card_le_switchingDepth_of_xorBool_internal
    (formula : DNF N) (restriction : Restriction.On N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input) :
    restriction.freeVariables.card ≤
      (formula.switchingDecisionTreeUnder restriction).depth := by
  apply
    Schnorr.freeVariables_card_le_depth_of_restricted_xor_internal
  intro input
  rw [switchingDecisionTreeUnder_eq_internal,
    eval_switchingDecisionTree_internal,
    DNF.eval_restrict, computes]

theorem freeVariables_atLeast_implies_switchingBad_internal
    (formula : DNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (queryCount : ℕ) (restriction : Restriction.On N)
    (hfree :
      queryCount ≤ restriction.freeVariables.card) :
    switchingBad formula queryCount restriction := by
  exact hfree.trans
    (freeVariables_card_le_switchingDepth_of_xorBool_internal
      formula restriction computes)

theorem freeVariables_eventCount_le_switchingBad_internal
    (formula : DNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
        (fun restriction : Restriction.On N =>
          queryCount ≤ restriction.freeVariables.card) ≤
      RandomRestriction.eventCount (q := q)
        (switchingBad formula queryCount) := by
  apply RandomRestriction.eventCount_mono_internal
  intro restriction hfree
  exact freeVariables_atLeast_implies_switchingBad_internal
    formula computes queryCount restriction hfree

theorem switchingParity_width_counting_bound_internal
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
        (4 * (formula.width + 1)) ^ queryCount := by
  have hcomputesClean :
      ∀ input,
        formula.consistentPart.eval input =
          Schnorr.xorBool N input := by
    intro input
    rw [eval_consistentPart_internal, computes]
  have hcount :=
    freeVariables_eventCount_le_switchingBad_internal
      formula.consistentPart hcomputesClean q queryCount
  exact
    (Nat.mul_le_mul_right (q ^ queryCount) hcount).trans
      (switchingBad_consistentPart_width_encoding_bound_internal
        formula q queryCount)

theorem switchingParity_width_one_free_bound_internal
    (formula : DNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q : ℕ) :
    ((2 * q + 1) ^ N - (2 * q) ^ N) * q ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) := by
  have hbound :=
    switchingParity_width_counting_bound_internal
      formula computes q 1
  rw [RandomRestriction.eventCount_one_le_freeVariables_internal]
    at hbound
  simpa using hbound

end DNF

namespace CNF

theorem freeVariables_card_le_switchingDepth_of_xorBool_internal
    (formula : CNF N) (restriction : Restriction.On N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input) :
    restriction.freeVariables.card ≤
      (formula.switchingDecisionTreeUnder restriction).depth := by
  apply
    Schnorr.freeVariables_card_le_depth_of_restricted_xor_internal
  intro input
  rw [switchingDecisionTreeUnder_eq_internal,
    eval_switchingDecisionTree_internal,
    CNF.eval_restrict, computes]

theorem freeVariables_atLeast_implies_switchingBad_internal
    (formula : CNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (queryCount : ℕ) (restriction : Restriction.On N)
    (hfree :
      queryCount ≤ restriction.freeVariables.card) :
    switchingBad formula queryCount restriction := by
  exact hfree.trans
    (freeVariables_card_le_switchingDepth_of_xorBool_internal
      formula restriction computes)

theorem freeVariables_eventCount_le_switchingBad_internal
    (formula : CNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q queryCount : ℕ) :
    RandomRestriction.eventCount (q := q)
        (fun restriction : Restriction.On N =>
          queryCount ≤ restriction.freeVariables.card) ≤
      RandomRestriction.eventCount (q := q)
        (switchingBad formula queryCount) := by
  apply RandomRestriction.eventCount_mono_internal
  intro restriction hfree
  exact freeVariables_atLeast_implies_switchingBad_internal
    formula computes queryCount restriction hfree

theorem switchingParity_width_counting_bound_internal
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
        (4 * (formula.width + 1)) ^ queryCount := by
  have hcomputesClean :
      ∀ input,
        formula.consistentPart.eval input =
          Schnorr.xorBool N input := by
    intro input
    rw [eval_consistentPart_internal, computes]
  have hcount :=
    freeVariables_eventCount_le_switchingBad_internal
      formula.consistentPart hcomputesClean q queryCount
  exact
    (Nat.mul_le_mul_right (q ^ queryCount) hcount).trans
      (switchingBad_consistentPart_width_encoding_bound_internal
        formula q queryCount)

theorem switchingParity_width_one_free_bound_internal
    (formula : CNF N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (q : ℕ) :
    ((2 * q + 1) ^ N - (2 * q) ^ N) * q ≤
      (2 * q + 1) ^ N *
        (4 * (formula.width + 1)) := by
  have hbound :=
    switchingParity_width_counting_bound_internal
      formula computes q 1
  rw [RandomRestriction.eventCount_one_le_freeVariables_internal]
    at hbound
  simpa using hbound

end CNF

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Fixed menus covering every finite state

This module proves the finite counting step in the nonuniform scheduler.
If a single candidate fails on only a small fraction of choices for each
state, a short list of candidates covers every state simultaneously. The
list is chosen once, before the runtime state is supplied.

The geometric failure estimate is a separate premise of this general lemma;
no circuit or geometric scheduler bound is asserted in this module.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped BigOperators

variable {State Choice : Type*} [Fintype State] [Fintype Choice]

/-- A menu covers all states if each state has a successful entry. -/
def Covers (good : State → Choice → Prop) (menu : Fin length → Choice) : Prop :=
  ∀ state, ∃ entry, good state (menu entry)

/-- Counting all-bad lists and then taking a union over states gives a fixed
menu whenever the bad-list bound is smaller than the entire list space. -/
theorem existsCoveringMenuOfCardBound
    (good : State → Choice → Prop) (length badBound : Nat)
    (badSmall : ∀ state,
      Nat.card {choice // ¬ good state choice} ≤ badBound)
    (totalSmall : Fintype.card State * badBound ^ length <
      Fintype.card Choice ^ length) :
    ∃ menu : Fin length → Choice, Covers good menu := by
  classical
  let badLists : State → Finset (Fin length → Choice) := fun state =>
    Fintype.piFinset fun _ => Finset.univ.filter fun choice => ¬ good state choice
  have badListsCard (state : State) :
      (badLists state).card ≤ badBound ^ length := by
    dsimp [badLists]
    rw [Fintype.card_piFinset_const]
    apply Nat.pow_le_pow_left
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using badSmall state
  let badUnion := Finset.univ.biUnion badLists
  have badUnionSmall : badUnion.card <
      (Finset.univ : Finset (Fin length → Choice)).card := by
    calc
      badUnion.card ≤ ∑ state : State, (badLists state).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _state : State, badBound ^ length :=
        Finset.sum_le_sum fun state _ => badListsCard state
      _ = Fintype.card State * badBound ^ length := by simp
      _ < Fintype.card Choice ^ length := totalSmall
      _ = (Finset.univ : Finset (Fin length → Choice)).card := by simp
  obtain ⟨menu, _, menuGood⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card badUnionSmall
  refine ⟨menu, ?_⟩
  intro state
  by_contra allBad
  apply menuGood
  apply Finset.mem_biUnion.mpr
  refine ⟨state, Finset.mem_univ _, ?_⟩
  simpa only [badLists, Fintype.mem_piFinset, Finset.mem_filter,
    Finset.mem_univ, true_and, not_exists] using allBad

/-- An exponential single-candidate failure bound and a state-description
bound give a menu with `descriptionBits / exponent + 1` entries. -/
theorem existsCoveringMenuOfExponentialBound
    [Nonempty Choice]
    (good : State → Choice → Prop) (descriptionBits exponent : Nat)
    (exponentPositive : 0 < exponent)
    (statesSmall : Fintype.card State ≤ 2 ^ descriptionBits)
    (badSmall : ∀ state,
      Nat.card {choice // ¬ good state choice} * 2 ^ exponent ≤
        Fintype.card Choice) :
    ∃ menu : Fin (descriptionBits / exponent + 1) → Choice,
      Covers good menu := by
  let length := descriptionBits / exponent + 1
  let badBound := Fintype.card Choice / 2 ^ exponent
  have powerPositive : 0 < 2 ^ exponent := by positivity
  have candidatePositive : 0 < Fintype.card Choice := Fintype.card_pos
  have productLarge : descriptionBits < exponent * length := by
    dsimp [length]
    have remainderSmall := Nat.mod_lt descriptionBits exponentPositive
    have division := Nat.mod_add_div descriptionBits exponent
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have stateStrict : Fintype.card State < (2 ^ exponent) ^ length := by
    apply statesSmall.trans_lt
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) productLarge
  have boundedProduct : badBound * 2 ^ exponent ≤ Fintype.card Choice :=
    Nat.div_mul_le_self _ _
  have totalSmall : Fintype.card State * badBound ^ length <
      Fintype.card Choice ^ length := by
    apply Nat.lt_of_mul_lt_mul_right (a := (2 ^ exponent) ^ length)
    calc
      (Fintype.card State * badBound ^ length) * (2 ^ exponent) ^ length =
          Fintype.card State * (badBound * 2 ^ exponent) ^ length := by
        rw [mul_pow]
        ring
      _ ≤ Fintype.card State * Fintype.card Choice ^ length := by gcongr
      _ < (2 ^ exponent) ^ length * Fintype.card Choice ^ length := by
        exact Nat.mul_lt_mul_of_pos_right stateStrict (by positivity)
      _ = Fintype.card Choice ^ length * (2 ^ exponent) ^ length := by ring
  apply existsCoveringMenuOfCardBound good length badBound _ totalSmall
  intro state
  exact (Nat.le_div_iff_mul_le powerPositive).2 (badSmall state)

end Algebraic.MassProduction.Nonuniform

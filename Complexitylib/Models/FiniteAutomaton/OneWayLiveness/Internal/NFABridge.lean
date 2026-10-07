/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Defs

/-!
# One-way liveness in Mathlib's NFA model

The relation-product language is exactly the language of the ordinary
`h`-state NFA whose transitions are the relations in the input. This connects
the imported lower bound to Mathlib's one-way automata and regular languages.
-/

public section

namespace Complexity.FiniteAutomaton

theorem livenessNFA_evalFrom (h : ℕ) (w : List (Alphabet h)) (S : Set (Fin h))
    (q : Fin h) :
    q ∈ (livenessNFA h).evalFrom S w ↔ ∃ p ∈ S, w.prod.holds p q := by
  induction w generalizing S with
  | nil => simp [BRel.one_holds]
  | cons R w ih =>
    simp only [NFA.evalFrom_cons, ih, NFA.mem_stepSet, List.prod_cons, BRel.mul_holds]
    change (∃ p, (∃ a ∈ S, R.holds a p) ∧ w.prod.holds p q) ↔
      ∃ a ∈ S, ∃ p, R.holds a p ∧ w.prod.holds p q
    aesop

theorem livenessNFA_accepts_proof (h : ℕ) :
    (livenessNFA h).accepts = oneWayLiveness h := by
  ext w
  change (∃ q ∈ (Set.univ : Set (Fin h)),
    q ∈ (livenessNFA h).evalFrom Set.univ w) ↔ ∃ p q, w.prod.holds p q
  simp only [Set.mem_univ, true_and, livenessNFA_evalFrom]
  exact exists_comm

end Complexity.FiniteAutomaton

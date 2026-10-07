/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.Complementation.Internal.Model
public import Complexitylib.Models.FiniteAutomaton.Defs

/-!
# Two-way complementation on the canonical automata model

Translate the existing endmarker, movement, and state conventions into the
source model without adding states. Swapping the configuration components
identifies the step relations and finite runs, including zero-step acceptance.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton.Complementation.Internal

/-- Translate the two numbered endmarkers and ordinary letters. -/
def decodeSymbol {Alpha : Type} : Fin 2 ⊕ Alpha → Symbol Alpha
  | .inl i => if i = 0 then .left else .right
  | .inr a => .letter a

/-- Translate source move codes zero, one, and two into left, stay, and right. -/
def decodeMove (m : Fin 3) : Move :=
  if m = 0 then .left else if m = 1 then .stay else .right

/-- Encode left, stay, and right moves as zero, one, and two. -/
def encodeMove : Move → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

theorem decode_encode_move (m : Move) : decodeMove (encodeMove m) = m := by
  cases m <;> rfl

theorem decodeMove_rel (m : Fin 3) (i j : ℕ) :
    (j : ℤ) = (i : ℤ) + (m.val : ℤ) - 1 ↔ (decodeMove m).Rel i j := by
  fin_cases m <;> simp [decodeMove, Move.Rel] <;> lia

theorem decodeSymbol_tapeSymbol {Alpha : Type} (w : List Alpha)
    (p : Fin (w.length + 2)) : decodeSymbol (tapeSymbol w p) = scanned w p := by
  by_cases hleft : p.val = 0
  · simp [tapeSymbol, scanned, hleft, decodeSymbol]
  · by_cases hright : p.val = w.length + 1
    · simp [tapeSymbol, scanned, hright, decodeSymbol]
    · have hp : p.val < w.length + 1 := by lia
      simp [tapeSymbol, scanned, hleft, hright, hp, decodeSymbol]

/-- View a canonical nondeterministic automaton as a source automaton on the same states. -/
def asSource {Alpha : Type} {s : ℕ} (M : NMachine Alpha s) : TwoNFA Alpha (Fin s) where
  initial := M.initial
  accepting := M.accepting
  transition q a := {p | (p.1, decodeMove p.2) ∈ M.transition q (decodeSymbol a)}

theorem asSource_step {Alpha : Type} {s : ℕ} (M : NMachine Alpha s) (w : List Alpha)
    (c d : Fin s × Fin (w.length + 2)) :
    (c, d) ∈ (asSource M).step w ↔ M.Step w c.swap d.swap := by
  change (∃ m : Fin 3, (d.1, decodeMove m) ∈ M.transition c.1
    (decodeSymbol (tapeSymbol w c.2)) ∧
    (d.2.val : ℤ) = (c.2.val : ℤ) + (m.val : ℤ) - 1) ↔ _
  rw [decodeSymbol_tapeSymbol]
  constructor
  · rintro ⟨m, ht, hp⟩
    exact ⟨decodeMove m, ht, (decodeMove_rel m _ _).mp hp⟩
  · rintro ⟨m, ht, hp⟩
    refine ⟨encodeMove m, ?_, ?_⟩
    · simpa only [decode_encode_move, Prod.swap] using ht
    · apply (decodeMove_rel _ _ _).mpr
      simpa only [decode_encode_move, Prod.swap] using hp

theorem asSource_language {Alpha : Type} {s : ℕ} (M : NMachine Alpha s) (w : List Alpha) :
    w ∈ (asSource M).language ↔ M.Accepts false w := by
  constructor
  · rintro ⟨c, hc, hr⟩
    refine ⟨c.swap, ?_, hc⟩
    exact hr.lift Prod.swap (fun c d h => (asSource_step M w c d).mp h)
  · rintro ⟨c, hr, hc⟩
    refine ⟨c.swap, hc, ?_⟩
    change Relation.ReflTransGen (M.Step w) _ _ at hr
    exact hr.lift Prod.swap (fun c d h => (asSource_step M w c.swap d.swap).mpr h)

end Complexity.FiniteAutomaton.Complementation.Internal

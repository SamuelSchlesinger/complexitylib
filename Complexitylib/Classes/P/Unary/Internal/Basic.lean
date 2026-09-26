/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# Polynomial-time numbers and tests — one-bit flags

The string facts behind the comparison, connective and case rules of
`Complexitylib.Classes.P.Unary`. Cobham's toolkit already computes the length
comparison, the Boolean connectives and a selection by a leading bit in
polynomial time; on one-bit strings each of them is the corresponding operation
on `Bool`, which is what lets a verdict be carried as a `Bool`.

## Contents

- `lenLeFlag_eq_decide` — the length comparison as a decided proposition
- `andBit_singleton`, `orBit_singleton`, `notBit_singleton` — the connectives on
  one-bit strings
- `selectHead_singleton` — selection by a one-bit string is an `if`
-/

@[expose] public section

namespace Complexity

/-- The length comparison `|b| ≤ |a|` outputs its verdict as one bit. -/
theorem lenLeFlag_eq_decide (a b : List Bool) :
    Cobham.lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  rcases Cobham.lenLeFlag_flag a b with h | h
  · rw [h, decide_eq_true ((Cobham.lenLeFlag_eq_true_iff a b).mp h)]
  · have hn : ¬ b.length ≤ a.length := fun hle => by
      have := (Cobham.lenLeFlag_eq_true_iff a b).mpr hle
      rw [h] at this
      exact Bool.false_ne_true (List.head_eq_of_cons_eq this)
    rw [h, decide_eq_false hn]

/-- Conjunction of one-bit strings. -/
theorem andBit_singleton (b c : Bool) : andBit [b] [c] = [b && c] := by
  cases b <;> cases c <;> rfl

/-- Disjunction of one-bit strings. -/
theorem orBit_singleton (b c : Bool) : orBit [b] [c] = [b || c] := by
  cases b <;> cases c <;> rfl

/-- Negation of a one-bit string. -/
theorem notBit_singleton (b : Bool) : notBit [b] = [!b] := by
  cases b <;> rfl

/-- Selection by a one-bit string picks the first branch on `true` and the
second on `false`. -/
theorem selectHead_singleton (b : Bool) (x y : List Bool) :
    Cobham.selectHead [b] x y = if b = true then x else y := by
  cases b <;> rfl

end Complexity

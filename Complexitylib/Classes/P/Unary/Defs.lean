/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Defs

/-!
# Polynomial-time numbers and tests — definitions

Two predicates that let a polynomial-time construction be stated on natural
numbers and propositions instead of on the strings a machine reads and writes.

A number is written in *unary*, as a string of that many `true`s. A function
from strings to numbers is polynomial-time (`UnaryFn`) when writing its value in
unary is. A test on strings is polynomial-time (`FPPred`) when a polynomial-time
function outputs its verdict as one bit.

`Complexitylib.Classes.P.Unary` proves that both are closed under the usual
arithmetic, comparisons, connectives and bounded loops, so that a function such
as `z ↦ |z| / 3` can be shown polynomial-time by combining rules.

## Main definitions

- `Complexity.UnaryFn` — a function to `ℕ` whose value can be written in unary
  in polynomial time
- `Complexity.FPPred` — a test decided by a polynomial-time one-bit verdict
-/

@[expose] public section

namespace Complexity

/-- **A polynomial-time number.** `UnaryFn f` says that writing `f z` in unary,
as `f z` copies of `true`, is a polynomial-time function of `z`.

For example, a randomness or query bound `r` is time-constructible in the sense
of the PCP development exactly when `UnaryFn fun x => r x.length`. -/
def UnaryFn (f : List Bool → ℕ) : Prop :=
  (fun z => List.replicate (f z) true) ∈ FP

/-- **A polynomial-time test.** `FPPred p` says that some polynomial-time
function outputs a single bit that is `true` exactly on the strings satisfying
`p`. This is the shape `mem_P_of_decisionFn_bool` turns into membership in
`P`. -/
def FPPred (p : List Bool → Prop) : Prop :=
  ∃ g : List Bool → Bool, (fun z => [g z]) ∈ FP ∧ ∀ z, p z ↔ g z = true

end Complexity

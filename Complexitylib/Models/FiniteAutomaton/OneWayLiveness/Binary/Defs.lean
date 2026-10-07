/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.FiniteAutomaton.OneWayLiveness.Defs

/-!
# A binary encoding of one-way liveness

The NFA scans a relation truth table using three groups of vertex counters.
A two-bit encoding of four scanner letters adds a three-valued bit buffer.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton.BinaryLiveness

/-- Four letters encode matrix entries, row boundaries, and relation boundaries. -/
inductive Letter where
  | bit : Bool → Letter
  | row
  | stop
  deriving DecidableEq, Fintype

/-- A row counter, a column counter, or the chosen target vertex. -/
inductive State (n : ℕ) where
  | seek : Fin (n + 1) → State n
  | scan : Fin (n + 1) → State n
  | carry : Fin (n + 1) → State n
  deriving DecidableEq, Fintype

open State

/-- Scan the selected relation row and nondeterministically choose a true entry. -/
def rules {n : ℕ} : State n → Letter → Set (State n)
  | .seek i, .bit _ => {.seek i}
  | .seek i, .row =>
      if hi : i.val = 0 then {.scan (Fin.last n)}
      else {.seek ⟨i.val - 1, by lia⟩}
  | .scan i, .bit b =>
      (if hi : i.val = 0 then ∅ else {.scan ⟨i.val - 1, by lia⟩}) ∪
        (if b then {.carry i} else ∅)
  | .carry i, .stop => {.seek i}
  | .carry i, _ => {.carry i}
  | _, _ => ∅

/-- The four-letter relation scanner; all row-selection states start and accept. -/
def machine (n : ℕ) : NFA Letter (State n) where
  step := rules
  start := Set.range seek
  accept := Set.range seek

/-- List the first `k` entries of a row in decreasing column order. -/
def columnWord (bits : ℕ → Bool) (k : ℕ) : List Letter :=
  ((List.range k).reverse.map bits).map Letter.bit

/-- A row marker followed by all entries in decreasing column order. -/
def rowWord (n : ℕ) (bits : ℕ → Bool) : List Letter :=
  Letter.row :: columnWord bits (n + 1)

/-- Read a row by its index, returning an all-false row outside the list. -/
def rowAt (rows : List (ℕ → Bool)) (i : ℕ) : ℕ → Bool :=
  rows[i]?.getD (fun _ => false)

/-- The truth-table rows of a relation in increasing source-vertex order. -/
noncomputable def relationRows {n : ℕ} (R : BRel (Fin (n + 1))) : List (ℕ → Bool) := by
  classical
  exact List.ofFn fun i : Fin (n + 1) => fun j =>
    if hj : j < n + 1 then decide (R.holds i ⟨j, hj⟩) else false

/-- Encode a relation by its marked rows followed by a relation terminator. -/
noncomputable def code {n : ℕ} (R : BRel (Fin (n + 1))) : List Letter :=
  (relationRows R).flatMap (rowWord n) ++ [Letter.stop]

/-- Encode each scanner letter by a pair of bits. -/
def letterBits : Letter → List Bool
  | .bit b => [false, b]
  | .row => [true, false]
  | .stop => [true, true]

/-- Decode a pair of bits into a scanner letter. -/
def decode : Bool → Bool → Letter
  | false, b => .bit b
  | true, false => .row
  | true, true => .stop

/-- Original states at a codeword boundary, with no buffered bit. -/
def boundary {Q : Type} (S : Set Q) : Set (Q × Option Bool) :=
  {p | p.1 ∈ S ∧ p.2 = none}

/-- Buffer the first bit, then execute the transition named by the bit pair. -/
def binaryRules {Q : Type} (M : NFA Letter Q) :
    Q × Option Bool → Bool → Set (Q × Option Bool)
  | (q, none), b => {(q, some b)}
  | (q, some a), b => boundary (M.step q (decode a b))

/-- Replace each transition of a four-letter NFA by two binary transitions. -/
def binaryMachine {Q : Type} (M : NFA Letter Q) : NFA Bool (Q × Option Bool) where
  step := binaryRules M
  start := boundary M.start
  accept := boundary M.accept

/-- The binary truth-table encoding of a relation. -/
noncomputable def binaryCode {n : ℕ} (R : BRel (Fin (n + 1))) : List Bool :=
  (code R).flatMap letterBits

end Complexity.FiniteAutomaton.BinaryLiveness

namespace Complexity.FiniteAutomaton

/-- States of the binary liveness NFA for relations on `n + 2` vertices. -/
abbrev BinaryLivenessState (n : ℕ) := BinaryLiveness.State (n + 1) × Option Bool

/-- A binary NFA with `9 * (n + 2)` states and exponential two-way deterministic cost. -/
def binaryLivenessNFA (n : ℕ) : NFA Bool (BinaryLivenessState n) :=
  BinaryLiveness.binaryMachine (BinaryLiveness.machine (n + 1))

/-- Encode a relation on `n + 2` vertices as a binary word. -/
noncomputable def binaryLivenessCode {n : ℕ} (R : Alphabet (n + 2)) : List Bool :=
  BinaryLiveness.binaryCode R

end Complexity.FiniteAutomaton

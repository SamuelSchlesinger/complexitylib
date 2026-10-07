/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-!
# Two-way finite automata

Adapted from OpenAI's one-way-liveness formalization (25 September 2026):
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Automata/Model.lean

The input is enclosed by two distinct endmarkers. Transitions cannot cross
these boundaries. Acceptance means that a finite run reaches an accepting
state, with no requirement that rejected inputs halt. The Boolean `positive`
parameter selects whether a length-zero accepting run is permitted (`false`)
or excluded (`true`). `NoLeft` permits stationary moves as well as right moves.
State counts include all states. These are finite automata, independently of
the work tapes and time accounting of the library's Turing machines.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

/-- The input alphabet with distinct left and right endmarkers. -/
inductive Symbol (Alpha : Type*) where
  | left : Symbol Alpha
  | letter : Alpha → Symbol Alpha
  | right : Symbol Alpha

/-- A two-way head may move left, stay, or move right. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq

/-- The relation between two head positions specified by a move. -/
def Move.Rel : Move → ℕ → ℕ → Prop
  | .left, i, j => j + 1 = i
  | .stay, i, j => j = i
  | .right, i, j => j = i + 1

/-- The finite word including both endmarkers. -/
def scanned {Alpha : Type*} (w : List Alpha) (i : Fin (w.length + 2)) : Symbol Alpha :=
  if h0 : i.val = 0 then .left
  else if hi : i.val < w.length + 1 then .letter (w[i.val - 1]'(by lia))
  else .right

/-- A head position on the endmarked word and a finite control state. -/
abbrev Configuration {Alpha : Type*} (w : List Alpha) (n : ℕ) := Fin (w.length + 2) × Fin n

/-- A deterministic two-way finite automaton with exactly `s` named states. -/
structure DMachine (Alpha : Type*) (s : ℕ) where
  /-- The initial control state. -/
  initial : Fin s
  /-- The accepting control states. -/
  accepting : Set (Fin s)
  /-- The next control states and head moves for each scanned symbol. -/
  transition : Fin s → Symbol Alpha → Option (Fin s × Move)
  left_boundary : ∀ q q', transition q .left ≠ some (q', .left)
  right_boundary : ∀ q q', transition q .right ≠ some (q', .right)

/-- A nondeterministic two-way finite automaton with exactly `n` named states. -/
structure NMachine (Alpha : Type*) (n : ℕ) where
  /-- The initial control state. -/
  initial : Fin n
  /-- The accepting control states. -/
  accepting : Set (Fin n)
  /-- The next control states and head moves for each scanned symbol. -/
  transition : Fin n → Symbol Alpha → Set (Fin n × Move)
  left_boundary : ∀ q q', (q', .left) ∉ transition q .left
  right_boundary : ∀ q q', (q', .right) ∉ transition q .right

/-- A deterministic transition and its associated head movement. -/
def DMachine.Step {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s) (w : List Alpha)
    (c c' : Configuration w s) : Prop :=
  ∃ d, M.transition c.2 (scanned w c.1) = some (c'.2, d) ∧ d.Rel c.1.val c'.1.val

/-- A chosen nondeterministic transition and its associated head movement. -/
def NMachine.Step {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) (w : List Alpha)
    (c c' : Configuration w n) : Prop :=
  ∃ d, (c'.2, d) ∈ M.transition c.2 (scanned w c.1) ∧ d.Rel c.1.val c'.1.val

/-- The positive convention explicitly excludes a length-zero computation. -/
def FiniteRun {C : Type*} (positive : Bool) (step : C → C → Prop) (c c' : C) : Prop :=
  if positive then Relation.TransGen step c c' else Relation.ReflTransGen step c c'

/-- A finite run from the left endmarker reaches an accepting state. -/
def DMachine.Accepts {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by lia⟩, M.initial) c ∧ c.2 ∈ M.accepting

/-- Some finite run from the left endmarker reaches an accepting state. -/
def NMachine.Accepts {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by lia⟩, M.initial) c ∧ c.2 ∈ M.accepting

/-- No transition moves the input head left; stationary moves are allowed. -/
def NMachine.NoLeft {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) : Prop :=
  ∀ q a q', (q', Move.left) ∉ M.transition q a

/-- The accepted words are exactly the members of the language. -/
def NMachine.Recognizes {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L

/-- The accepted words are exactly the members of the language. -/
def DMachine.Recognizes {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L

/-- An alphabet-independent polynomial bound for deterministic simulation. -/
def PolynomialSimulation (positive : Bool) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (Alpha : Type) (_ : Fintype Alpha) (n : ℕ) (N : NMachine Alpha n),
    ∃ (s : ℕ) (D : DMachine Alpha s),
      (s : ℝ) ≤ C * (n : ℝ) ^ c ∧
      ∀ w, D.Accepts positive w ↔ N.Accepts positive w

/-- A polynomial deterministic simulation bound restricted to one-way nondeterministic inputs. -/
def OneWayPolynomialSimulation (positive : Bool) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (Alpha : Type) (_ : Fintype Alpha) (n : ℕ) (N : NMachine Alpha n), N.NoLeft →
    ∃ (s : ℕ) (D : DMachine Alpha s),
      (s : ℝ) ≤ C * (n : ℝ) ^ c ∧
      ∀ w, D.Accepts positive w ↔ N.Accepts positive w

end Complexity.FiniteAutomaton

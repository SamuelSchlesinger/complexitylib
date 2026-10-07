/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.CategoryTheory.Category.RelCat
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-!
# Two-way complementation: model

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TwoWayAutomata/Model.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity.FiniteAutomaton

namespace Complementation.Internal

open scoped SetRel

/-- Reflexive transitive closure, including the empty path. -/
def relStar {α : Type*} (R : SetRel α α) : SetRel α α :=
  {(x, y) | Relation.ReflTransGen (fun a b => (a, b) ∈ R) x y}

/-- A read-only 2NFA. The two endmarkers are `Sum.inl 0` and `Sum.inl 1`.
    Move codes 0, 1, 2 mean left, stay, right. -/
structure TwoNFA (Sigma Q : Type*) where
  /-- The state in which the machine starts on the left endmarker. -/
  initial : Q
  /-- States whose occurrence on a finite run constitutes acceptance. -/
  accepting : Set Q
  /-- Allowed next-state and move pairs, determined by the state and scanned symbol. -/
  transition : Q → (Fin 2 ⊕ Sigma) → Set (Q × Fin 3)

/-- Tape lookup includes two distinct endmarkers, even on empty input. -/
def tapeSymbol {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) : Fin 2 ⊕ Sigma :=
  if hleft : p.val = 0 then .inl 0
  else if hright : p.val = w.length + 1 then .inl 1
  else .inr (w[p.val - 1]'(by omega))

namespace TwoNFA

/-- One legal step: both head positions stay within the marked input. -/
def step {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    SetRel (Q × Fin (w.length + 2)) (Q × Fin (w.length + 2)) :=
  {(c, d) | ∃ move : Fin 3,
    (d.1, move) ∈ A.transition c.1 (tapeSymbol w c.2) ∧
    (d.2.val : ℤ) = (c.2.val : ℤ) + (move.val : ℤ) - 1}

/-- Existential finite-run acceptance, allowing a run of length zero. -/
def language {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Set (List Sigma) :=
  {w | ∃ c, c.1 ∈ A.accepting ∧
    ((A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.step w)}

end TwoNFA

end Complementation.Internal

end Complexity.FiniteAutomaton

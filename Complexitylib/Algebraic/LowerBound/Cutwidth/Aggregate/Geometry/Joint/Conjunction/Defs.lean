/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Defs
public import Mathlib.Data.Finset.Card

/-!
# Finite sets of signed primary literals

Repeated identical literals are represented once. Opposite literals on the same
coordinate remain visible, so contradictions are handled without a normalization
assumption on the original circuit.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

variable {V : Type*} [DecidableEq V]

/-- The primary variables appearing in a finite collection of signed literals. -/
def literalVars (literals : Finset (V × Bool)) : Finset V := literals.image Prod.fst

/-- A conjunction of the specified primary literals. -/
def evalLiterals (literals : Finset (V × Bool)) (x : V → Bool) : Bool :=
  decide (∀ t ∈ literals, x t.1 = t.2)

/-- All literals on a given variable require the same value. -/
def ConsistentLiterals (literals : Finset (V × Bool)) : Prop :=
  ∀ a ∈ literals, ∀ b ∈ literals, a.1 = b.1 → a.2 = b.2

end Algebraic.Cutwidth.Aggregate.Geometry.Joint

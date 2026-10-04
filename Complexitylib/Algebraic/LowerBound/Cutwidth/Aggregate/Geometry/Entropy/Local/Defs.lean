/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite

/-!+# Signed conjunctions on two distinct variables

Each sign records the input value making its literal true. These edges describe
the nonconstant two-variable primary-input summaries of conjunction gates.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-- A conjunction of two signed literals on distinct primary coordinates. -/
structure SignedEdge (V : Type*) where
  /-- First primary variable. -/
  left : V
  /-- Second primary variable. -/
  right : V
  distinct : left ≠ right
  /-- Required value of the first variable. -/
  leftSign : Bool
  /-- Required value of the second variable. -/
  rightSign : Bool

/-- The conjunction is true precisely when both coordinates match their signs. -/
def SignedEdge.eval {V : Type*} (e : SignedEdge V) (x : V → Bool) : Bool :=
  (x e.left == e.leftSign) && (x e.right == e.rightSign)

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Defs

/-!
# Two-coordinate Boolean conjunctions for the finite conditional tables
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-- A signed conjunction on two named coordinates. -/
def pairBit {n : ℕ} (i j : Fin n) (a b : Bool) (x : Fin n → Bool) : Bool :=
  (x i == a) && (x j == b)

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy

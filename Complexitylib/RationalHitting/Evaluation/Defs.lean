/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.RationalHitting.Defs

/-!
# Executable matrix evaluation and finite tests

Every inverse node requires a nonsingular operand. The finite tests inspect
exact rational matrix values; their correctness does not assert a bit-time bound.
-/

@[expose] public section

namespace Complexity.RationalHitting

/-- Compute a matrix value, rejecting a singular operand at every inverse node. -/
def Formula.evalMatrix? {n d : ℕ} (f : Formula n) (X : Tuple n d) : Option (Mat d) :=
  match f with
  | .var i => some (X i)
  | .const a => some (algebraMap ℚ (Mat d) a)
  | .add f g => do
      let a ← f.evalMatrix? X
      let b ← g.evalMatrix? X
      pure (a + b)
  | .mul f g => do
      let a ← f.evalMatrix? X
      let b ← g.evalMatrix? X
      pure (a * b)
  | .inv f => do
      let a ← f.evalMatrix? X
      if a.det = 0 then none else some (a.det⁻¹ • a.adjugate)

/-- Test whether at least one tuple belongs to the formula's domain. -/
def Output.admissibilityTest {n : ℕ} (H : Output n) (f : Formula n) : Bool :=
  H.tuples.any fun X => (f.evalMatrix? X).isSome

/-- Test whether at least one tuple yields an invertible matrix value. -/
def Output.nonzeroTest {n : ℕ} (H : Output n) (f : Formula n) : Bool :=
  H.tuples.any fun X => (f.evalMatrix? X).any fun v => decide (v.det ≠ 0)

end Complexity.RationalHitting

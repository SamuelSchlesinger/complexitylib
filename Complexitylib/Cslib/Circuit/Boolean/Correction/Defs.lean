/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.RelativeComplexity
public import Complexitylib.Cslib.Circuit.Complexity
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Dist

/-!
# Supports and labels of Boolean circuit corrections

All complexity measures are CSLib's minimum De Morgan gate counts. Constants
are counted, and selecting or repeating output wires is free. Relative
complexity supplies both the original input and the comparison function.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Correction

variable {n m : ℕ}

/-- Inputs on which two output vectors differ. -/
def errorSupport (f g : (Fin n → Bool) → Fin m → Bool) : Set (Fin n → Bool) :=
  {x | f x ≠ g x}

/-- Number of input rows on which the two output vectors differ. -/
noncomputable def rowDistance (f g : (Fin n → Bool) → Fin m → Bool) : ℕ := by
  classical
  exact (errorSupport f g).toFinset.card

/-- Output coordinates on which the two functions differ somewhere. -/
noncomputable def activeOutputs (f g : (Fin n → Bool) → Fin m → Bool) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j => ∃ x, f x j ≠ g x j

/-- The indicator of a set, as a single-output target. -/
noncomputable def indicator (s : Set (Fin n → Bool)) : (Fin n → Bool) → Fin 1 → Bool := by
  classical
  exact fun x _ => decide (x ∈ s)

/-- The XOR correction restricted to a selected finite set of output coordinates. -/
noncomputable def errorVector (f g : (Fin n → Bool) → Fin m → Bool)
    (outputs : Finset (Fin m)) : (Fin n → Bool) → Fin outputs.card → Bool :=
  fun x j => Bool.xor (f x ((outputs.equivFin).symm j))
    (g x ((outputs.equivFin).symm j))

end Cslib.Circuits.Boolean.Correction

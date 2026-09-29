/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Layer.Internal

/-!
# Compiling alternating layers to CSLib

The output is a CSLib circuit over `Basis.unboundedAndOr.signature`. Size
counts AND/OR gates and depth counts gate layers; signed inputs cost neither.
-/

public section

namespace Complexity.Shallow.Layer

/-- Alternating layers compile to a CSLib circuit with exactly their gate
count, without increasing depth. -/
theorem exists_circuit {n d : ℕ} (f : Layer n (d + 1)) (op : AndOrOp) :
    ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1,
      c.size = size f ∧ c.depth ≤ d + 1 ∧
        c.Computes Basis.unboundedAndOr.interpretation (fun x _ => eval op f x) ∧
        InputNegationsOnly c := by
  obtain ⟨c, b, hs, hd, he, hb, hn⟩ := exists_signed_circuit f op
  have hb' := hb (Nat.zero_lt_succ d)
  subst b
  refine ⟨c, hs, hd, fun x => ?_, hn⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [hi] using he x

end Complexity.Shallow.Layer

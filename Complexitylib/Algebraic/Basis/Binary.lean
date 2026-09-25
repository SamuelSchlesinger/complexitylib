/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Data.Fintype.BigOperators

/-!
# The full binary basis

Every gate of the full binary basis `B₂` computes one of the sixteen Boolean
functions of two bits. Both argument slots may read the same wire, fan-out is
unrestricted, and every gate costs one. This is the basis of the `(4 - ε) n`
circuit lower bound in `Algebraic.LowerBound.Cutwidth`.
-/

@[expose] public section

namespace Algebraic
namespace Binary

/-- An operation symbol of the full binary basis is a Boolean function of two bits. -/
abbrev Op := Bool → Bool → Bool

/-- The sixteen binary Boolean functions. -/
theorem card_op : Fintype.card Op = 16 := by
  simp [Fintype.card_bool]

/-- The signature of the full binary basis: every symbol takes two arguments. -/
abbrev signature : Signature where
  Op := Op
  Arity := fun _ => 2

/-- The Boolean interpretation applies the symbol to its two argument bits. -/
def interpretation : Interpretation signature Bool :=
  fun op arguments => op (arguments 0) (arguments 1)

@[simp] theorem interpretation_apply (op : Op) (arguments : Fin 2 → Bool) :
    interpretation op arguments = op (arguments 0) (arguments 1) := rfl

/-- Every gate of a binary program has fan-in two. -/
theorem program_fanInAtMost_two {n g : Nat} (program : Program signature n g) :
    program.FanInAtMost 2 := by
  induction program with
  | empty => trivial
  | gate program line ih => exact ⟨ih, le_rfl⟩

/-- Every gate of a binary circuit has fan-in two. -/
theorem circuit_fanInAtMost_two {n m : Nat} (circuit : Circuit signature n m) :
    circuit.FanInAtMost 2 :=
  program_fanInAtMost_two circuit.program

end Binary
end Algebraic

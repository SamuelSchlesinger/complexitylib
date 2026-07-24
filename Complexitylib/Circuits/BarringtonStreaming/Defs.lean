/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonCompiler.Defs

/-!
# Random-access Barrington instruction streams -- definitions

The ordinary executable compiler constructs its complete instruction list.
For uniform generation we instead need a description supporting one indexed
instruction query at a time. `BPStream` retains only the length and query
function; its combinators implement append, reversal/inversion, final
multiplication, and the four-block commutator without materializing a list.
-/

namespace Complexity

/-- A random-access description of a branching program's instruction list. -/
structure BPStream (w : ℕ) where
  /-- Number of instructions in the represented program. -/
  length : ℕ
  /-- Instruction at a zero-based index, or `none` outside the stream. -/
  instruction? : ℕ → Option (BPInstr w)

namespace BPStream

/-- The empty random-access program. -/
def empty : BPStream w where
  length := 0
  instruction? := fun _ => none

/-- A one-instruction random-access program. -/
def singleton (instruction : BPInstr w) : BPStream w where
  length := 1
  instruction? := fun index => if index = 0 then some instruction else none

/-- Concatenate two random-access programs. -/
def append (left right : BPStream w) : BPStream w where
  length := left.length + right.length
  instruction? := fun index =>
    if index < left.length then left.instruction? index
    else right.instruction? (index - left.length)

/-- Reverse a random-access program and invert every instruction. -/
def inverse (stream : BPStream w) : BPStream w where
  length := stream.length
  instruction? := fun index =>
    if index < stream.length then
      (stream.instruction? (stream.length - 1 - index)).map BPInstr.inverse
    else none

/-- Fold a constant permutation into the final instruction. -/
def postMul (stream : BPStream w) (permutation : Equiv.Perm (Fin w)) :
    BPStream w where
  length := max 1 stream.length
  instruction? := fun index =>
    if stream.length = 0 then
      if index = 0 then some (BPInstr.const permutation) else none
    else if index + 1 = stream.length then
      (stream.instruction? index).map fun instruction =>
        BPInstr.postMul instruction permutation
    else stream.instruction? index

/-- The four-block stream `left right left⁻¹ right⁻¹`. -/
def commutator (left right : BPStream w) : BPStream w :=
  ((left.append right).append left.inverse).append right.inverse

/-- A stream agrees with a concrete branching program when its length and
every indexed query are exact. -/
def CorrectFor (stream : BPStream w) (program : BP w) : Prop :=
  stream.length = program.length ∧
    ∀ index, stream.instruction? index = program[index]?

end BPStream

/-- Exact number of instructions produced by Barrington compilation. Unlike
the compiler itself, this recurrence never constructs an instruction. -/
def barringtonInstructionCount : BoolFormula → ℕ
  | .var _ | .tru => 1
  | .fls => 0
  | .neg formula => max 1 (barringtonInstructionCount formula)
  | .conj left right =>
      2 * barringtonInstructionCount left +
        2 * barringtonInstructionCount right
  | .disj left right =>
      2 * max 1 (barringtonInstructionCount left) +
        2 * max 1 (barringtonInstructionCount right)

/-- Random-access form of the executable Barrington compiler. No recursive
case constructs a complete branching-program list. -/
def barringtonCompileStream : BoolFormula →
    Equiv.Perm (Fin 5) → BPStream 5
  | .var index, target =>
      .singleton ⟨index, 1, target⟩
  | .tru, target =>
      .singleton (BPInstr.const target)
  | .fls, _ =>
      .empty
  | .neg formula, target =>
      (barringtonCompileStream formula target⁻¹).postMul target
  | .conj left right, target =>
      .commutator
        (barringtonCompileStream left (barringtonLeft target))
        (barringtonCompileStream right (barringtonRight target))
  | .disj left right, target =>
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftStream :=
        (barringtonCompileStream left leftTarget⁻¹).postMul leftTarget
      let rightStream :=
        (barringtonCompileStream right rightTarget⁻¹).postMul rightTarget
      (BPStream.commutator leftStream rightStream).postMul target

end Complexity

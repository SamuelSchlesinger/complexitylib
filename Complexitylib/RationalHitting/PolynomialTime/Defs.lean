/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.RationalHitting
public import Complexitylib.Interop.Mathlib.TM0.Guard.Defs

/-!
# A total binary interface to the rational hitting-list generator

The input is `true^n ++ [false] ++ true^s`, with both parameters positive.
Every other string returns the empty string. The successful output is exactly
the source's encoding of its rational matrix hitting list.
-/

@[expose] public section

namespace Complexity.RationalHitting

/-- The binary form of the source's two unary parameters. -/
def binaryInput (n s : ℕ) : List Bool :=
  List.replicate n true ++ false :: List.replicate s true

/-- States recognizing two nonempty unary blocks separated by one false bit. -/
inductive InputState where
  /-- No input has been read. -/
  | start
  /-- At least one bit of the first unary block has been read. -/
  | left
  /-- The separator has just been read. -/
  | separator
  /-- At least one bit of the second unary block has been read. -/
  | right
  /-- The input is malformed. -/
  | dead
  deriving DecidableEq

/-- The validator uses five concrete states. -/
instance : Fintype InputState where
  elems := {.start, .left, .separator, .right, .dead}
  complete q := by cases q <;> simp

/-- A five-state validator for the literal source input format. -/
def inputDFA : DFA Bool InputState where
  start := .start
  accept := {.right}
  step q b := match q, b with
    | .start, true => .left
    | .left, true => .left
    | .left, false => .separator
    | .separator, true => .right
    | .right, true => .right
    | _, _ => .dead

/-- The format check is computable by the finite validator. -/
instance decidableInput : DecidablePred (· ∈ inputDFA.accepts) :=
  fun w => inferInstanceAs (Decidable (inputDFA.eval w = .right))

/-- Read the first unary block. -/
def inputVariables (w : List Bool) : ℕ := (w.takeWhile id).length

/-- Read the remaining unary size, excluding the separator. -/
def inputSize (w : List Bool) : ℕ := w.length - inputVariables w - 1

/-- Generate an encoded hitting list, returning empty output on malformed inputs. -/
def hittingGenerator (w : List Bool) : List Bool :=
  if w ∈ inputDFA.accepts then
    encodeOutput (hittingList (inputVariables w) (inputSize w))
  else []

end Complexity.RationalHitting

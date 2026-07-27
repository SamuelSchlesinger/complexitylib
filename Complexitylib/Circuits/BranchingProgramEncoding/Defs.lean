/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonCompiler.Defs
public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Mathlib.NatBits

/-!
# Machine-facing encoding of width-five branching programs

This file defines a deterministic, proof-free bit format for the width-`5`
permutation branching programs produced by Barrington's theorem. Permutations
are represented by their rank in the computable `S₅` enumeration, using seven
bits because `|S₅| = 120 < 2^7`. Variable indices and the instruction count use
the existing terminated-unary circuit codec.

An instruction is encoded as its variable field followed by two fixed-width
permutation fields. A program starts with its instruction count, so exact
decoding rejects truncation and trailing garbage.
-/

@[expose] public section

namespace Complexity

namespace BPCode

namespace Perm5

/-- Number of bits in the canonical rank encoding of an `S₅` permutation. -/
def bitWidth : ℕ := 7

/-- The fixed computable table used to rank and unrank `S₅`. -/
def table : List (Equiv.Perm (Fin 5)) :=
  allPermutationsFin 5

/-- The canonical table position of a permutation. -/
def index (permutation : Equiv.Perm (Fin 5)) : ℕ :=
  table.idxOf permutation

/-- Encode an `S₅` permutation by its seven-bit table position. -/
def encode (permutation : Equiv.Perm (Fin 5)) : List Bool :=
  Nat.toBits bitWidth (index permutation)

/-- Decode one fixed-width permutation field and return the unused suffix. -/
def decodePrefix? (bits : List Bool) : Option (Equiv.Perm (Fin 5) × List Bool) :=
  if bits.length < bitWidth then
    none
  else
    match table[Nat.fromBits (bits.take bitWidth)]? with
    | none => none
    | some permutation => some (permutation, bits.drop bitWidth)

end Perm5

namespace Instr

/-- Encode one width-`5` instruction as a terminated-unary variable followed
by its two seven-bit permutation ranks. -/
def encode (instruction : BPInstr 5) : List Bool :=
  CircuitCode.NatCode.encode instruction.var ++
    Perm5.encode instruction.perm0 ++ Perm5.encode instruction.perm1

/-- Decode one instruction prefix and return the unused suffix. -/
def decodePrefix? (bits : List Bool) : Option (BPInstr 5 × List Bool) := do
  let (var, rest) ← CircuitCode.NatCode.decodePrefix? bits
  let (perm0, rest) ← Perm5.decodePrefix? rest
  let (perm1, rest) ← Perm5.decodePrefix? rest
  some (⟨var, perm0, perm1⟩, rest)

end Instr

namespace Program

/-- Decode exactly `count` instruction prefixes and return the unused suffix. -/
def decodeInstructions? : ℕ → List Bool → Option (BP 5 × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (instruction, rest) ← Instr.decodePrefix? bits
      let (program, rest) ← decodeInstructions? count rest
      some (instruction :: program, rest)

/-- Canonically encode a width-`5` branching program. -/
def encode (program : BP 5) : List Bool :=
  CircuitCode.NatCode.encode program.length ++ program.flatMap Instr.encode

/-- Decode one complete program prefix and return the unused suffix. -/
def decodePrefix? (bits : List Bool) : Option (BP 5 × List Bool) := do
  let (count, rest) ← CircuitCode.NatCode.decodePrefix? bits
  decodeInstructions? count rest

/-- Decode exactly one width-`5` branching program. Trailing bits are rejected. -/
def decode? (bits : List Bool) : Option (BP 5) :=
  match decodePrefix? bits with
  | some (program, []) => some program
  | _ => none

end Program

end BPCode

end Complexity

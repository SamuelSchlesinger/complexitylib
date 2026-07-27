/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BranchingProgramEncoding.Defs
public import Complexitylib.Circuits.BranchingProgramEncoding.Internal

/-!
# Canonical encoding of width-five branching programs

This module exposes the machine-facing codec used by the uniform Barrington
track. Every `S₅` permutation is ranked in a fixed computable table and stored
in seven bits. Instructions add a terminated-unary variable index, and a
program adds a terminated-unary instruction count.

The exact decoder is a left inverse, serialization is injective, nonempty
trailing data is rejected, and the code length is explicit. Consequently the
remaining uniformity proof can target one stable bit format without carrying
finite permutation proofs on the machine tape.

## Main results

- `BPCode.Perm5.decodePrefix?_encode_append` -- permutation-field round trip.
- `BPCode.Instr.decodePrefix?_encode_append` -- instruction round trip.
- `BPCode.Program.decode?_encode` -- whole-program round trip.
- `BPCode.Program.encode_injective` -- canonical codes are unambiguous.
- `BPCode.Program.length_encode` -- exact serialization length.
-/

@[expose] public section

namespace Complexity

namespace BPCode

namespace Perm5

/-- The explicit permutation table has exactly `5! = 120` entries. -/
theorem table_length : table.length = 120 :=
  table_length_internal

/-- Every permutation of `Fin 5` occurs in the fixed table. -/
theorem mem_table (permutation : Equiv.Perm (Fin 5)) : permutation ∈ table :=
  mem_table_internal permutation

/-- Every canonical table position fits in the seven-bit field. -/
theorem index_lt_two_pow (permutation : Equiv.Perm (Fin 5)) :
    index permutation < 2 ^ bitWidth :=
  index_lt_two_pow_internal permutation

/-- Every encoded permutation field has the fixed width of seven bits. -/
@[simp] theorem length_encode (permutation : Equiv.Perm (Fin 5)) :
    (encode permutation).length = bitWidth :=
  length_encode_internal permutation

/-- Decoding an encoded permutation in front of any suffix recovers both. -/
@[simp] theorem decodePrefix?_encode_append
    (permutation : Equiv.Perm (Fin 5)) (suffix : List Bool) :
    decodePrefix? (encode permutation ++ suffix) =
      some (permutation, suffix) :=
  decodePrefix?_encode_append_internal permutation suffix

end Perm5

namespace Instr

/-- An instruction uses its unary variable length plus fourteen permutation
bits, for a total of `var + 15`. -/
@[simp] theorem length_encode (instruction : BPInstr 5) :
    (encode instruction).length = instruction.var + 15 :=
  length_encode_internal instruction

/-- Decoding an encoded instruction in front of any suffix recovers both. -/
@[simp] theorem decodePrefix?_encode_append
    (instruction : BPInstr 5) (suffix : List Bool) :
    decodePrefix? (encode instruction ++ suffix) =
      some (instruction, suffix) :=
  decodePrefix?_encode_append_internal instruction suffix

end Instr

namespace Program

/-- Fixed-count decoding consumes exactly the requested encoded instructions. -/
@[simp] theorem decodeInstructions?_flatMap_encode_append
    (program : BP 5) (suffix : List Bool) :
    decodeInstructions? program.length (program.flatMap Instr.encode ++ suffix) =
      some (program, suffix) :=
  decodeInstructions?_flatMap_encode_append_internal program suffix

/-- Prefix decoding preserves a caller-supplied suffix. -/
@[simp] theorem decodePrefix?_encode_append
    (program : BP 5) (suffix : List Bool) :
    decodePrefix? (encode program ++ suffix) = some (program, suffix) :=
  decodePrefix?_encode_append_internal program suffix

/-- Exact decoding is a left inverse of canonical serialization. -/
@[simp] theorem decode?_encode (program : BP 5) :
    decode? (encode program) = some program :=
  decode?_encode_internal program

/-- Canonical program serialization is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact decoding rejects nonempty trailing data. -/
theorem decode?_encode_append_eq_none
    (program : BP 5) {suffix : List Bool} (hsuffix : suffix ≠ []) :
    decode? (encode program ++ suffix) = none :=
  decode?_encode_append_eq_none_internal program hsuffix

/-- Exact code length: one unary count field plus all instruction fields. -/
@[simp] theorem length_encode (program : BP 5) :
    (encode program).length =
      program.length + 1 +
        (program.map fun instruction => instruction.var + 15).sum :=
  length_encode_internal program

/-- If all variable indices are bounded, serialization has the corresponding
linear-in-program-length bound. -/
theorem length_encode_le (program : BP 5) (variableBound : ℕ)
    (hvars : ∀ instruction ∈ program, instruction.var ≤ variableBound) :
    (encode program).length ≤
      program.length + 1 + program.length * (variableBound + 15) :=
  length_encode_le_internal program variableBound hvars

end Program

end BPCode

end Complexity

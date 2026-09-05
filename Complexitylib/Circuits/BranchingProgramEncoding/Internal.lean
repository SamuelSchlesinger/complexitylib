/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BarringtonCompiler
public import Complexitylib.Circuits.BranchingProgramEncoding.Defs
public import Complexitylib.Circuits.Encoding.Internal.Codec
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

/-!
# Width-five branching-program codec internals

This module proves round-trip and length properties of the canonical codec.
Public statements are re-exported by
`Complexitylib.Circuits.BranchingProgramEncoding`.
-/


public section

set_option maxRecDepth 100000

namespace Complexity

namespace BPCode

namespace Perm5

/-- Internal cardinality check for the explicit `S₅` table. -/
theorem table_length_internal : table.length = 120 := by
  decide

/-- Internal completeness of the fixed permutation table. -/
theorem mem_table_internal (permutation : Equiv.Perm (Fin 5)) :
    permutation ∈ table := by
  simpa only [table] using mem_allPermutationsFin permutation

/-- Internal proof that every canonical permutation rank fits in seven bits. -/
theorem index_lt_two_pow_internal (permutation : Equiv.Perm (Fin 5)) :
    index permutation < 2 ^ bitWidth := by
  have hindex : index permutation < table.length :=
    List.idxOf_lt_length_of_mem (mem_table_internal permutation)
  rw [table_length_internal] at hindex
  rw [show (2 : ℕ) ^ bitWidth = 128 from rfl]
  omega

/-- Internal exact length of a permutation field. -/
theorem length_encode_internal (permutation : Equiv.Perm (Fin 5)) :
    (encode permutation).length = bitWidth := by
  simp [encode, Nat.length_toBits]

/-- Internal permutation-prefix round trip. -/
theorem decodePrefix?_encode_append_internal
    (permutation : Equiv.Perm (Fin 5)) (suffix : List Bool) :
    decodePrefix? (encode permutation ++ suffix) =
      some (permutation, suffix) := by
  have hmem := mem_table_internal permutation
  have hindexTable : index permutation < table.length :=
    List.idxOf_lt_length_of_mem hmem
  have hindexPow := index_lt_two_pow_internal permutation
  simp [decodePrefix?, encode, Nat.length_toBits, Nat.fromBits_toBits hindexPow,
    hindexTable]
  exact List.getElem_idxOf hindexTable

end Perm5

namespace Instr

/-- Internal exact instruction-code length. -/
theorem length_encode_internal (instruction : BPInstr 5) :
    (encode instruction).length = instruction.var + 15 := by
  simp [encode, CircuitCode.NatCode.length_encode,
    Perm5.length_encode_internal, Perm5.bitWidth]

/-- Internal instruction-prefix round trip. -/
theorem decodePrefix?_encode_append_internal
    (instruction : BPInstr 5) (suffix : List Bool) :
    decodePrefix? (encode instruction ++ suffix) =
      some (instruction, suffix) := by
  rcases instruction with ⟨var, perm0, perm1⟩
  simp [encode, decodePrefix?, List.append_assoc,
    Perm5.decodePrefix?_encode_append_internal]

end Instr

namespace Program

/-- Internal fixed-count instruction-list round trip. -/
theorem decodeInstructions?_flatMap_encode_append_internal
    (program : BP 5) (suffix : List Bool) :
    decodeInstructions? program.length (program.flatMap Instr.encode ++ suffix) =
      some (program, suffix) := by
  induction program with
  | nil => simp [decodeInstructions?]
  | cons instruction program ih =>
      simp [decodeInstructions?, ih, List.append_assoc,
        Instr.decodePrefix?_encode_append_internal]

/-- Internal program-prefix round trip. -/
theorem decodePrefix?_encode_append_internal
    (program : BP 5) (suffix : List Bool) :
    decodePrefix? (encode program ++ suffix) = some (program, suffix) := by
  simp [decodePrefix?, encode, List.append_assoc,
    decodeInstructions?_flatMap_encode_append_internal]

/-- Internal exact-decoder round trip. -/
theorem decode?_encode_internal (program : BP 5) :
    decode? (encode program) = some program := by
  unfold decode?
  rw [show encode program = encode program ++ [] by simp,
    decodePrefix?_encode_append_internal]

/-- Internal proof that canonical program serialization is injective. -/
theorem encode_injective_internal : Function.Injective encode := by
  intro left right heq
  have hleft := decode?_encode_internal left
  have hright := decode?_encode_internal right
  rw [heq] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

/-- Internal proof that exact decoding rejects a nonempty trailing suffix. -/
theorem decode?_encode_append_eq_none_internal
    (program : BP 5) {suffix : List Bool} (hsuffix : suffix ≠ []) :
    decode? (encode program ++ suffix) = none := by
  unfold decode?
  rw [decodePrefix?_encode_append_internal]
  simp [hsuffix]

/-- Internal exact program-code length. -/
theorem length_encode_internal (program : BP 5) :
    (encode program).length =
      program.length + 1 +
        (program.map fun instruction => instruction.var + 15).sum := by
  simp [encode, CircuitCode.NatCode.length_encode, List.length_flatMap,
    Instr.length_encode_internal]

/-- Internal polynomial bound when every referenced variable is bounded. -/
theorem length_encode_le_internal (program : BP 5) (variableBound : ℕ)
    (hvars : ∀ instruction ∈ program, instruction.var ≤ variableBound) :
    (encode program).length ≤
      program.length + 1 + program.length * (variableBound + 15) := by
  have hsum :
      (program.map fun instruction => instruction.var + 15).sum ≤
        program.length * (variableBound + 15) := by
    induction program with
    | nil => simp
    | cons instruction program ih =>
        have hinstruction : instruction.var ≤ variableBound :=
          hvars instruction (by simp)
        have htail : ∀ item ∈ program, item.var ≤ variableBound := by
          intro item hitem
          exact hvars item (by simp [hitem])
        specialize ih htail
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        calc
          instruction.var + 15 +
                (program.map fun item => item.var + 15).sum ≤
              (variableBound + 15) +
                program.length * (variableBound + 15) :=
            Nat.add_le_add (Nat.add_le_add_right hinstruction 15) ih
          _ = (program.length + 1) * (variableBound + 15) := by
            simp only [Nat.add_mul, Nat.one_mul]
            ac_rfl
  rw [length_encode_internal]
  exact Nat.add_le_add_left hsum (program.length + 1)

end Program

end BPCode

end Complexity

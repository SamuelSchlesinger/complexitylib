/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding.Defs
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding.Internal

/-!
# Exact decoding of finite structures

Decoding and encoding are inverse on structures, including their relation and
constant interpretations. The decoder succeeds precisely on valid encodings;
every other bit string is rejected. These are computability and correctness
results, without a machine time or space bound.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- The empty input is not a structure encoding. -/
@[simp] theorem decodeStruct_nil (V : Vocabulary) : decodeStruct V [] = none := by
  simp [decodeStruct]

/-- Every encoded structure is recovered exactly by the computable decoder. -/
@[simp] theorem decodeStruct_encodeStruct {V : Vocabulary} (A : DecFinStruct V) :
    decodeStruct V (encodeStruct A) = some A := decodeStruct_encodeStruct_internal A

/-- Successful decoding is equivalent to exact re-encoding of the returned structure. -/
theorem decodeStruct_eq_some_iff {V : Vocabulary} (bits : List Bool) (A : DecFinStruct V) :
    decodeStruct V bits = some A ↔ encodeStruct A = bits := by
  constructor
  · exact decodeStruct_sound_internal bits A
  · rintro rfl
    exact decodeStruct_encodeStruct A

/-- A rejected input is exactly a string outside the image of the encoder. -/
theorem decodeStruct_eq_none_iff {V : Vocabulary} (bits : List Bool) :
    decodeStruct V bits = none ↔ ¬ ∃ A : DecFinStruct V, encodeStruct A = bits := by
  constructor
  · intro h ⟨A, hA⟩
    have := (decodeStruct_eq_some_iff bits A).mpr hA
    rw [h] at this
    contradiction
  · intro h
    cases hd : decodeStruct V bits with
    | none => rfl
    | some A => exact (h ⟨A, (decodeStruct_eq_some_iff bits A).mp hd⟩).elim

/-- The bit-string encoding determines all fields of a decidable finite structure. -/
theorem encodeStruct_injective {V : Vocabulary} : Function.Injective (@encodeStruct V) := by
  intro A B h
  have hd := congrArg (decodeStruct V) h
  simpa only [decodeStruct_encodeStruct, Option.some.injEq] using hd

end Complexity.DescriptiveComplexity

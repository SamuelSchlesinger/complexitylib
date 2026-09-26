/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding.Defs

/-!
# Decoder round trips and exact rejection

The position lemmas recover relation tables and the unique value of each
constant. Re-encoding validation gives soundness for every input string.
-/

public section

namespace Complexity.DescriptiveComplexity

private theorem find_value {α : Type} [DecidableEq α] (xs : List α) (a : α)
    (ha : a ∈ xs) : xs.find? (fun b => decide (a = b)) = some a := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    by_cases hab : a = b
    · subst b
      simp
    · simp only [List.mem_cons] at ha
      simp [hab, ih (ha.resolve_left hab)]

theorem readStructCandidate_encodeStruct_internal {V : Vocabulary} (A : DecFinStruct V) :
    readStructCandidate V A.card A.hcard (encodeStruct A) = A := by
  have hrel : (readStructCandidate V A.card A.hcard (encodeStruct A)).rel = A.rel := by
    funext i args
    simp [readStructCandidate, getElem?_encodeStruct_position, inputSiteValue]
  have hconst : (readStructCandidate V A.card A.hcard (encodeStruct A)).const = A.const := by
    funext c
    simp only [readStructCandidate, getElem?_encodeStruct_position, inputSiteValue,
      Option.getD_some]
    rw [find_value _ _ (List.mem_finRange _)]
    rfl
  cases A with
  | mk card hcard rel const => exact congrArg₂ (DecFinStruct.mk card hcard) hrel hconst

theorem decodeStruct_encodeStruct_internal {V : Vocabulary} (A : DecFinStruct V) :
    decodeStruct V (encodeStruct A) = some A := by
  simp only [decodeStruct, encodeStruct_card, A.hcard, dite_true,
    encodeStruct_length_eq, ite_true, readStructCandidate_encodeStruct_internal]

theorem decodeStruct_sound_internal {V : Vocabulary} (bits : List Bool) (A : DecFinStruct V)
    (h : decodeStruct V bits = some A) : encodeStruct A = bits := by
  unfold decodeStruct at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · rename_i hcard hlength hcheck
        exact (Option.some.inj h) ▸ hcheck
      · simp at h
    · simp at h
  · simp at h

end Complexity.DescriptiveComplexity

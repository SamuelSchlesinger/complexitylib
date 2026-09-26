/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.TaggedReduction.Encoding.Defs
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Encoding.Validity
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Bridge
import Complexitylib.Classes.P.Cobham.Internal

/-!
# Arithmetic realization of tagged interpretations

Mathlib's tuple equivalence uses little-endian numerals, exactly as the structure
encoder does. The product equivalence places the tag above the coordinate block.
These identities identify arithmetic relation and constant generation with the
existing interpreted structure. Fixed finite formula selection, table scanning,
and encoding validation then give a polynomial-time string map.
-/

public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim : Nat}

theorem elementEquiv_tag_val_internal {card : Nat} (x : Fin (tags * card ^ dim)) :
    (elementEquiv card tags dim x).1.val = x.val / card ^ dim := rfl

theorem elementEquiv_coord_val_internal {card : Nat} (x : Fin (tags * card ^ dim))
    (j : Fin dim) :
    ((elementEquiv card tags dim x).2 j).val = tupleDigits card dim (x.val % card ^ dim) j := by
  exact (tupleDigits_eq_div_pow card dim (x.val % card ^ dim) j).symm

theorem elementEquiv_symm_val_internal {card : Nat} (tag : Fin tags) (coords : Fin dim → Fin card) :
    ((elementEquiv card tags dim).symm (tag, coords)).val =
      tupleIndex card (fun j => (coords j).val) + card ^ dim * tag.val := by
  change (finFunctionFinEquiv coords).val + card ^ dim * tag.val = _
  rw [finFunctionFinEquiv_apply, tupleIndex_eq_sum]

theorem relationEnvCode_eq_internal {card arity : Nat}
    (args : Fin arity → Fin (tags * card ^ dim)) :
    relationEnvCode card dim (fun j => (args j).val) =
      fun k => (relationEnv args k).val := by
  funext k
  exact (elementEquiv_coord_val_internal _ _).symm

theorem applyDec_toFinStruct_internal (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) : (I.applyDec A).toFinStruct = I.apply A.toFinStruct := by
  have hrel : (I.applyDec A).toFinStruct.rel = (I.apply A.toFinStruct).rel := by
    funext r args
    exact propext (Formula.evalB_eq_sat A _ _)
  rw [show (I.applyDec A).toFinStruct =
    { I.apply A.toFinStruct with rel := (I.applyDec A).toFinStruct.rel } from rfl, hrel]

theorem relationBitCode_encodeStruct_internal (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) (r : Fin W.numRels)
    (args : Fin (W.relArity r) → Fin (tags * A.card ^ dim)) :
    I.relationBitCode r A.card (encodeStruct A) (fun j => (args j).val) =
      (I.applyDec A).rel r args := by
  apply Bool.eq_iff_iff.mpr
  change _ ↔ Formula.evalB A (relationEnv args)
    (I.relFormula r (fun j => (elementEquiv A.card tags dim (args j)).1)) = true
  simp only [relationBitCode, List.any_eq_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.mem_finRange, forall_const, relationEnvCode_eq_internal,
    Formula.evalCode_encodeStruct, Formula.evalB_eq_sat]
  constructor
  · rintro ⟨τ, _, htag, hsat⟩
    have ht : τ = fun j => (elementEquiv A.card tags dim (args j)).1 := by
      funext j
      exact Fin.ext (htag j)
    simpa only [ht] using hsat
  · intro hsat
    exact ⟨_, mem_allTuples _ _ _, fun _ => rfl, hsat⟩

theorem relationTableCode_encodeStruct_internal (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) (r : Fin W.numRels) :
    I.relationTableCode r A.card (encodeStruct A) = encodeRelC ((I.applyDec A).rel r) := by
  have hcard : 0 < tags * A.card ^ dim := lt_of_lt_of_le (by decide) (I.two_le_card A.toFinStruct)
  rw [relationTableCode, ← map_allTuples_eq_range hcard]
  unfold encodeRelC
  apply List.map_congr_left
  intro args _
  exact relationBitCode_encodeStruct_internal I A r args

theorem constantCode_encodeStruct_internal (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) (c : Fin W.numConsts) :
    I.constantCode c A.card (encodeStruct A) = ((I.applyDec A).const c).val := by
  have hconst (j : Fin dim) :
      (Term.const (I.constCoord c j) : Term V 0).evalCode A.card (encodeStruct A) Fin.elim0 =
        (A.const (I.constCoord c j)).val := by
    simpa only [Term.evalCode, Term.eval, DecFinStruct.toFinStruct] using
      Term.evalCode_encodeStruct A (Term.const (I.constCoord c j)) (emptyEnv A.card)
  simp only [constantCode, hconst]
  exact (elementEquiv_symm_val_internal _ _).symm

private theorem constant_block_eq (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) (c : Fin W.numConsts) :
    (List.range (tags * A.card ^ dim)).map (fun a =>
      decide (a = I.constantCode c A.card (encodeStruct A))) =
        encodeConstC ((I.applyDec A).const c) := by
  rw [constantCode_encodeStruct_internal]
  apply List.ext_getElem (by simp [applyDec])
  intro i hi hj
  simp [encodeConstC, beq_eq_decide, Fin.ext_iff]

theorem rawEncoding_encodeStruct_internal (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) : I.rawEncoding A.card (encodeStruct A) = encodeStruct (I.applyDec A) := by
  simp only [rawEncoding, relationTableCode_encodeStruct_internal, constant_block_eq]
  rfl

theorem rawEncoding_length_internal (I : TaggedFOInterpretation V W tags dim)
    (card : Nat) (input : List Bool) :
    (I.rawEncoding card input).length = encodingLength W (tags * card ^ dim) := by
  simp [rawEncoding, relationTableCode, encodingLength, List.length_flatMap, Nat.add_assoc]
  omega

end Complexity.DescriptiveComplexity.TaggedFOInterpretation

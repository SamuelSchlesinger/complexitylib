/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime.Defs
public import Complexitylib.DescriptiveComplexity.ModelChecking.Encoded
public import Complexitylib.DescriptiveComplexity.Definable
public import Complexitylib.Classes.P.StringAccess
import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime.Internal
import Complexitylib.Classes.P.DecisionFn

/-!
# First-order queries belong to machine polynomial time

Arithmetic evaluation agrees with the original semantics on encoded structures.
For each fixed formula it is polynomial-time when the input string, cardinality,
and free-variable values are polynomial-time. Combining this result with exact
encoding validation proves `FODefinable.queryLanguage_mem_P` for the existing
machine class `P`, including every malformed input. The original encoded Boolean
evaluator itself has an `FP` one-bit verdict.
For open formulas, `Formula.tableCode` also writes the complete assignment truth
table in polynomial time, with exactly `card ^ n` bits for `n` free variables.

This is the standard fixed-formula model-checking argument from Immerman's
*Descriptive Complexity*, implemented using the library's machine-backed Cobham
closure rules. Logarithmic space is not established. `SecondOrder.PolynomialTime`
extends arithmetic evaluation to existential second-order certificate checking.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Arithmetic term evaluation on an encoding recovers the semantic element's value. -/
theorem Term.evalCode_encodeStruct {V : Vocabulary} {n : Nat} (A : DecFinStruct V)
    (t : Term V n) (σ : Env A.card n) :
    t.evalCode A.card (encodeStruct A) (fun i => (σ i).val) =
      (t.eval A.toFinStruct σ).val := term_evalCode_encodeStruct_internal A t σ

/-- Term evaluation is polynomial-time on polynomial-time numeric inputs. -/
theorem Term.evalCode_unary {V : Vocabulary} {n : Nat} (t : Term V n)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    {σ : List Bool → Fin n → Nat} (hbits : bits ∈ FP) (hcard : UnaryFn card)
    (hσ : ∀ i, UnaryFn fun z => σ z i) :
    UnaryFn fun z => t.evalCode (card z) (bits z) (σ z) :=
  term_evalCode_unary_internal t hbits hcard hσ

/-- Arithmetic formula evaluation on an encoding agrees with first-order satisfaction. -/
theorem Formula.evalCode_encodeStruct {V : Vocabulary} {n : Nat} (A : DecFinStruct V)
    (φ : Formula V n) (σ : Env A.card n) :
    φ.evalCode A.card (encodeStruct A) (fun i => (σ i).val) = true ↔
      φ.Sat A.toFinStruct σ := formula_evalCode_encodeStruct_internal A φ σ

/-- A fixed formula gives a polynomial-time predicate on polynomial-time numeric inputs. -/
theorem Formula.evalCode_fpPred {V : Vocabulary} {n : Nat} (φ : Formula V n)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    {σ : List Bool → Fin n → Nat} (hbits : bits ∈ FP) (hcard : UnaryFn card)
    (hσ : ∀ i, UnaryFn fun z => σ z i) :
    FPPred fun z => φ.evalCode (card z) (bits z) (σ z) = true :=
  formula_evalCode_fpPred_internal φ bits card σ hbits hcard hσ

/-- The arithmetic evaluator's one-bit verdict is a polynomial-time string function. -/
theorem Formula.evalCode_mem_FP {V : Vocabulary} {n : Nat} (φ : Formula V n)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    {σ : List Bool → Fin n → Nat} (hbits : bits ∈ FP) (hcard : UnaryFn card)
    (hσ : ∀ i, UnaryFn fun z => σ z i) :
    (fun z => [φ.evalCode (card z) (bits z) (σ z)]) ∈ FP := by
  simpa using (φ.evalCode_fpPred hbits hcard hσ).flag_mem_FP

/-- A formula's assignment truth table has one bit for each tuple of variable values. -/
@[simp] theorem Formula.tableCode_length {V : Vocabulary} {n : Nat} (φ : Formula V n)
    (card : Nat) (bits : List Bool) : (φ.tableCode card bits).length = card ^ n := by
  simp only [Formula.tableCode, List.length_map, List.length_range]

/-- Formula truth-table generation agrees with the canonical relation-table encoding. -/
theorem Formula.tableCode_encodeStruct {V : Vocabulary} {n : Nat}
    (A : DecFinStruct V) (φ : Formula V n) :
    φ.tableCode A.card (encodeStruct A) = encodeRelC (fun σ => Formula.evalB A σ φ) :=
  formula_tableCode_encodeStruct_internal A φ

/-- Writing the full truth table of a fixed formula is polynomial-time. -/
theorem Formula.tableCode_mem_FP {V : Vocabulary} {n : Nat} (φ : Formula V n)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) :
    (fun z => φ.tableCode (card z) (bits z)) ∈ FP :=
  formula_tableCode_mem_FP_internal φ hbits hcard

/-- Closed arithmetic evaluation agrees with the original sentence semantics. -/
theorem Sentence.evalCode_encodeStruct {V : Vocabulary} (A : DecFinStruct V) (φ : Sentence V) :
    φ.evalCode A.card (encodeStruct A) Fin.elim0 = true ↔ Sentence.Models A.toFinStruct φ :=
  sentence_evalCode_encodeStruct_internal A φ

/-- Sentence truth on arbitrary encoded input is a polynomial-time predicate. -/
theorem Sentence.queryLanguage_fpPred {V : Vocabulary} (φ : Sentence V) :
    FPPred fun input => input ∈ queryLanguage (fun A => Sentence.Models A φ) :=
  sentence_queryLanguage_fpPred_internal φ

/-- Every fixed first-order sentence defines a binary language in machine P. -/
theorem Sentence.queryLanguage_mem_P {V : Vocabulary} (φ : Sentence V) :
    queryLanguage (fun A => Sentence.Models A φ) ∈ P := φ.queryLanguage_fpPred.mem_P

/-- The existing decoder-based Boolean sentence evaluator has a polynomial-time verdict. -/
theorem Sentence.evalEncoded_mem_FP {V : Vocabulary} (φ : Sentence V) :
    (fun input => [φ.evalEncoded input]) ∈ FP := by
  have h := φ.queryLanguage_fpPred.of_iff fun input =>
    (φ.evalEncoded_eq_queryLanguage input).symm
  simpa using h.flag_mem_FP

/-- First-order definability implies polynomial-time membership of the induced binary language. -/
theorem FODefinable.queryLanguage_mem_P {V : Vocabulary} {Q : BooleanQuery V}
    (hQ : FODefinable Q) : queryLanguage Q ∈ P := by
  obtain ⟨φ, hφ⟩ := hQ
  apply FPPred.mem_P
  refine φ.queryLanguage_fpPred.of_iff fun input => ?_
  simp only [mem_queryLanguage_iff_decodeStruct, hφ]

end Complexity.DescriptiveComplexity

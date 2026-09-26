/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.TaggedReduction
public import Complexitylib.DescriptiveComplexity.ModelChecking
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime.Defs
public import Complexitylib.DescriptiveComplexity.Language

/-!
# Tagged interpretations on binary encodings

The decidable structure map uses the same finite product and tuple equivalences
as the original interpretation. Arithmetic generation recovers tags by division
and coordinates by base expansion. Each relation chooses among the fixed finite
family of defining formulas; constants pack tuples of source constants.

The full output has universe size `tags * card ^ dim`. Its binary map decodes,
interprets, and re-encodes, with the fixed non-encoding `[]` for malformed input.
This extends the structural reduction method of Immerman, Chapter 3, to the
tagged full-product interpretation design of Senellart and Gnatenko (2026).
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim : Nat}

/-- Evaluate the defining formulas on the exact tagged tuple universe. -/
def applyDec (I : TaggedFOInterpretation V W tags dim) (A : DecFinStruct V) :
    DecFinStruct W where
  card := tags * A.card ^ dim
  hcard := I.two_le_card A.toFinStruct
  rel r args := Formula.evalB A (relationEnv args)
    (I.relFormula r (fun j => (elementEquiv A.card tags dim (args j)).1))
  const c := (elementEquiv A.card tags dim).symm
    (I.constTag c, fun j => A.const (I.constCoord c j))

/-- Recover the flattened source coordinates from numeric target-element indices. -/
def relationEnvCode (card dim : Nat) {arity : Nat} (args : Fin arity → Nat) :
    Fin (arity * dim) → Nat := fun k =>
  tupleDigits card dim (args (finProdFinEquiv.symm k).1 % card ^ dim)
    (finProdFinEquiv.symm k).2

/-- Select a defining formula by its tag tuple and evaluate its source coordinates. -/
def relationBitCode (I : TaggedFOInterpretation V W tags dim) (r : Fin W.numRels)
    (card : Nat) (input : List Bool) (args : Fin (W.relArity r) → Nat) : Bool :=
  (allTuples tags (W.relArity r)).any fun τ =>
    (List.finRange (W.relArity r)).all (fun j => decide ((τ j).val = args j / card ^ dim)) &&
      (I.relFormula r τ).evalCode card input (relationEnvCode card dim args)

/-- Write the complete target relation table in canonical tuple order. -/
def relationTableCode (I : TaggedFOInterpretation V W tags dim) (r : Fin W.numRels)
    (card : Nat) (input : List Bool) : List Bool :=
  (List.range ((tags * card ^ dim) ^ W.relArity r)).map fun index =>
    I.relationBitCode r card input (tupleDigits (tags * card ^ dim) (W.relArity r) index)

/-- Pack the fixed tag and source-constant coordinates of a target constant. -/
def constantCode (I : TaggedFOInterpretation V W tags dim) (c : Fin W.numConsts)
    (card : Nat) (input : List Bool) : Nat :=
  tupleIndex card (fun j =>
    (Term.const (I.constCoord c j) : Term V 0).evalCode card input Fin.elim0) +
      card ^ dim * (I.constTag c).val

/-- Generate all target tables and constant blocks at a supplied source size. -/
def rawEncoding (I : TaggedFOInterpretation V W tags dim) (card : Nat)
    (input : List Bool) : List Bool :=
  let size := tags * card ^ dim
  List.replicate size true ++ false ::
    ((List.finRange W.numRels).flatMap (fun r => I.relationTableCode r card input) ++
      (List.finRange W.numConsts).flatMap fun c => (List.range size).map fun a =>
        decide (a = I.constantCode c card input))

/-- Decode, interpret, and re-encode, sending malformed inputs to the non-encoding `[]`. -/
def mapEncoding (I : TaggedFOInterpretation V W tags dim) (input : List Bool) : List Bool :=
  match decodeStruct V input with
  | none => []
  | some A => encodeStruct (I.applyDec A)

end Complexity.DescriptiveComplexity.TaggedFOInterpretation

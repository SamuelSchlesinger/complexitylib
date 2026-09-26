/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Reduction
public import Complexitylib.DescriptiveComplexity.ModelChecking
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime.Defs
public import Complexitylib.DescriptiveComplexity.Language

/-!
# First-order interpretations on binary encodings

The universe-preserving interpretation acts computably on decidable structures.
Its string map decodes, interprets, and re-encodes, sending malformed strings to
the empty string. Arithmetic table generation supplies a polynomial-time
implementation of this same map in the surface module.

This is the encoding bridge from structural first-order reductions to machine
many-one reductions, following Immerman's *Descriptive Complexity*, Chapter 3.
Tagged tuple interpretations and exact projective reductions are separate APIs.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.FOInterpretation

variable {V W : Vocabulary}

/-- Interpret a decidable structure by evaluating the defining relation formulas. -/
def applyDec (I : FOInterpretation V W) (A : DecFinStruct V) : DecFinStruct W where
  card := A.card
  hcard := A.hcard
  rel r args := Formula.evalB A args (I.relFormula r)
  const c := A.const (I.constMap c)

/-- Generate target tables arithmetically at a supplied universe size, without validation. -/
def rawEncoding (I : FOInterpretation V W) (card : Nat) (input : List Bool) : List Bool :=
  List.replicate card true ++ false ::
    ((List.finRange W.numRels).flatMap (fun r => (I.relFormula r).tableCode card input) ++
      (List.finRange W.numConsts).flatMap fun c => (List.range card).map fun a =>
        input[constantAddress V card (I.constMap c) a]?.getD false)

/-- Decode, interpret, and re-encode; malformed input maps to the fixed non-encoding `[]`. -/
def mapEncoding (I : FOInterpretation V W) (input : List Bool) : List Bool :=
  match decodeStruct V input with
  | none => []
  | some A => encodeStruct (I.applyDec A)

end Complexity.DescriptiveComplexity.FOInterpretation

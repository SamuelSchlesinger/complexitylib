/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic
public import Complexitylib.DescriptiveComplexity.SecondOrder.Encoding
public import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P

/-!
# Polynomial-time access to structure encodings

The universe size, tuple coordinates, and bit positions are natural numbers
written in unary by polynomial-time machines. Fixed-arity tuple indices,
relation addresses, constant addresses, and encoding lengths use only fixed
sums, powers, and products. Bit reads at these positions therefore have actual
`FP` implementations, including the false default on missing input bits.

The unary-cardinality parser and the encoded-length check are also polynomial
time. `Encoding.Validity` uses these primitives to recognize valid encodings in
`P`, and `ModelChecking.PolynomialTime` proves the same bound for fixed first-order
queries. `SecondOrder.PolynomialTime` extends evaluation to relation witnesses
and proves polynomial-time existential-SO certificate checking.
-/

public section

namespace Complexity.DescriptiveComplexity

private theorem sum_powers_unary {ι : Type} (indices : List ι) (arity : ι → Nat)
    {card : List Bool → Nat} (hcard : UnaryFn card) :
    UnaryFn fun z => (indices.map fun i => card z ^ arity i).sum := by
  induction indices with
  | nil => exact UnaryFn.const 0
  | cons i indices ih => exact (hcard.pow_const (arity i)).add ih

/-- Fixed-arity tuple indices are polynomial-time unary numbers. -/
theorem tupleIndex_unary {card : List Bool → Nat} {k : Nat}
    {args : List Bool → Fin k → Nat} (hcard : UnaryFn card)
    (hargs : ∀ i, UnaryFn fun z => args z i) :
    UnaryFn fun z => tupleIndex (card z) (args z) := by
  induction k with
  | zero => exact UnaryFn.const 0
  | succ k ih => exact (hargs 0).add (hcard.mul (ih fun i => hargs i.succ))

/-- Extracting a fixed coordinate of a polynomial-time tuple index is polynomial-time. -/
theorem tupleDigits_unary {card index : List Bool → Nat}
    (hcard : UnaryFn card) (hindex : UnaryFn index) (k : Nat) (i : Fin k) :
    UnaryFn fun z => tupleDigits (card z) k (index z) i := by
  induction k generalizing index with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hindex.mod hcard
    · exact ih (hindex.div hcard) j

/-- Computing a fixed relation's bit address is polynomial-time. -/
theorem relationAddress_unary (V : Vocabulary) (r : Fin V.numRels)
    {card : List Bool → Nat} {args : List Bool → Fin (V.relArity r) → Nat}
    (hcard : UnaryFn card) (hargs : ∀ i, UnaryFn fun z => args z i) :
    UnaryFn fun z => relationAddress V (card z) r (args z) :=
  ((hcard.add (UnaryFn.const 1)).add
    (sum_powers_unary ((List.finRange V.numRels).take r.val) V.relArity hcard)).add
      (tupleIndex_unary hcard hargs)

/-- Computing a fixed constant's one-hot bit address is polynomial-time. -/
theorem constantAddress_unary (V : Vocabulary) (c : Fin V.numConsts)
    {card a : List Bool → Nat} (hcard : UnaryFn card) (ha : UnaryFn a) :
    UnaryFn fun z => constantAddress V (card z) c (a z) :=
  (((hcard.add (UnaryFn.const 1)).add
    (sum_powers_unary (List.finRange V.numRels) V.relArity hcard)).add
      ((UnaryFn.const c.val).mul hcard)).add ha

/-- The full encoded structure length is polynomial-time in a polynomial-time universe size. -/
theorem encodingLength_unary (V : Vocabulary) {card : List Bool → Nat}
    (hcard : UnaryFn card) : UnaryFn fun z => encodingLength V (card z) :=
  ((hcard.add (UnaryFn.const 1)).add
    (sum_powers_unary (List.finRange V.numRels) V.relArity hcard)).add
      ((UnaryFn.const V.numConsts).mul hcard)

/-- A fixed relation-witness context's certificate length is a polynomial-time unary number. -/
theorem DecREnv.encodingLength_unary (rctx : List Nat) {card : List Bool → Nat}
    (hcard : UnaryFn card) : UnaryFn fun z => DecREnv.encodingLength (card z) rctx :=
  sum_powers_unary rctx id hcard

/-- The universe size read from an input's leading unary block is polynomial-time. -/
theorem encodedCard_unary : UnaryFn fun input : List Bool => (input.takeWhile id).length :=
  UnaryFn.leadingTrueLength id_mem_FP

/-- Testing the full encoding length against the parsed cardinality is polynomial-time. -/
theorem encodingLengthMatches_fpPred (V : Vocabulary) :
    FPPred fun input : List Bool =>
      input.length = encodingLength V (input.takeWhile id).length :=
  FPPred.eq (UnaryFn.length id_mem_FP) (encodingLength_unary V encodedCard_unary)

/-- A relation-table bit can be tested in polynomial time at polynomial-time coordinates. -/
theorem relationBit_fpPred (V : Vocabulary) (r : Fin V.numRels)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    {args : List Bool → Fin (V.relArity r) → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) (hargs : ∀ i, UnaryFn fun z => args z i) :
    FPPred fun z => (bits z)[relationAddress V (card z) r (args z)]?.getD false = true :=
  FPPred.getBit hbits (relationAddress_unary V r hcard hargs)

/-- A constant's one-hot bit can be tested in polynomial time. -/
theorem constantBit_fpPred (V : Vocabulary) (c : Fin V.numConsts)
    {bits : List Bool → List Bool} {card a : List Bool → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) (ha : UnaryFn a) :
    FPPred fun z => (bits z)[constantAddress V (card z) c (a z)]?.getD false = true :=
  FPPred.getBit hbits (constantAddress_unary V c hcard ha)

end Complexity.DescriptiveComplexity

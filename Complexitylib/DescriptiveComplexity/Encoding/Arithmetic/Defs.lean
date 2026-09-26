/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Positions

/-!
# Arithmetic addresses in structure encodings

The encoder varies the first tuple coordinate fastest. Its tuple index is thus
the little-endian base-`card` numeral of the coordinates. Relation addresses add
the unary header and the lengths of earlier relation tables. Constant addresses
skip all relation tables and then the preceding one-hot blocks.

Coordinates are natural numbers in these computations; the correctness theorems
specialize to coordinates in `Fin card`. This interface permits direct use of
polynomial-time unary arithmetic without enumerating the tuple universe.
`tupleDigits` also decodes a numeric index to its fixed-width coordinates, for
writing truth tables in the same order.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Little-endian base-`card` index, matching the first-coordinate-fastest tuple order. -/
def tupleIndex (card : Nat) : {k : Nat} → (Fin k → Nat) → Nat
  | 0, _ => 0
  | _ + 1, args => args 0 + card * tupleIndex card (fun i => args i.succ)

/-- Recover the fixed-width little-endian base-`card` coordinates of a tuple index. -/
def tupleDigits (card : Nat) : (k : Nat) → Nat → Fin k → Nat
  | 0, _ => Fin.elim0
  | k + 1, index => Fin.cons (index % card) (tupleDigits card k (index / card))

/-- Arithmetic position of a relation-table bit in the full structure encoding. -/
def relationAddress (V : Vocabulary) (card : Nat) (r : Fin V.numRels)
    (args : Fin (V.relArity r) → Nat) : Nat :=
  card + 1 + (((List.finRange V.numRels).take r.val).map
    (fun i => card ^ V.relArity i)).sum + tupleIndex card args

/-- Arithmetic position of a constant's one-hot bit in the full structure encoding. -/
def constantAddress (V : Vocabulary) (card : Nat) (c : Fin V.numConsts) (a : Nat) : Nat :=
  card + 1 + ((List.finRange V.numRels).map (fun i => card ^ V.relArity i)).sum +
    c.val * card + a

end Complexity.DescriptiveComplexity

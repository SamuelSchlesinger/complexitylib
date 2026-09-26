/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding
public import Mathlib.Data.Fintype.Sum

/-!
# Positions in the finite-structure encoding

The table sites follow exactly the computable enumeration used by `encodeStruct`:
relation symbols in order, their tuples in `allTuples` order, then one-hot
constant blocks. `encodingPosition` includes the unary-cardinality prefix.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- A relation-table cell or one entry in a constant's one-hot block. -/
abbrev InputSite (V : Vocabulary) (card : Nat) :=
  (Σ i : Fin V.numRels, Fin (V.relArity i) → Fin card) ⊕ (Fin V.numConsts × Fin card)

/-- Number of bits in the relation tables and constant blocks. -/
def tableInputCount (V : Vocabulary) (card : Nat) : Nat := Fintype.card (InputSite V card)

/-- The value stored at a table-input site. -/
def inputSiteValue {V : Vocabulary} (A : DecFinStruct V) : InputSite V A.card → Bool
  | .inl ⟨i, args⟩ => A.rel i args
  | .inr (c, a) => decide (A.const c = a)

/-- Table sites in the computable order used by the structure encoder. -/
def encodingTableSites (V : Vocabulary) (card : Nat) : List (InputSite V card) :=
  (List.finRange V.numRels).flatMap (fun i =>
    (allTuples card (V.relArity i)).map (fun args => .inl ⟨i, args⟩)) ++
  (List.finRange V.numConsts).flatMap (fun c =>
    (List.finRange card).map (fun a => .inr (c, a)))

/-- Full encoded length, including the unary cardinality and its terminator. -/
def encodingLength (V : Vocabulary) (card : Nat) : Nat :=
  card + 1 + ((List.finRange V.numRels).map (fun i => card ^ V.relArity i)).sum +
    V.numConsts * card

/-- Zero-based bit position of a table entry in the full encoding. -/
def encodingPosition (V : Vocabulary) (card : Nat) (site : InputSite V card) : Nat :=
  card + 1 + (encodingTableSites V card).idxOf site

end Complexity.DescriptiveComplexity

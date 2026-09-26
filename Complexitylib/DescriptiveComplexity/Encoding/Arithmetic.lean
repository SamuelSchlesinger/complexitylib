/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic.Defs
import Complexitylib.DescriptiveComplexity.Encoding.Arithmetic.Internal

/-!
# Arithmetic access to the canonical structure encoding

Base-`card` tuple indices and prefix sums give exactly the bit positions defined
by the original site enumeration. The equalities include arbitrary relation
arities, nullary relations, and the one-hot blocks for distinguished constants.
Consequently the arithmetic addresses recover the encoded relation and constant
bits, without changing the wire format.
Fixed-width base expansion recovers the tuple coordinates; scanning the numeric
indices reproduces the encoder's tuple enumeration exactly.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Tuple packing is the usual little-endian positional numeral. -/
theorem tupleIndex_eq_sum (card : Nat) {k : Nat} (args : Fin k → Nat) :
    tupleIndex card args = ∑ i : Fin k, args i * card ^ i.val :=
  tupleIndex_eq_sum_internal card args

/-- Each extracted coordinate is a base-`card` digit, including at cardinality zero. -/
theorem tupleDigits_eq_div_pow (card k index : Nat) (i : Fin k) :
    tupleDigits card k index i = index / card ^ i.val % card :=
  tupleDigits_eq_div_pow_internal card k index i

/-- A tuple of valid coordinates has an index inside its relation truth table. -/
theorem tupleIndex_lt {card k : Nat} (args : Fin k → Fin card) :
    tupleIndex card (fun i => (args i).val) < card ^ k := tupleIndex_lt_internal args

/-- The arithmetic index selects the tuple itself in the encoder's enumeration. -/
theorem getElem?_allTuples_index {card k : Nat} (args : Fin k → Fin card) :
    (allTuples card k)[tupleIndex card (fun i => (args i).val)]? = some args :=
  getElem?_allTuples_index_internal args

/-- Arithmetic tuple lookup recovers a bit from a relation's standalone truth table. -/
theorem getElem?_encodeRelC_index {card k : Nat} (S : (Fin k → Fin card) → Bool)
    (args : Fin k → Fin card) :
    (encodeRelC S)[tupleIndex card (fun i => (args i).val)]? = some (S args) := by
  simp only [encodeRelC, List.getElem?_map, getElem?_allTuples_index, Option.map_some]

/-- Every extracted coordinate lies in a positive-cardinality universe. -/
theorem tupleDigits_lt {card : Nat} (hcard : 0 < card) (k index : Nat) (i : Fin k) :
    tupleDigits card k index i < card := tupleDigits_lt_internal hcard k index i

/-- Re-encoding the coordinates recovers every index inside the tuple table. -/
theorem tupleIndex_tupleDigits {card : Nat} (hcard : 0 < card) (k index : Nat)
    (hi : index < card ^ k) : tupleIndex card (tupleDigits card k index) = index :=
  tupleIndex_tupleDigits_internal hcard k index hi

/-- Enumerating tuples agrees with scanning their numeric indices in order. -/
theorem map_allTuples_eq_range {α : Type} {card : Nat} (hcard : 0 < card)
    (k : Nat) (f : (Fin k → Nat) → α) :
    (allTuples card k).map (fun args => f (fun i => (args i).val)) =
      (List.range (card ^ k)).map (fun index => f (tupleDigits card k index)) :=
  map_allTuples_eq_range_internal hcard k f

/-- Arithmetic relation addresses equal the existing enumeration-based positions. -/
theorem encodingPosition_relation (V : Vocabulary) (card : Nat)
    (r : Fin V.numRels) (args : Fin (V.relArity r) → Fin card) :
    encodingPosition V card (.inl ⟨r, args⟩) =
      relationAddress V card r (fun i => (args i).val) :=
  encodingPosition_relation_internal V card r args

/-- Arithmetic constant addresses equal the existing one-hot positions. -/
theorem encodingPosition_constant (V : Vocabulary) (card : Nat)
    (c : Fin V.numConsts) (a : Fin card) :
    encodingPosition V card (.inr (c, a)) = constantAddress V card c a.val :=
  encodingPosition_constant_internal V card c a

/-- Reading the arithmetic relation address returns the corresponding relation bit. -/
theorem getElem?_encodeStruct_relation {V : Vocabulary} (A : DecFinStruct V)
    (r : Fin V.numRels) (args : Fin (V.relArity r) → Fin A.card) :
    (encodeStruct A)[relationAddress V A.card r (fun i => (args i).val)]? =
      some (A.rel r args) := by
  rw [← encodingPosition_relation]
  exact getElem?_encodeStruct_position A (.inl ⟨r, args⟩)

/-- Reading the arithmetic constant address tests equality with the distinguished element. -/
theorem getElem?_encodeStruct_constant {V : Vocabulary} (A : DecFinStruct V)
    (c : Fin V.numConsts) (a : Fin A.card) :
    (encodeStruct A)[constantAddress V A.card c a.val]? = some (decide (A.const c = a)) := by
  rw [← encodingPosition_constant]
  exact getElem?_encodeStruct_position A (.inr (c, a))

end Complexity.DescriptiveComplexity

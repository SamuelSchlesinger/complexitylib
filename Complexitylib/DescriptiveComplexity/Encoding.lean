/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Structure
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.TakeWhile

/-!
# Encoding finite structures as bit strings

To connect descriptive complexity to the machine model, a finite structure must be
presented as an input to a Turing machine — a bit string. The standard encoding
(for an *ordered* universe `Fin card`) lists, for each relation, its **truth
table**: the values over all tuples in the canonical order. This module builds the
relational part of that encoding and computes its length; it is step 5 (structure
→ bit-string encoding) of the Fagin decomposition on roadmap track L6.

## Main definitions and results

- `DescriptiveComplexity.encodeRel`, `encodeRel_length` — a relation's truth table
  (length `card ^ arity`).
- `DescriptiveComplexity.encodeRels`, `encodeRels_length` — the relational part of
  a structure's encoding, and its total length.
- `DescriptiveComplexity.allTuples`, `encodeRelC` — a **computable** tuple
  enumeration and a computable truth-table encoding (needed for the machine-side
  Fagin bridge).
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- A **computable** enumeration of all `k`-tuples over `Fin card`, built by
    prepending each element to each shorter tuple. -/
def allTuples (card : ℕ) : (k : ℕ) → List (Fin k → Fin card)
  | 0 => [Fin.elim0]
  | k + 1 => (allTuples card k).flatMap (fun t => (List.finRange card).map (fun v => Fin.cons v t))

/-- The enumeration has length `card ^ k`. -/
theorem allTuples_length (card k : ℕ) : (allTuples card k).length = card ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [allTuples, List.length_flatMap, Nat.pow_succ, ← ih]
    simp only [List.length_map, List.length_finRange]
    generalize allTuples card k = L
    induction L with
    | nil => simp
    | cons t rest ihl =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ihl, Nat.succ_mul]; omega

/-- Every tuple appears in the enumeration. -/
theorem mem_allTuples (card k : ℕ) (t : Fin k → Fin card) : t ∈ allTuples card k := by
  induction k with
  | zero => simp only [allTuples, List.mem_singleton]; funext i; exact i.elim0
  | succ k ih =>
    rw [allTuples, List.mem_flatMap]
    refine ⟨Fin.tail t, ih _, ?_⟩
    rw [List.mem_map]
    exact ⟨t 0, List.mem_finRange _, by rw [Fin.cons_self_tail]⟩

/-- A **computable** truth-table encoding of a relation, using `allTuples`. -/
def encodeRelC {card k : Nat} (r : (Fin k → Fin card) → Bool) : List Bool :=
  (allTuples card k).map r

/-- The computable encoding also has length `card ^ k`. -/
theorem encodeRelC_length {card k : Nat} (r : (Fin k → Fin card) → Bool) :
    (encodeRelC r).length = card ^ k := by
  rw [encodeRelC, List.length_map, allTuples_length]

/-- The **computable** relational encoding of a decidable structure: the computable
    truth tables of all its relations, concatenated. -/
def encodeRelsC {V : Vocabulary} (A : DecFinStruct V) : List Bool :=
  (List.finRange V.numRels).flatMap (fun i => encodeRelC (A.rel i))

/-- The computable relational encoding has the expected total length. -/
theorem encodeRelsC_length {V : Vocabulary} (A : DecFinStruct V) :
    (encodeRelsC A).length
      = ((List.finRange V.numRels).map (fun i => A.card ^ V.relArity i)).sum := by
  simp only [encodeRelsC, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  exact encodeRelC_length (A.rel i)

/-- The **full** computable encoding of a decidable structure: the cardinality in
    unary (a block of `card` `true`s terminated by a `false`), followed by the
    relational encoding. The unary prefix makes `card` self-delimiting. -/
def encodeStruct {V : Vocabulary} (A : DecFinStruct V) : List Bool :=
  List.replicate A.card true ++ false :: encodeRelsC A

/-- The cardinality is recoverable from the encoding as the length of the leading
    run of `true`s. -/
theorem encodeStruct_card {V : Vocabulary} (A : DecFinStruct V) :
    ((encodeStruct A).takeWhile id).length = A.card := by
  rw [encodeStruct]; simp

/-- Encode a `Bool`-valued arity-`k` relation on `Fin card` as its **truth table**:
    the list of its values over all `k`-tuples, in the canonical `Fintype` order. -/
noncomputable def encodeRel {card k : Nat} (r : (Fin k → Fin card) → Bool) : List Bool :=
  (Finset.univ : Finset (Fin k → Fin card)).toList.map r

/-- The truth-table encoding of an arity-`k` relation has length `card ^ k`. -/
theorem encodeRel_length {card k : Nat} (r : (Fin k → Fin card) → Bool) :
    (encodeRel r).length = card ^ k := by
  simp only [encodeRel, List.length_map, Finset.length_toList, Finset.card_univ]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The relational part of a decidable structure's encoding: the truth tables of
    all its relations, concatenated. -/
noncomputable def encodeRels {V : Vocabulary} (A : DecFinStruct V) : List Bool :=
  (List.finRange V.numRels).flatMap (fun i => encodeRel (A.rel i))

/-- The relational encoding's length is the sum of the per-relation truth-table
    sizes `card ^ (arity)`. -/
theorem encodeRels_length {V : Vocabulary} (A : DecFinStruct V) :
    (encodeRels A).length
      = ((List.finRange V.numRels).map (fun i => A.card ^ V.relArity i)).sum := by
  simp only [encodeRels, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  exact encodeRel_length (A.rel i)

end DescriptiveComplexity

end Complexity

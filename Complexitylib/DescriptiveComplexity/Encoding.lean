/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Structure
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Encoding finite structures as bit strings

To connect descriptive complexity to the machine model, a finite structure must be
presented as an input to a Turing machine — a bit string. The standard encoding
(for an *ordered* universe `Fin card`) lists, for each relation, its **truth
table**: the values over all tuples in the canonical order. This module builds the
full encoding — the cardinality in unary, the relational truth tables, and one
one-hot block per distinguished constant — and computes its length; it is step 5
(structure → bit-string encoding) of the Fagin decomposition.

## Main definitions and results

- `DescriptiveComplexity.encodeStruct` — the full computable encoding of a decidable
  structure: `card` in unary (terminated by `false`), the relational truth tables,
  then the constant blocks.
- `DescriptiveComplexity.encodeStruct_length`, `encodeStruct_card` — its length, and
  recovery of the cardinality from the unary prefix.
- `DescriptiveComplexity.encodeStruct_of_isRelational` — for constant-free
  vocabularies the encoding is the unary cardinality followed by the relations.
- `DescriptiveComplexity.encodeRel`, `encodeRel_length` — a relation's truth table
  (length `card ^ arity`).
- `DescriptiveComplexity.encodeRels`, `encodeRels_length` — the relational part of
  a structure's encoding, and its total length.
- `DescriptiveComplexity.encodeConstC`, `encodeConstsC`, `encodeConstC_injective` —
  computable one-hot encodings of the distinguished constants; a block determines
  its constant.
- `DescriptiveComplexity.allTuples`, `encodeRelC` — a **computable** tuple
  enumeration and a computable truth-table encoding (needed for the machine-side
  Fagin bridge).
-/


public section

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

/-- Encode a distinguished constant as the truth table of its singleton unary
    relation. The resulting one-hot block has exactly `card` bits. -/
def encodeConstC {card : Nat} (c : Fin card) : List Bool :=
  (List.finRange card).map fun i => i == c

@[simp] theorem encodeConstC_length {card : Nat} (c : Fin card) :
    (encodeConstC c).length = card := by
  simp [encodeConstC]

/-- A one-hot constant block determines the distinguished element. -/
theorem encodeConstC_injective {card : Nat} :
    Function.Injective (@encodeConstC card) := by
  intro a b h
  apply Fin.ext
  have hget := congrArg (fun bits => bits[a.val]?) h
  simp [encodeConstC, Fin.ext_iff] at hget
  exact hget

/-- Encode all distinguished constants as consecutive one-hot blocks. -/
def encodeConstsC {V : Vocabulary} (A : DecFinStruct V) : List Bool :=
  (List.finRange V.numConsts).flatMap fun i => encodeConstC (A.const i)

@[simp] theorem encodeConstsC_length {V : Vocabulary} (A : DecFinStruct V) :
    (encodeConstsC A).length = V.numConsts * A.card := by
  simp [encodeConstsC]

/-- The **full** computable encoding of a decidable structure: the cardinality in
    unary (a block of `card` `true`s terminated by a `false`), followed by the
    relational truth tables and one one-hot block per distinguished constant.
    The unary prefix makes `card` self-delimiting. -/
def encodeStruct {V : Vocabulary} (A : DecFinStruct V) : List Bool :=
  List.replicate A.card true ++ false :: (encodeRelsC A ++ encodeConstsC A)

/-- The cardinality is recoverable from the encoding as the length of the leading
    run of `true`s. -/
theorem encodeStruct_card {V : Vocabulary} (A : DecFinStruct V) :
    ((encodeStruct A).takeWhile id).length = A.card := by
  rw [encodeStruct]; simp

/-- Constant-free vocabularies retain the prior cardinality-plus-relations wire
    format. -/
theorem encodeStruct_of_isRelational {V : Vocabulary} (A : DecFinStruct V)
    (hV : V.IsRelational) :
    encodeStruct A = List.replicate A.card true ++ false :: encodeRelsC A := by
  have hempty : encodeConstsC A = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [encodeConstsC_length]
    unfold Vocabulary.IsRelational at hV
    simp [hV]
  simp [encodeStruct, hempty]

/-- The full encoding has one unary cardinality block, all relation tables, and
    one `card`-bit block for each constant symbol. -/
theorem encodeStruct_length {V : Vocabulary} (A : DecFinStruct V) :
    (encodeStruct A).length =
      A.card + 1 +
        ((List.finRange V.numRels).map (fun i => A.card ^ V.relArity i)).sum +
          V.numConsts * A.card := by
  simp only [encodeStruct, List.length_append, List.length_replicate, List.length_cons,
    encodeRelsC_length, encodeConstsC_length]
  omega

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

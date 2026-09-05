/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Basic

/-!
# Fixed-length bit strings and lists

Circuits consume fixed-length functions `BitString n = Fin n → Bool`, while
machine languages consume `List Bool`. This module makes `List.ofFn` the
canonical serialization and provides round-trip lemmas in both directions.

The variable-length equivalence is already available from Mathlib as
`List.equivSigmaTuple : List Bool ≃ Σ n, BitString n`.
-/


@[expose] public section

namespace Complexity

namespace BitString

/-- Extend a fixed-length bit string to a total assignment by setting every
out-of-range variable to `false`. This is the canonical semantic bridge from
typed Boolean functions to formula and branching-program syntax. -/
def toTotal (x : BitString n) : ℕ → Bool :=
  fun i => if h : i < n then x ⟨i, h⟩ else false

/-- The total extension agrees with the original bit string on every
in-range index. -/
@[simp] theorem toTotal_apply (x : BitString n) (i : Fin n) :
    x.toTotal i.val = x i := by
  simp [toTotal, i.isLt]

/-- An explicit natural index below the arity is read from the original bit
string by the total extension. -/
theorem toTotal_of_lt (x : BitString n) (i : ℕ) (h : i < n) :
    x.toTotal i = x ⟨i, h⟩ := by
  simp [toTotal, h]

/-- Every out-of-range index is `false` in the canonical total extension. -/
theorem toTotal_of_le (x : BitString n) (i : ℕ) (h : n ≤ i) :
    x.toTotal i = false := by
  simp [toTotal, Nat.not_lt.mpr h]

/-- Serialize a fixed-length bit string in increasing index order. -/
def toList (x : BitString n) : List Bool :=
  List.ofFn x

/-- Read a list of the specified length as a fixed-length bit string. -/
def ofList (xs : List Bool) {n : ℕ} (h : xs.length = n) : BitString n :=
  fun i => xs.get (Fin.cast h.symm i)

/-- Serialization preserves length: `toList` of an `n`-bit string has length `n`. -/
@[simp] theorem length_toList (x : BitString n) : x.toList.length = n := by
  simp [toList]

/-- Indexing into the serialized list agrees with the original bit string: `x.toList[i] = x i`. -/
@[simp] theorem getElem_toList (x : BitString n) (i : Fin n) :
    x.toList[i.val]'(by rw [length_toList]; exact i.isLt) = x i := by
  simp [toList]

/-- Round trip, list side: serializing `ofList xs h` recovers the original list `xs`. -/
@[simp] theorem toList_ofList (xs : List Bool) {n : ℕ} (h : xs.length = n) :
    toList (ofList xs h) = xs := by
  subst n
  exact List.ofFn_get xs

/-- Round trip, bit-string side: deserializing `toList x` recovers the original bit string `x`. -/
@[simp] theorem ofList_toList (x : BitString n) :
    ofList (toList x) (length_toList x) = x := by
  funext i
  exact List.get_ofFn x _

/-- Serialization is injective: two bit strings have equal `toList` iff they are equal. -/
@[simp] theorem toList_inj {x y : BitString n} : x.toList = y.toList ↔ x = y :=
  List.ofFn_inj

/-- Serialization commutes with pointwise maps: `toList (f ∘ x) = x.toList.map f`. -/
@[simp] theorem toList_map (f : Bool → Bool) (x : BitString n) :
    toList (fun i => f (x i)) = x.toList.map f :=
  List.ofFn_comp' x f

/-- Serialization sends `Fin.append` to list append: `toList (x ++ y) = x.toList ++ y.toList`. -/
@[simp] theorem toList_append (x : BitString m) (y : BitString n) :
    toList (Fin.append x y) = x.toList ++ y.toList := by
  change List.ofFn (Fin.append x y) = List.ofFn x ++ List.ofFn y
  exact List.ofFn_fin_append x y

end BitString

end Complexity

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.DataScan
public import Complexitylib.Classes.PCP.Internal.SubsetNP
public import Complexitylib.Classes.PCP.Internal.CoinEnum

/-!
# Reading a verifier's query list

A `PCPVerifier` hands over its query positions only as an encoded list — that is
what `positions_mem` provides, and it is all a polynomial-time algorithm can
have, since a single position may be astronomically large. This module reads
individual entries back out of that encoding with the bracket scan.

Two facts make the reading enough for everything downstream. A position is
recovered as its own serialization, so two positions can be compared by
comparing strings, with no arithmetic on the values; and an index past the end
of the list is recognisable, because every serialization is non-empty.

## Main definitions

- `Complexity.posInner` — the encoding stripped of its outer brackets
- `Complexity.posAt`, `Complexity.posCount` — one entry, and how many there are

## Main results

- `Complexity.posAt_eq`, `Complexity.posCount_eq` — what the scan reads
- `Complexity.posAt_eq_iff` — comparing entries compares positions
-/

@[expose] public section

namespace Complexity

/-- The serialized entries of an encoded list, with the outer brackets removed:
the string the scan consumes. -/
def posInner (e : List Bool) : List Bool := (e.drop 1).take (e.length - 2)

theorem posInner_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => posInner (a z)) ∈ FP := by
  have hdrop : (fun z => dropOne (a z)) ∈ FP := dropOneFn_mem_FP ha
  have hlen : (fun z => List.replicate ((a z).length - 2) false) ∈ FP := by
    have h1 : (fun z => dropOne (dropOne (a z))) ∈ FP := dropOneFn_mem_FP hdrop
    have := zeroBlockFn_mem_FP h1
    refine mem_FP_of_eq this fun z => ?_
    congr 1
    rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega
  have := Cobham.takeLenFn_mem_FP hlen hdrop
  refine mem_FP_of_eq this fun z => ?_
  rw [posInner, dropOne, List.length_replicate]

/-- The `i`-th entry of an encoded list, as its own serialization. -/
noncomputable def posAt (e : List Bool) (i : ℕ) : List Bool :=
  DataScan.childOf DataScan.scanPoly (DataScan.scanArg i (posInner e))

/-- How many entries an encoded list has, in unary. -/
noncomputable def posCount (e : List Bool) : List Bool :=
  DataScan.childCount DataScan.scanPoly (DataScan.scanArg 0 (posInner e))

theorem posAt_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => posAt (b z) (a z).length) ∈ FP := by
  have harg : (fun z => DataScan.scanArg (a z).length (posInner (b z))) ∈ FP :=
    DataScan.scanArg_mem_FP ha (posInner_mem_FP hb)
  have := mem_FP_comp harg (DataScan.childOf_mem_FP DataScan.scanPoly)
  exact this

theorem posCount_mem_FP {b : List Bool → List Bool} (hb : b ∈ FP) :
    (fun z => posCount (b z)) ∈ FP := by
  have harg : (fun z => DataScan.scanArg (([] : List Bool)).length (posInner (b z))) ∈ FP :=
    DataScan.scanArg_mem_FP (constFn_mem_FP []) (posInner_mem_FP hb)
  have := mem_FP_comp harg (DataScan.childCount_mem_FP DataScan.scanPoly)
  exact this

/-! ### What the scan reads -/

variable {α : Type} [DataEncode α]

theorem posInner_bitstringEncode (l : List α) :
    posInner (DataEncode.bitstringEncode l)
      = ((l.map DataEncode.encode).map Data.toBits).flatten := by
  rw [posInner, DataEncode.bitstringEncode_def,
    show DataEncode.encode l = Data.l (l.map DataEncode.encode) from rfl]
  exact DataScan.inner_toBits _

theorem posCount_eq (l : List α) :
    posCount (DataEncode.bitstringEncode l) = List.replicate l.length true := by
  rw [posCount, posInner_bitstringEncode, DataScan.childCount_flatten]
  simp

theorem posAt_eq (l : List α) (i : ℕ) :
    posAt (DataEncode.bitstringEncode l) i
      = (((l.map DataEncode.encode)[i]?).map Data.toBits).getD [] := by
  rw [posAt, posInner_bitstringEncode, DataScan.child_flatten]

theorem posAt_eq_of_lt {l : List α} {i : ℕ} (h : i < l.length) :
    posAt (DataEncode.bitstringEncode l) i
      = DataEncode.bitstringEncode (l[i]'h) := by
  rw [posAt_eq, List.getElem?_map, List.getElem?_eq_getElem (by simpa using h)]
  rfl

theorem posAt_eq_nil {l : List α} {i : ℕ} (h : l.length ≤ i) :
    posAt (DataEncode.bitstringEncode l) i = [] := by
  rw [posAt_eq, List.getElem?_map, List.getElem?_eq_none (by simpa using h)]
  rfl

theorem posAt_ne_nil {l : List α} {i : ℕ} (h : i < l.length) :
    posAt (DataEncode.bitstringEncode l) i ≠ [] := by
  rw [posAt_eq_of_lt h, DataEncode.bitstringEncode_def]
  cases hd : DataEncode.encode (l[i]'h) with
  | l xs =>
      rw [Data.toBits_l]
      simp

/-- **Concatenating encoded lists.** The encoding of an append is the two inner
parts, one after the other, inside a fresh pair of brackets. -/
theorem bitstringEncode_append (l₁ l₂ : List α) :
    DataEncode.bitstringEncode (l₁ ++ l₂)
      = false :: (posInner (DataEncode.bitstringEncode l₁)
          ++ posInner (DataEncode.bitstringEncode l₂)) ++ [true] := by
  rw [posInner_bitstringEncode, posInner_bitstringEncode,
    DataEncode.bitstringEncode_def,
    show DataEncode.encode (l₁ ++ l₂)
      = Data.l ((l₁ ++ l₂).map DataEncode.encode) from rfl,
    Data.toBits_l, List.map_append, List.map_append, List.flatten_append]
  simp

/-- **Comparing entries compares positions.** The scan returns each entry's own
serialization, and that serialization determines the entry. -/
theorem posAt_eq_iff {l l' : List α} {i i' : ℕ} (h : i < l.length) (h' : i' < l'.length) :
    posAt (DataEncode.bitstringEncode l) i = posAt (DataEncode.bitstringEncode l') i'
      ↔ (l[i]'h) = (l'[i']'h') := by
  rw [posAt_eq_of_lt h, posAt_eq_of_lt h']
  exact ⟨fun hh => DataEncode.bitstringEncode_injective hh, fun hh => by rw [hh]⟩

end Complexity

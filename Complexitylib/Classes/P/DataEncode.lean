/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.DataEncode.Defs
public import Complexitylib.Encoding.DataEncode
public import Complexitylib.Encoding.Pairing
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.Bridge
import Complexitylib.Classes.P.NatCodes
import Complexitylib.Classes.P.PairWithInput
import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.Unary
import Complexitylib.Classes.P.DataEncode.Internal.Scan
import Complexitylib.Classes.P.DataEncode.Internal.Write

/-!
# Writing and reading encodings in polynomial time

A polynomial-time construction that hands its result to a `DataEncode` consumer,
such as a verifier reading a list of query positions, has to write the
`DataEncode.bitstringEncode` of that result; one that is handed such a list has
to read its entries back. This module shows that both are polynomial-time.

*Writing.* A bit list is encoded as the encodings of its bits between two
brackets, and writing that is a fold over the list (`encodeList_mem_FP`). A
number is encoded as its minimal binary expansion `Nat.bits`, so writing a
polynomial-time number's encoding is writing its expansion (`bits_mem_FP`) and
then encoding that list (`natEncode_mem_FP`). No width has to be supplied. A list
of numbers given by a polynomial-time length and a polynomial-time rule for each
entry is written the same way, entry by entry (`natListEncode_mem_FP`).

*Reading.* The `i`-th entry of an encoded list (`posAt`) and the number of
entries (`posCount`) are read by one left-to-right bracket scan, which is a
polynomial-time fold (`posAt_mem_FP`, `posCount_mem_FP`). On the encoding of a
list, the scan returns each entry's own encoding (`posAt_eq_of_lt`), so two
entries can be compared by comparing strings (`posAt_eq_iff`), and an index past
the end reads as the empty string (`posAt_eq_nil`), which no entry's encoding is
(`posAt_ne_nil`).

## Main results

- `encodeList_mem_FP` — writing the encoding of a bit list is polynomial-time
- `natEncode_mem_FP` — writing the encoding of a polynomial-time number is
  polynomial-time
- `natListEncode_mem_FP` — so is writing a list of polynomial-time numbers
- `posInner_mem_FP`, `posAt_mem_FP`, `posCount_mem_FP` — reading an encoded list
  is polynomial-time
- `posCount_eq`, `posAt_eq_of_lt`, `posAt_eq_nil`, `posAt_ne_nil`,
  `posAt_eq_iff` — what the reading returns on an encoded list
-/

public section

namespace Complexity

/-! ## Writing -/

/-- **Writing the encoding of a bit list is polynomial-time.** If `a ∈ FP`, then
so is `z ↦ DataEncode.bitstringEncode (a z)`. -/
theorem encodeList_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => DataEncode.bitstringEncode (a z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.appendFn_mem_FP (encodeBody_mem_FP ha)
    (constFn_mem_FP [true])) (Cobham.cons_mem_FP false))
    fun z => (bitstringEncode_eq_encodeBody (a z)).symm

/-- **Writing the encoding of a polynomial-time number is polynomial-time.** If
`n` is a polynomial-time number, then `z ↦ DataEncode.bitstringEncode (n z)` is
in `FP`: a number is encoded as its minimal binary expansion. -/
theorem natEncode_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => DataEncode.bitstringEncode (n z)) ∈ FP :=
  encodeList_mem_FP (bits_mem_FP hn)

/-- **Writing the encoding of a list of polynomial-time numbers is
polynomial-time.** If the length `n` and the entries `v` are polynomial-time
numbers, with entry `i` of the list for `z` computed from `pair z (1^i)`, then
writing the encoding of `[v z 0, …, v z (n z - 1)]` is polynomial-time. -/
theorem natListEncode_mem_FP {n : List Bool → ℕ} {v : List Bool → ℕ → ℕ}
    (hn : UnaryFn n) (hv : UnaryFn fun w => v (pairFst w) (pairSnd w).length) :
    (fun z => DataEncode.bitstringEncode ((List.range (n z)).map (v z))) ∈ FP := by
  refine mem_FP_of_eq (mem_FP_comp (mem_FP_pairWithInput hn)
    (listEncFn_mem_FP (natEncode_mem_FP hv))) fun z => ?_
  rw [Function.comp_apply]
  refine listEncFn_eq_bitstringEncode _ ?_ fun i hi => ?_
  · rw [pairFst_pair, List.length_replicate, List.length_map, List.length_range]
  · simp only [pairSnd_pair, pairFst_pair, List.length_replicate, List.getElem_map,
      List.getElem_range]

/-! ## Reading -/

/-- Stripping the outer brackets of a polynomial-time string is
polynomial-time. -/
theorem posInner_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => posInner (a z)) ∈ FP :=
  mem_FP_of_eq (Cobham.takeLenFn_mem_FP ((UnaryFn.length ha).sub (UnaryFn.const 2))
    (dropOneFn_mem_FP ha)) fun z => by rw [posInner, List.length_replicate]; rfl

/-- **Reading an entry of an encoded list is polynomial-time**: the entry of
`b z` at the index `|a z|`. -/
theorem posAt_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => posAt (b z) (a z).length) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (DataScan.scan_mem_FP ha (posInner_mem_FP hb))
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP)) fun z => by
    simp only [Function.comp_apply, DataScan.pack, pairSnd_pair, posAt]

/-- **Counting the entries of an encoded list is polynomial-time.** -/
theorem posCount_mem_FP {b : List Bool → List Bool} (hb : b ∈ FP) :
    (fun z => posCount (b z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (DataScan.scan_mem_FP (constFn_mem_FP []) (posInner_mem_FP hb))
    (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)) fun z => by
    simp only [Function.comp_apply, DataScan.pack, pairSnd_pair, pairFst_pair, posCount,
      List.length_nil]

/-! ## What the reading returns -/

variable {α : Type} [DataEncode α]

/-- Without its outer brackets, the encoding of a list is its entries' encodings,
one after another. -/
theorem posInner_bitstringEncode (l : List α) :
    posInner (DataEncode.bitstringEncode l)
      = ((l.map DataEncode.encode).map Data.toBits).flatten := by
  rw [posInner, DataEncode.bitstringEncode_def,
    show DataEncode.encode l = Data.l (l.map DataEncode.encode) from rfl, Data.toBits_l]
  simp

/-- The number of entries of an encoded list is its length. -/
theorem posCount_eq (l : List α) :
    posCount (DataEncode.bitstringEncode l) = List.replicate l.length true := by
  rw [posCount, posInner_bitstringEncode, DataScan.runSpec_inner, List.length_map]

/-- The `i`-th entry of an encoded list is the `i`-th entry's encoding, or
nothing past the end. -/
theorem posAt_eq (l : List α) (i : ℕ) :
    posAt (DataEncode.bitstringEncode l) i
      = (((l.map DataEncode.encode)[i]?).map Data.toBits).getD [] := by
  rw [posAt, posInner_bitstringEncode, DataScan.runSpec_inner]

/-- **An entry within range reads as its encoding.** -/
theorem posAt_eq_of_lt {l : List α} {i : ℕ} (h : i < l.length) :
    posAt (DataEncode.bitstringEncode l) i
      = DataEncode.bitstringEncode (l[i]'h) := by
  rw [posAt_eq, List.getElem?_map, List.getElem?_eq_getElem (by simpa using h)]
  rfl

/-- **An index past the end reads as the empty string.** -/
theorem posAt_eq_nil {l : List α} {i : ℕ} (h : l.length ≤ i) :
    posAt (DataEncode.bitstringEncode l) i = [] := by
  rw [posAt_eq, List.getElem?_map, List.getElem?_eq_none (by simpa using h)]
  rfl

/-- **An entry within range never reads as the empty string.** -/
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
  rw [posInner_bitstringEncode, posInner_bitstringEncode, DataEncode.bitstringEncode_append,
    List.map_map, List.map_map, List.cons_append]
  rfl

/-- **Comparing entries compares values.** The scan returns each entry's own
encoding, and that encoding determines the entry. -/
theorem posAt_eq_iff {l l' : List α} {i i' : ℕ} (h : i < l.length) (h' : i' < l'.length) :
    posAt (DataEncode.bitstringEncode l) i = posAt (DataEncode.bitstringEncode l') i'
      ↔ (l[i]'h) = (l'[i']'h') := by
  rw [posAt_eq_of_lt h, posAt_eq_of_lt h']
  exact ⟨fun hh => DataEncode.bitstringEncode_injective hh, fun hh => by rw [hh]⟩

end Complexity

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH.SipserLautemann.Covering

/-!
# Bitstring codecs for seeds and shift tuples

The Lautemann characterization quantifies over seeds `Fin m → Bool` and over
tuples of shifts `Fin t → Fin m → Bool`, while the polynomial hierarchy
quantifies over bitstrings. This file provides the two codecs and their
round-trip lemmas: `listOfSeed`/`seedOfList` for a single seed, and
`listOfShifts`/`shiftsOfList` for a tuple, flattened in row-major order.

Decoding is total — out-of-range positions read as `false` — so a decoder is
available on every bitstring, and the length equations pin down the well-formed
encodings.
-/

@[expose] public section

namespace Complexity

namespace Lautemann

variable {t m : ℕ}

/-- Encode a seed as a bitstring, one bit per position. -/
def listOfSeed (s : Fin m → Bool) : List Bool := (List.finRange m).map s

/-- Decode a bitstring as a seed, reading out-of-range positions as `false`. -/
def seedOfList (m : ℕ) (r : List Bool) : Fin m → Bool := fun j => r.getD j.val false

@[simp] theorem length_listOfSeed (s : Fin m → Bool) : (listOfSeed s).length = m := by
  simp [listOfSeed]

/-- Reading an encoded seed at an in-range position returns that bit. -/
theorem getD_listOfSeed (s : Fin m → Bool) (idx : ℕ) (h : idx < m) :
    (listOfSeed s).getD idx false = s ⟨idx, h⟩ := by
  have hlen : idx < (listOfSeed s).length := by simpa using h
  rw [List.getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp [listOfSeed]

@[simp] theorem seedOfList_listOfSeed (s : Fin m → Bool) :
    seedOfList m (listOfSeed s) = s := by
  funext j
  simpa [seedOfList] using getD_listOfSeed s j.val j.isLt

/-- Flatten a tuple of shifts into a single seed of length `t * m`, in
row-major order. -/
def flattenShifts (u : Fin t → Fin m → Bool) : Fin (t * m) → Bool := fun kk =>
  if h : 0 < m then
    u ⟨kk.val / m, (Nat.div_lt_iff_lt_mul h).mpr kk.isLt⟩ ⟨kk.val % m, Nat.mod_lt _ h⟩
  else false

/-- Encode a tuple of shifts as a bitstring of length `t * m`. -/
def listOfShifts (u : Fin t → Fin m → Bool) : List Bool := listOfSeed (flattenShifts u)

/-- Decode a bitstring as a tuple of shifts, reading out-of-range positions as
`false`. -/
def shiftsOfList (t m : ℕ) (w : List Bool) : Fin t → Fin m → Bool :=
  fun i j => w.getD (i.val * m + j.val) false

@[simp] theorem length_listOfShifts (u : Fin t → Fin m → Bool) :
    (listOfShifts u).length = t * m := by
  simp [listOfShifts]

@[simp] theorem shiftsOfList_listOfShifts (u : Fin t → Fin m → Bool) :
    shiftsOfList t m (listOfShifts u) = u := by
  funext i j
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact absurd j.isLt (by omega))
  have hidx : i.val * m + j.val < t * m := by
    have hi : i.val + 1 ≤ t := i.isLt
    calc i.val * m + j.val < i.val * m + m := by omega
      _ = (i.val + 1) * m := by ring
      _ ≤ t * m := Nat.mul_le_mul_right _ hi
  have hdiv : (i.val * m + j.val) / m = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hmod : (i.val * m + j.val) % m = j.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  simp only [shiftsOfList, listOfShifts]
  rw [getD_listOfSeed _ _ hidx]
  simp only [flattenShifts, dite_eq_left hm]
  congr 1 <;> [exact Fin.ext hdiv; exact Fin.ext hmod]

end Lautemann

end Complexity

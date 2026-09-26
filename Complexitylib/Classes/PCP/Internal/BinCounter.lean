/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchBits
public import Complexitylib.Classes.Containments.Internal.FPBridge
public import Complexitylib.Classes.Containments.Internal.BinArith
public import Complexitylib.Classes.Containments.Internal.WitnessEnum

/-!
# A binary counter from a unary index

A polynomial-time loop receives its counter in unary, since that is the form a
loop bound takes. This module turns such an index into fixed-width binary: the
width-preserving counter of `SavitchBits` is incremented that many times,
starting from all zeros.

Nothing here is arithmetic on the index. `bumpBits` is the width-preserving
increment already proved polynomial-time for Savitch's theorem, and iterating a
polynomial-time step a polynomial number of times is `iterate_mem_FP`.

## Main definitions

- `Complexity.coinStr` — the counter after that many increments

## Main results

- `Complexity.coinStr_eq` — below the wrap-around, it is `bitsOfLenLE`
- `Complexity.coinStr_mem_FP` — in polynomial time, for any index
-/

@[expose] public section

namespace Complexity

/-- A block of zeros as wide as a computed string. -/
theorem zeroBlockFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => List.replicate (a z).length false) ∈ FP :=
  unFn_mem_FP (g := fun s => List.replicate s.length false)
    (Cobham.zeroBlockFn (Cobham.proj 0)) ha

theorem bumpBits_mem_FP : bumpBits ∈ FP := by
  have h := bumpCodeFn_mem_FP id_mem_FP
  refine mem_FP_of_eq h fun z => ?_
  simp

theorem length_bumpBits_iterate (n : ℕ) (w : List Bool) :
    (bumpBits^[n] w).length = w.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', bumpBits_length, ih]

/-- The width-`t` counter after `c` increments. Total: past `2 ^ t` it wraps,
which never happens where it is used but keeps the function unconditional. -/
def coinStr (t c : ℕ) : List Bool := bumpBits^[c] (List.replicate t false)

theorem coinStr_eq {t c : ℕ} (h : c < 2 ^ t) : coinStr t c = bitsOfLenLE t c := by
  rw [coinStr, ← bitsOfLenLE_zero t, bumpBits_iterate _ _ h]

/-- **The counter value in polynomial time.** With the width and the index both
supplied in unary, the counter is polynomial-time computable — with no bound on
the index, so that the function is total where a loop guard has not yet been
applied. -/
theorem coinStr_mem_FP {t c : List Bool → ℕ}
    (ht : (fun z => List.replicate (t z) true) ∈ FP)
    (hc : (fun z => List.replicate (c z) true) ∈ FP) :
    (fun z => coinStr (t z) (c z)) ∈ FP := by
  have hinit : (fun z => List.replicate (t z) false) ∈ FP := by
    have := zeroBlockFn_mem_FP ht
    simpa using this
  have hbound : ∀ z : List Bool, ∀ n ≤ (List.replicate (c z) true).length,
      (bumpBits^[n] (List.replicate (t z) false)).length
        ≤ (List.replicate (t z) false).length := fun z n _ =>
    le_of_eq (length_bumpBits_iterate n _)
  have hiter := Cobham.iterate_mem_FP bumpBits_mem_FP hinit hc hinit hbound
  refine mem_FP_of_eq hiter fun z => ?_
  rw [List.length_replicate, coinStr]

end Complexity

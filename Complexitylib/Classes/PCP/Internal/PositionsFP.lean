/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ListEncode

/-!
# A verifier's query list from its positions

`PCPVerifier` asks for the query list in `DataEncode` form, which is not how an
algorithm naturally describes it: an algorithm says "the `i`-th position is
this number". This module bridges the two, so that building a verifier needs
only a polynomial-time rule for each position, given in unary.

The width a number needs is the number itself — every `v` is below `2 ^ v` — so
no logarithms are involved: the same unary value serves as both the value and
the width bound for `natEncodeFn`.

## Main results

- `Complexity.positions_mem_of_unary` — a unary position rule gives
  `positions_mem`
-/

@[expose] public section

namespace Complexity

/-- The encoding of one position, read off a packed argument. -/
noncomputable def posEntryFn (P : List Bool → List Bool) (w : List Bool) : List Bool :=
  natEncodeFn (pair (P w) (P w))

theorem posEntryFn_mem_FP {P : List Bool → List Bool} (hP : P ∈ FP) :
    posEntryFn P ∈ FP := by
  have := mem_FP_comp (Cobham.pairFn_mem_FP hP hP) natEncodeFn_mem_FP
  exact this

theorem posEntryFn_eq {P : List Bool → List Bool} (w : List Bool) :
    posEntryFn P w = DataEncode.bitstringEncode ((P w).length) := by
  rw [posEntryFn, natEncodeFn_eq, pairSnd_pair]
  rw [pairSnd_pair, pairFst_pair]
  exact Nat.lt_two_pow_self

/-- **A unary position rule gives the query list.** If the number of queries and
each query position are polynomial-time computable in unary, then the encoded
query list is polynomial-time computable. -/
theorem positions_mem_of_unary {pos : List Bool → ℕ → ℕ} {cnt : List Bool → ℕ}
    (hcnt : (fun z : List Bool => List.replicate (cnt z) true) ∈ FP)
    {P : List Bool → List Bool} (hP : P ∈ FP)
    (hPspec : ∀ (z : List Bool) (i : ℕ),
      P (pair z (List.replicate i true)) = List.replicate (pos z i) true) :
    ∃ g ∈ FP, ∀ z : List Bool,
      g z = DataEncode.bitstringEncode ((List.range (cnt z)).map (pos z)) := by
  classical
  set E := posEntryFn P with hE
  have hEfp : E ∈ FP := posEntryFn_mem_FP hP
  have hEspec : ∀ (z : List Bool) (i : ℕ),
      E (pair z (List.replicate i true)) = DataEncode.bitstringEncode (pos z i) := by
    intro z i
    rw [hE, posEntryFn_eq, hPspec, List.length_replicate]
  refine ⟨fun z => listEncFn E (pair (List.replicate (cnt z) true) z), ?_, ?_⟩
  · have hpair : (fun z : List Bool => pair (List.replicate (cnt z) true) z) ∈ FP :=
      mem_FP_pairWithInput hcnt
    have := mem_FP_comp hpair (listEncFn_mem_FP hEfp)
    exact this
  · intro z
    refine listEncFn_eq_bitstringEncode _ ?_ ?_
    · rw [pairFst_pair, List.length_replicate, List.length_map, List.length_range]
    · intro i hi
      rw [pairSnd_pair, hEspec]
      congr 1
      rw [List.getElem_map, List.getElem_range]

end Complexity

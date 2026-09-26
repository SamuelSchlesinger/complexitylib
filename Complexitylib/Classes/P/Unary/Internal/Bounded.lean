/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Classes.P.Range.Defs
public import Complexitylib.Classes.P.Iterate
public import Complexitylib.Classes.P.PairWithInput
public import Complexitylib.Classes.Containments.Internal.FPBridge
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Polynomial-time numbers and tests — loops

The facts behind the loop rules of `Complexitylib.Classes.P.Unary`: a loop on a
number, run as a loop on strings that carry the input alongside the number; the
maximum of `Complexitylib.Classes.P.Range` as a `Finset.sup`; and the first
index at which a test passes as a count.

## Contents

- `unaryLoopStep`, `unaryLoopStep_iterate` — one round of a loop on a number,
  and what the rounds compute
- `unaryFn_iterate_internal` — the loop is polynomial-time while its values stay
  below a polynomial-time bound
- `maxOver_eq_sup` — the maximum over a range is a `Finset.sup`
- `findIdx_range_eq_card` — the first index at which a test passes counts the
  indices before which it never passes
-/

@[expose] public section

namespace Complexity

/-! ## A loop on a number -/

/-- One round of the loop that updates a number `x` by `x ↦ s z x`, on
`pair (1^x) z`. The input `z` rides along, so that the update can read it. -/
def unaryLoopStep (s : List Bool → ℕ → ℕ) (st : List Bool) : List Bool :=
  pair (List.replicate (s (pairSnd st) (pairFst st).length) true) (pairSnd st)

/-- `j` rounds of the loop apply the update `j` times. -/
theorem unaryLoopStep_iterate (s : List Bool → ℕ → ℕ) (z : List Bool) (x : ℕ) :
    ∀ j, (unaryLoopStep s)^[j] (pair (List.replicate x true) z)
      = pair (List.replicate ((s z)^[j] x) true) z
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', unaryLoopStep_iterate s z x j, unaryLoopStep,
        pairFst_pair, pairSnd_pair, List.length_replicate, Function.iterate_succ_apply']

/-- **A loop on a number is polynomial-time** while its values stay below a
polynomial-time bound. The update reads `pair z (1^x)`. -/
theorem unaryFn_iterate_internal {s : List Bool → ℕ → ℕ} {a k B : List Bool → ℕ}
    (hs : UnaryFn fun w => s (pairFst w) (pairSnd w).length) (ha : UnaryFn a)
    (hk : UnaryFn k) (hB : UnaryFn B) (hbound : ∀ z, ∀ j ≤ k z, (s z)^[j] (a z) ≤ B z) :
    UnaryFn fun z => (s z)^[k z] (a z) := by
  have hswap : (fun st : List Bool => pair (pairSnd st) (pairFst st)) ∈ FP :=
    Cobham.pairFn_mem_FP Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP
  have hs' : (fun st : List Bool =>
      List.replicate (s (pairSnd st) (pairFst st).length) true) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hswap hs) fun st => by
      simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  have hF : unaryLoopStep s ∈ FP := Cobham.pairFn_mem_FP hs' Cobham.sndBlock_mem_FP
  obtain ⟨p, hp⟩ := Cobham.output_length_poly_of_mem_FP hB
  have hpoly : PolyBound fun m => 2 * p.eval m + 2 + m :=
    (((PolyBound.const 2).mul (PolyBound.eval p)).add (PolyBound.const 2)).add PolyBound.id
  have hiter := iterate_mem_FP_of_polyBound hF (mem_FP_pairWithInput ha) hk hpoly
    fun z j hj => by
      rw [List.length_replicate] at hj
      rw [unaryLoopStep_iterate, pair_length, List.length_replicate]
      have h1 := hbound z j hj
      have h2 := hp z
      rw [List.length_replicate] at h2
      omega
  refine mem_FP_of_eq (mem_FP_comp hiter Cobham.fstBlock_mem_FP) fun z => ?_
  rw [Function.comp_apply, List.length_replicate, unaryLoopStep_iterate, pairFst_pair]

/-! ## The maximum -/

/-- The maximum over a range, as a `Finset.sup`. -/
theorem maxOver_eq_sup (f : List Bool → List Bool) (z : List Bool) :
    ∀ n, maxOver f z n
      = (Finset.range n).sup fun i => (f (pair z (List.replicate i true))).length
  | 0 => rfl
  | n + 1 => by
      rw [maxOver, maxOver_eq_sup f z n, Finset.range_add_one, Finset.sup_insert,
        max_comm]

/-! ## The first index -/

/-- **The first index at which a test passes is a count**: the number of indices
`j` such that the test fails at every index up to `j`. -/
theorem findIdx_range_eq_card (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    (List.range n).findIdx (fun i => decide (q i))
      = ((Finset.range n).filter
          fun j => ((Finset.range (j + 1)).filter q).card = 0).card := by
  set m := (List.range n).findIdx (fun i => decide (q i)) with hm
  have hmn : m ≤ n := by
    have := List.findIdx_le_length (p := fun i => decide (q i)) (xs := List.range n)
    rwa [List.length_range] at this
  have hfilter : (Finset.range n).filter
      (fun j => ((Finset.range (j + 1)).filter q).card = 0) = Finset.range m := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, hm, List.lt_findIdx_iff]
    constructor
    · rintro ⟨hj, hnone⟩
      refine ⟨by rwa [List.length_range], fun k hk => ?_⟩
      rw [List.getElem_range, decide_eq_false_iff_not]
      exact hnone (Finset.mem_range.mpr (by omega))
    · rintro ⟨hj, hnone⟩
      rw [List.length_range] at hj
      refine ⟨hj, fun k hk => ?_⟩
      have hk' : k ≤ j := by rw [Finset.mem_range] at hk; omega
      have := hnone k hk'
      rwa [List.getElem_range, decide_eq_false_iff_not] at this
  rw [hfilter, Finset.card_range]

end Complexity

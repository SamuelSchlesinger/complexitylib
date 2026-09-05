/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# Searching a block-aligned string for a block

⚠️ Unreviewed by Bolton

A search that keeps its visited set as a run of fixed-width records must be able
to ask whether a record is already there. This file supplies that test as a
polynomial-time function: one scan, one block per step, accumulating a flag.

The scan is written as an iteration rather than a recursion, because that is the
shape `Cobham.iterate_mem_FP` consumes — the state is a packed
`pair (pair u f) rest`, and one step compares `u` against the leading block of
`rest` and drops it.

## Main definitions

- `Complexity.scanStep` — one step of the scan, on the unpacked state
- `Complexity.memStep` — the same on the packed state
- `Complexity.memFlag` — the verdict of a full scan

## Main results

- `Complexity.memStep_iterate` — the packed iteration tracks the unpacked one
- `Complexity.memFlag_eq_true_iff` — what the scan decides
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## The scan, on the unpacked state -/

/-- One step of a scan that folds a per-record test into a flag. A remainder
shorter than one record is a dead end, so the state stands still. -/
def anyStepPair (R : List Bool) (f : List Bool → List Bool)
    (s : List Bool × List Bool) : List Bool × List Bool :=
  if R.length ≤ s.2.length then (orBit s.1 (f (s.2.take R.length)), s.2.drop R.length)
  else s

theorem anyStepPair_pos (R : List Bool) (f : List Bool → List Bool)
    (s : List Bool × List Bool) (h : R.length ≤ s.2.length) :
    anyStepPair R f s = (orBit s.1 (f (s.2.take R.length)), s.2.drop R.length) :=
  ite_eq_left h

theorem anyStepPair_neg (R : List Bool) (f : List Bool → List Bool)
    (s : List Bool × List Bool) (h : ¬ R.length ≤ s.2.length) : anyStepPair R f s = s :=
  ite_eq_right h

/-- The flag component of a scan is a flag. -/
theorem anyStepPair_flag (R : List Bool) {f : List Bool → List Bool}
    (hf : ∀ z, f z = [true] ∨ f z = [false]) {s : List Bool × List Bool}
    (hs : s.1 = [true] ∨ s.1 = [false]) (n : ℕ) :
    ((anyStepPair R f)^[n] s).1 = [true] ∨ ((anyStepPair R f)^[n] s).1 = [false] := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      refine ih ?_
      rw [anyStepPair]
      split
      · exact orBit_flag hs (hf _)
      · exact hs

/-- The remainder never grows. -/
theorem anyStepPair_rest_length (R : List Bool) (f : List Bool → List Bool)
    (s : List Bool × List Bool) (n : ℕ) :
    ((anyStepPair R f)^[n] s).2.length ≤ s.2.length := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      refine le_trans (ih (anyStepPair R f s)) ?_
      rw [anyStepPair]
      split
      · simp
      · exact le_rfl

/-- Dropping one record shifts the record index. -/
theorem blockAt_drop (R z : List Bool) (i : ℕ) :
    blockAt R (z.drop R.length) i = blockAt R z (i + 1) := by
  rw [blockAt, blockAt, List.drop_drop]
  congr 2
  ring

/-- **A scan fires exactly when the test fires on one of the records.** -/
theorem anyStepPair_flag_eq_true_iff (R : List Bool) {f : List Bool → List Bool}
    (hf : ∀ z, f z = [true] ∨ f z = [false]) (s : List Bool × List Bool)
    (hs : s.1 = [true] ∨ s.1 = [false]) (n : ℕ) :
    ((anyStepPair R f)^[n] s).1 = [true] ↔
      s.1 = [true] ∨ ∃ i < n, i * R.length + R.length ≤ s.2.length ∧
        f (blockAt R s.2 i) = [true] := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      have hstep : (anyStepPair R f s).1 = [true] ∨ (anyStepPair R f s).1 = [false] := by
        rw [anyStepPair]
        split
        · exact orBit_flag hs (hf _)
        · exact hs
      rw [Function.iterate_succ_apply, ih (anyStepPair R f s) hstep]
      by_cases hle : R.length ≤ s.2.length
      · have hfst : (anyStepPair R f s).1 = orBit s.1 (f (s.2.take R.length)) := by
          rw [anyStepPair, ite_eq_left hle]
        have hsnd : (anyStepPair R f s).2 = s.2.drop R.length := by
          rw [anyStepPair, ite_eq_left hle]
        rw [hfst, hsnd, orBit_eq_true_iff hs (hf _)]
        constructor
        · rintro ((h | h) | ⟨i, hi, hlen, hblk⟩)
          · exact Or.inl h
          · refine Or.inr ⟨0, by omega, by omega, ?_⟩
            rw [blockAt, Nat.zero_mul, List.drop_zero]
            exact h
          · have hmul : (i + 1) * R.length = i * R.length + R.length := by ring
            rw [List.length_drop] at hlen
            refine Or.inr ⟨i + 1, by omega, by omega, ?_⟩
            rw [← blockAt_drop]
            exact hblk
        · rintro (h | ⟨i, hi, hlen, hblk⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.eq_zero_or_pos i with rfl | hipos
            · refine Or.inl (Or.inr ?_)
              rw [blockAt, Nat.zero_mul, List.drop_zero] at hblk
              exact hblk
            · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
              have hmul : (j + 1) * R.length = j * R.length + R.length := by ring
              refine Or.inr ⟨j, by omega, ?_, ?_⟩
              · rw [List.length_drop]
                omega
              · rw [blockAt_drop]
                exact hblk
      · have hfix : anyStepPair R f s = s := by rw [anyStepPair, ite_eq_right hle]
        rw [hfix]
        constructor
        · rintro (h | ⟨i, hi, hlen, hblk⟩)
          · exact Or.inl h
          · exact Or.inr ⟨i, by omega, hlen, hblk⟩
        · rintro (h | ⟨i, hi, hlen, hblk⟩)
          · exact Or.inl h
          · have : R.length ≤ s.2.length := le_trans (by omega) hlen
            omega

/-- One step of the membership scan: compare `u` against the leading record. -/
def scanStep (R u : List Bool) : List Bool × List Bool → List Bool × List Bool :=
  anyStepPair R (eqFlag u)

theorem scanStep_flag (R u : List Bool) {s : List Bool × List Bool}
    (hs : s.1 = [true] ∨ s.1 = [false]) (n : ℕ) :
    ((scanStep R u)^[n] s).1 = [true] ∨ ((scanStep R u)^[n] s).1 = [false] :=
  anyStepPair_flag R (fun z => eqFlag_flag u z) hs n

theorem scanStep_rest_length (R u : List Bool) (s : List Bool × List Bool) (n : ℕ) :
    ((scanStep R u)^[n] s).2.length ≤ s.2.length :=
  anyStepPair_rest_length R _ s n

/-- **The scan finds a record exactly when one matches.** -/
theorem scanStep_flag_eq_true_iff (R u : List Bool) (s : List Bool × List Bool)
    (hs : s.1 = [true] ∨ s.1 = [false]) (n : ℕ) :
    ((scanStep R u)^[n] s).1 = [true] ↔
      s.1 = [true] ∨ ∃ i < n, i * R.length + R.length ≤ s.2.length ∧
        blockAt R s.2 i = u := by
  rw [scanStep, anyStepPair_flag_eq_true_iff R (fun z => eqFlag_flag u z) s hs n]
  constructor
  · rintro (h | ⟨i, hi, hlen, hblk⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, hlen, ((eqFlag_eq_true_iff _ _).mp hblk).symm⟩
  · rintro (h | ⟨i, hi, hlen, hblk⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, hlen, (eqFlag_eq_true_iff _ _).mpr hblk.symm⟩

/-! ## The scan, packed -/

/-- The packed scan state: the ruler, then the sought block, the flag and the
remaining string. Everything the step needs travels inside the state, which is
what `Cobham.iterate_mem_FP` iterates. -/
def memPack (R u f rest : List Bool) : List Bool := pair R (pair (pair u f) rest)

@[simp] theorem memPack_length (R u f rest : List Bool) :
    (memPack R u f rest).length
      = 2 * R.length + 2 * (2 * u.length + f.length + 2) + rest.length + 4 := by
  rw [memPack, pair_length, pair_length, pair_length]
  omega

/-- One step of the scan on the packed state. -/
def memStep (z : List Bool) : List Bool :=
  pair (pairFst z)
    (Cobham.selectHead
      (Cobham.lenLeFlag (pairSnd (pairSnd z)) (pairFst z))
      (pair
        (pair (pairFst (pairFst (pairSnd z)))
          (orBit (pairSnd (pairFst (pairSnd z)))
            (Cobham.eqFlag (pairFst (pairFst (pairSnd z)))
              ((pairSnd (pairSnd z)).take (pairFst z).length))))
        ((pairSnd (pairSnd z)).drop (pairFst z).length))
      (pairSnd z))

/-- **The packed step is the unpacked step.** -/
theorem memStep_pack (R u f rest : List Bool) :
    memStep (memPack R u f rest)
      = memPack R u (scanStep R u (f, rest)).1 (scanStep R u (f, rest)).2 := by
  rw [memStep, memPack]
  simp only [pairFst_pair, pairSnd_pair]
  by_cases hle : R.length ≤ rest.length
  · rw [scanStep, anyStepPair_pos R (eqFlag u) (f, rest) hle, Cobham.selectHead,
      ite_eq_left (by rw [(Cobham.lenLeFlag_eq_true_iff rest R).mpr hle]; rfl)]
    rfl
  · rw [scanStep, anyStepPair_neg R (eqFlag u) (f, rest) hle, Cobham.selectHead]
    have hflag : Cobham.lenLeFlag rest R = [false] := by
      rcases Cobham.lenLeFlag_flag rest R with h | h
      · rw [Cobham.lenLeFlag_eq_true_iff rest R] at h
        omega
      · exact h
    rw [ite_eq_right (by rw [hflag]; simp), ite_eq_left (by rw [hflag]; rfl)]
    rfl

/-- **The packed iteration is the unpacked one.** -/
theorem memStep_iterate (R u : List Bool) (s : List Bool × List Bool) (n : ℕ) :
    memStep^[n] (memPack R u s.1 s.2)
      = memPack R u ((scanStep R u)^[n] s).1 ((scanStep R u)^[n] s).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, memStep_pack, ih (scanStep R u s),
        Function.iterate_succ_apply]

/-! ## The verdict -/

/-- Does the block `u` occur in the block-aligned string `V`? -/
def memFlag (R u V : List Bool) : List Bool :=
  pairSnd (pairFst (pairSnd (memStep^[V.length]
    (memPack R u [false] V))))

theorem memFlag_flag (R u V : List Bool) :
    memFlag R u V = [true] ∨ memFlag R u V = [false] := by
  rw [memFlag, show V = ((([false] : List Bool), V)).2 from rfl,
    show ([false] : List Bool) = ((([false] : List Bool), V)).1 from rfl,
    memStep_iterate, memPack]
  simp only [pairFst_pair, pairSnd_pair]
  exact scanStep_flag R u (Or.inr rfl) _

/-- **The scan decides membership.** -/
theorem memFlag_eq_true_iff (R u V : List Bool) (hR : 0 < R.length) :
    memFlag R u V = [true] ↔
      ∃ i, i * R.length + R.length ≤ V.length ∧ blockAt R V i = u := by
  rw [memFlag, show V = ((([false] : List Bool), V)).2 from rfl,
    show ([false] : List Bool) = ((([false] : List Bool), V)).1 from rfl,
    memStep_iterate, memPack]
  simp only [pairFst_pair, pairSnd_pair]
  rw [scanStep_flag_eq_true_iff R u _ (Or.inr rfl)]
  constructor
  · rintro (h | ⟨i, -, hlen, hblk⟩)
    · simp at h
    · exact ⟨i, hlen, hblk⟩
  · rintro ⟨i, hlen, hblk⟩
    refine Or.inr ⟨i, ?_, hlen, hblk⟩
    calc i ≤ i * R.length := Nat.le_mul_of_pos_right _ hR
      _ < V.length := by omega

/-! ## The scan is polynomial-time -/

theorem memStep_mem_FP : memStep ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP →
      (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    exact this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP →
      (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    exact this
  have hR := hfst hid
  have hw := hsnd hid
  have hrest := hsnd hw
  have hu := hfst (hfst hw)
  have hf := hsnd (hfst hw)
  have htake : (fun z => (pairSnd (pairSnd z)).take
      (pairFst z).length) ∈ FP := Cobham.takeLenFn_mem_FP hR hrest
  have hdrop : (fun z => (pairSnd (pairSnd z)).drop
      (pairFst z).length) ∈ FP := dropLenFn_mem_FP hR hrest
  have hthen : (fun z => pair (pair (pairFst (pairFst (pairSnd z)))
      (orBit (pairSnd (pairFst (pairSnd z)))
        (Cobham.eqFlag (pairFst (pairFst (pairSnd z)))
          ((pairSnd (pairSnd z)).take (pairFst z).length))))
      ((pairSnd (pairSnd z)).drop (pairFst z).length)) ∈ FP :=
    Cobham.pairFn_mem_FP
      (Cobham.pairFn_mem_FP hu (orBitFn_mem_FP hf (eqFlagFn_mem_FP hu htake))) hdrop
  exact Cobham.pairFn_mem_FP hR
    (Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hrest hR) hthen hw)

/-- The scan's state never grows. -/
theorem memStep_iterate_length_le (R u : List Bool) (s : List Bool × List Bool)
    (hf : s.1 = [true] ∨ s.1 = [false]) (n : ℕ) :
    (memStep^[n] (memPack R u s.1 s.2)).length ≤ (memPack R u s.1 s.2).length := by
  rw [memStep_iterate, memPack_length, memPack_length]
  have hflen : ((scanStep R u)^[n] s).1.length = s.1.length := by
    rcases scanStep_flag R u hf n with h | h <;> rw [h] <;>
      rcases hf with h' | h' <;> rw [h'] <;> rfl
  have hrest := scanStep_rest_length R u s n
  omega

/-- **The membership scan is polynomial-time.** -/
theorem memFlagFn_mem_FP {Rf uf Vf : List Bool → List Bool}
    (hR : Rf ∈ FP) (hu : uf ∈ FP) (hV : Vf ∈ FP) :
    (fun z => memFlag (Rf z) (uf z) (Vf z)) ∈ FP := by
  have hinit : (fun z => memPack (Rf z) (uf z) [false] (Vf z)) ∈ FP :=
    Cobham.pairFn_mem_FP hR
      (Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hu (constFn_mem_FP [false])) hV)
  have hbound : ∀ z, ∀ n ≤ (Vf z).length,
      (memStep^[n] (memPack (Rf z) (uf z) [false] (Vf z))).length
        ≤ (memPack (Rf z) (uf z) [false] (Vf z)).length :=
    fun z n _ => memStep_iterate_length_le (Rf z) (uf z) ([false], Vf z) (Or.inr rfl) n
  have h := Cobham.iterate_mem_FP memStep_mem_FP hinit hV hinit hbound
  have hcomp : (fun z => pairSnd (pairFst (pairSnd
      (memStep^[(Vf z).length] (memPack (Rf z) (uf z) [false] (Vf z)))))) ∈ FP := by
    have h1 := mem_FP_comp h Cobham.sndBlock_mem_FP
    have h2 := mem_FP_comp h1 Cobham.fstBlock_mem_FP
    have h3 := mem_FP_comp h2 Cobham.sndBlock_mem_FP
    exact h3
  exact hcomp

end Complexity

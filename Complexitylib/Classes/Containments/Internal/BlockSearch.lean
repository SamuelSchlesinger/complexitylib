/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BlockMember
public import Complexitylib.Models.TuringMachine.Branch

/-!
# The worklist search over encoded configurations

⚠️ Unreviewed by Bolton

The configuration graph of a space-bounded machine is searched by a worklist: a
visited string holds the codes found so far, one fixed-width record each, and a
counter says which record is expanded next. One step expands one record — it
appends each of its two successors that is not already there — and advances the
counter. Running the loop for as many steps as there are configurations expands
everything, since the counter passes every record the search will ever hold.

The encoding is the one Cobham's theorem already uses: `Cobham.cfgCode` packs a
configuration into `2(k+2)+1` fixed-width blocks and `Cobham.stepFn` is the
encoded step of a deterministic machine, so `NTM.branchTM` supplies the two
successors.

## Main definitions

- `Complexity.nstepFn` — the encoded successor along one branch
- `Complexity.addBlock` — append a record unless it is already there
- `Complexity.searchStepPair` — one worklist step, on the unpacked state
- `Complexity.searchStep` — the same on the packed state

## Main results

- `Complexity.searchStep_pack` — the packed step is the unpacked step
- `Complexity.searchStep_mem_FP` — one step is polynomial-time
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## Rulers for a whole code -/

/-- A code's width, as a ruler: `m` copies of the block ruler. -/
def wideRuler (m : ℕ) (R : List Bool) : List Bool := (List.replicate m R).flatten

@[simp] theorem wideRuler_length (m : ℕ) (R : List Bool) :
    (wideRuler m R).length = m * R.length := by
  rw [wideRuler, List.length_flatten]
  simp [List.sum_replicate]

/-- Every constant number of copies of a polynomial-time value is
polynomial-time. -/
theorem wideRulerFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) (m : ℕ) :
    (fun z => wideRuler m (a z)) ∈ FP := by
  induction m with
  | zero => exact mem_FP_of_eq (constFn_mem_FP []) (fun _ => rfl)
  | succ m ih =>
      refine mem_FP_of_eq (Cobham.appendFn_mem_FP ha ih) fun z => ?_
      simp only [wideRuler, List.replicate_succ, List.flatten_cons]

/-- Normalise a would-be code to exactly the code width. -/
def fitCode (m : ℕ) (R b : List Bool) : List Bool := padTo (wideRuler m R) b

@[simp] theorem fitCode_length (m : ℕ) (R b : List Bool) :
    (fitCode m R b).length = m * R.length := by
  rw [fitCode, padTo_length, wideRuler_length]

/-- A value already of the code width is unchanged. -/
theorem fitCode_of_length (m : ℕ) (R b : List Bool) (h : b.length = m * R.length) :
    fitCode m R b = b := by
  rw [fitCode, padTo_eq_append _ _ (by rw [wideRuler_length]; omega), wideRuler_length, h]
  simp

theorem fitCodeFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (m : ℕ) : (fun z => fitCode m (a z) (b z)) ∈ FP :=
  padToFn_mem_FP (wideRulerFn_mem_FP ha m) hb

/-! ## The encoded successors -/

/-- The encoded successor of a configuration along branch `b`. -/
noncomputable def nstepFn (tm : NTM k) (b : Bool) (R z : List Bool) : List Bool :=
  stepFn (tm.branchTM b) R z

theorem nstepFnFn_mem_FP (tm : NTM k) (b : Bool) {a c : List Bool → List Bool}
    (ha : a ∈ FP) (hc : c ∈ FP) : (fun z => nstepFn tm b (a z) (c z)) ∈ FP :=
  binFn_mem_FP (g := nstepFn tm b)
    (Cobham.stepFn_mem (tm.branchTM b) (Cobham.proj 0) (Cobham.proj 1)) ha hc

/-! ## One step of the search -/

/-- Append a record to the visited string unless it is already there. -/
def addBlock (R b V : List Bool) : List Bool := selectHead (memFlag R b V) V (V ++ b)

theorem addBlock_eq_self (R b V : List Bool) (h : memFlag R b V = [true]) :
    addBlock R b V = V := by
  rw [addBlock, selectHead, ite_eq_left (by rw [h]; rfl)]

theorem addBlock_eq_append (R b V : List Bool) (h : memFlag R b V = [false]) :
    addBlock R b V = V ++ b := by
  rw [addBlock, selectHead, ite_eq_right (by rw [h]; simp), ite_eq_left (by rw [h]; rfl)]

theorem addBlockFn_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) : (fun z => addBlock (a z) (b z) (c z)) ∈ FP :=
  Cobham.selectHeadFn_mem_FP (memFlagFn_mem_FP ha hb hc) hc
    (Cobham.appendFn_mem_FP hc hb)

/-- The record the counter points at. -/
def curBlock (m : ℕ) (R r V : List Bool) : List Bool :=
  blockAt (wideRuler m R) V r.length

theorem curBlockFn_mem_FP {a b c : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) (m : ℕ) : (fun z => curBlock m (a z) (b z) (c z)) ∈ FP := by
  refine mem_FP_of_eq (Cobham.takeLenFn_mem_FP (wideRulerFn_mem_FP ha m)
    (dropLenFn_mem_FP (Cobham.mulLenFn_mem_FP hb (wideRulerFn_mem_FP ha m)) hc))
    fun z => ?_
  rw [curBlock, blockAt]
  simp

/-- The visited string must be at least this long for the record to exist. -/
def guardRuler (m : ℕ) (R r : List Bool) : List Bool :=
  List.replicate ((false :: r).length * (wideRuler m R).length) false

theorem guardRulerFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (m : ℕ) : (fun z => guardRuler m (a z) (b z)) ∈ FP := by
  have hcons : (fun z => false :: b z) ∈ FP := by
    have := mem_FP_comp hb (Cobham.cons_mem_FP false)
    exact this
  exact Cobham.mulLenFn_mem_FP hcons (wideRulerFn_mem_FP ha m)

@[simp] theorem guardRuler_length (m : ℕ) (R r : List Bool) :
    (guardRuler m R r).length = (r.length + 1) * (m * R.length) := by
  rw [guardRuler, List.length_replicate, wideRuler_length, List.length_cons]

/-- Expanding one record: append each successor that is not already there. -/
noncomputable def searchBody (tm : NTM k) (m : ℕ) (R r V : List Bool) : List Bool :=
  addBlock (wideRuler m R) (fitCode m R (nstepFn tm true R (curBlock m R r V)))
    (addBlock (wideRuler m R) (fitCode m R (nstepFn tm false R (curBlock m R r V))) V)

theorem searchBodyFn_mem_FP (tm : NTM k) (m : ℕ) {a b c : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) (hc : c ∈ FP) :
    (fun z => searchBody tm m (a z) (b z) (c z)) ∈ FP := by
  have hcur := curBlockFn_mem_FP ha hb hc m
  have hstep : ∀ β : Bool, (fun z => fitCode m (a z)
      (nstepFn tm β (a z) (curBlock m (a z) (b z) (c z)))) ∈ FP :=
    fun β => fitCodeFn_mem_FP ha (nstepFnFn_mem_FP tm β ha hcur) m
  exact addBlockFn_mem_FP (wideRulerFn_mem_FP ha m) (hstep true)
    (addBlockFn_mem_FP (wideRulerFn_mem_FP ha m) (hstep false) hc)

/-- One step of the worklist search, on the unpacked state `(counter, visited)`.
The counter is a ruler whose length is the index of the record to expand. -/
noncomputable def searchStepPair (tm : NTM k) (m : ℕ) (R : List Bool)
    (s : List Bool × List Bool) : List Bool × List Bool :=
  if (guardRuler m R s.1).length ≤ s.2.length then
    (false :: s.1, searchBody tm m R s.1 s.2)
  else (false :: s.1, s.2)

/-- The packed search state: the ruler, the counter and the visited string. -/
def searchPack (R r V : List Bool) : List Bool := pair R (pair r V)

@[simp] theorem searchPack_length (R r V : List Bool) :
    (searchPack R r V).length = 2 * R.length + 2 * r.length + V.length + 4 := by
  rw [searchPack, pair_length, pair_length]
  omega

/-- One step of the worklist search, on the packed state. -/
noncomputable def searchStep (tm : NTM k) (m : ℕ) (z : List Bool) : List Bool :=
  pair (pairFst z)
    (pair (false :: pairFst (pairSnd z))
      (selectHead
        (lenLeFlag (pairSnd (pairSnd z))
          (guardRuler m (pairFst z) (pairFst (pairSnd z))))
        (searchBody tm m (pairFst z) (pairFst (pairSnd z)) (pairSnd (pairSnd z)))
        (pairSnd (pairSnd z))))

/-- **The packed step is the unpacked step.** -/
theorem searchStep_pack (tm : NTM k) (m : ℕ) (R r V : List Bool) :
    searchStep tm m (searchPack R r V)
      = searchPack R (searchStepPair tm m R (r, V)).1 (searchStepPair tm m R (r, V)).2 := by
  rw [searchStep, searchPack, searchStepPair]
  simp only [pairFst_pair, pairSnd_pair]
  by_cases hle : (guardRuler m R r).length ≤ V.length
  · rw [ite_eq_left hle, selectHead,
      ite_eq_left (by rw [(Cobham.lenLeFlag_eq_true_iff V (guardRuler m R r)).mpr hle]; rfl)]
    rfl
  · have hflag : lenLeFlag V (guardRuler m R r) = [false] := by
      rcases Cobham.lenLeFlag_flag V (guardRuler m R r) with h | h
      · rw [Cobham.lenLeFlag_eq_true_iff V (guardRuler m R r)] at h
        omega
      · exact h
    rw [ite_eq_right hle, selectHead, ite_eq_right (by rw [hflag]; simp),
      ite_eq_left (by rw [hflag]; rfl)]
    rfl

/-- **The packed iteration is the unpacked one.** -/
theorem searchStep_iterate (tm : NTM k) (m : ℕ) (R : List Bool)
    (s : List Bool × List Bool) (n : ℕ) :
    (searchStep tm m)^[n] (searchPack R s.1 s.2)
      = searchPack R ((searchStepPair tm m R)^[n] s).1 ((searchStepPair tm m R)^[n] s).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, searchStep_pack, ih (searchStepPair tm m R s),
        Function.iterate_succ_apply]

/-- **One search step is polynomial-time.** -/
theorem searchStep_mem_FP (tm : NTM k) (m : ℕ) : searchStep tm m ∈ FP := by
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
  have hr := hfst hw
  have hV := hsnd hw
  have hcons : (fun z => false :: pairFst (pairSnd z)) ∈ FP := by
    have := mem_FP_comp hr (Cobham.cons_mem_FP false)
    exact this
  exact Cobham.pairFn_mem_FP hR (Cobham.pairFn_mem_FP hcons
    (Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hV (guardRulerFn_mem_FP hR hr m))
      (searchBodyFn_mem_FP tm m hR hr hV) hV))

end Complexity

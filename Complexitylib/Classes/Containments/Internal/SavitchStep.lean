/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchFrame
public import Complexitylib.Classes.Containments.Internal.CodeAccept
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble
public import Complexitylib.Classes.Containments.Internal.BinArith

/-!
# One step of Savitch's stack machine

⚠️ Unreviewed by Bolton

The recursion of Savitch's theorem, written as a single polynomial-time function
on the stack of `Complexitylib.Classes.Containments.Internal.SavitchFrame`.

A step does exactly one of five things.

* **Publish** — the done flag is set, so the answer is copied into the flag the
  iteration reads.
* **Finish** — the stack is empty, so the root's return value is the answer and
  the done flag goes up.
* **Bottom out** — the top frame's level is zero, so its subproblem is one step
  of the configuration graph; the frame is popped with its verdict.
* **Descend** — the top frame pushes the half of its interval it is currently
  trying.
* **Return** — a subcall has come back: a success either advances the frame to
  its second half or finishes it, and a failure advances the midpoint, giving up
  when the enumeration wraps.

## Main definitions

- `Complexity.baseReach`, `Complexity.baseAcc` — the two base cases
- `Complexity.savStep` — one step of the recursion
- `Complexity.savInit` — the state the recursion starts from
- `Complexity.savG` — the function `SpaceIter.mem_PSPACE_of_iterate` iterates

## Main results

- `Complexity.savStep_mem_FP`, `Complexity.savG_mem_FP` — a step is
  polynomial-time
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## Reading the state -/

/-- The frame on top of the state's stack. -/
def savTop (s : List Bool) : List Bool := stkTop (stStk s)

/-- The stack below the top frame. -/
def savRest (s : List Bool) : List Bool := stkRest (stStk s)

/-- The wide ruler a whole configuration code is measured against. -/
def savRuler (k : ℕ) (R : List Bool) : List Bool := wideRuler (codeBlocks k) R

/-- The all-zero code: the first midpoint the enumeration tries. -/
def savZero (k : ℕ) (R : List Bool) : List Bool := padTo (savRuler k R) []

@[simp] theorem savZero_length (k : ℕ) (R : List Bool) :
    (savZero k R).length = codeBlocks k * R.length := by
  rw [savZero, padTo_length, savRuler, wideRuler]
  simp [List.length_flatten]

/-! ## The base cases -/

/-- The base case of a reachability frame: `v` is `u`, or one step from it. -/
noncomputable def baseReach (tm : NTM k) (R u v : List Bool) : List Bool :=
  orBit (eqFlag u v)
    (orBit (eqFlag (nstepFn tm false R u) v) (eqFlag (nstepFn tm true R u) v))

/-- The base case of an acceptance frame: an accepting configuration is `u`, or
one step from it. -/
noncomputable def baseAcc (tm : NTM k) (R rl u : List Bool) : List Bool :=
  orBit (acceptFlag (stateCode tm.qhalt) R rl u)
    (orBit (acceptFlag (stateCode tm.qhalt) R rl (nstepFn tm false R u))
      (acceptFlag (stateCode tm.qhalt) R rl (nstepFn tm true R u)))

theorem baseReach_flag (tm : NTM k) (R u v : List Bool) :
    baseReach tm R u v = [true] ∨ baseReach tm R u v = [false] := by
  rw [baseReach]
  rcases eqFlag_flag u v with h | h <;>
    rcases eqFlag_flag (nstepFn tm false R u) v with h1 | h1 <;>
      rcases eqFlag_flag (nstepFn tm true R u) v with h2 | h2 <;>
        rw [h, h1, h2] <;> simp [orBit]

theorem baseAcc_flag (tm : NTM k) (R rl u : List Bool) :
    baseAcc tm R rl u = [true] ∨ baseAcc tm R rl u = [false] := by
  rw [baseAcc]
  rcases acceptFlag_flag (stateCode tm.qhalt) R rl u with h | h <;>
    rcases acceptFlag_flag (stateCode tm.qhalt) R rl (nstepFn tm false R u) with h1 | h1 <;>
      rcases acceptFlag_flag (stateCode tm.qhalt) R rl (nstepFn tm true R u) with h2 | h2 <;>
        rw [h, h1, h2] <;> simp [orBit]

/-! ## The step -/

/-- The child the top frame pushes: the first half of its interval while its
phase is zero, the second half afterwards. -/
noncomputable def savChild (k : ℕ) (s : List Bool) : List Bool :=
  selectHead (frPh (savTop s))
    (selectHead (frKind (savTop s))
      (mkFrame [true] [false] (dropOne (frLvl (savTop s))) (frM (savTop s))
        (savZero k (stR s)) (savZero k (stR s)))
      (mkFrame [false] [false] (dropOne (frLvl (savTop s))) (frM (savTop s))
        (frV (savTop s)) (savZero k (stR s))))
    (mkFrame [false] [false] (dropOne (frLvl (savTop s))) (frU (savTop s))
      (frM (savTop s)) (savZero k (stR s)))

/-- A failed subcall: try the next midpoint, or give up if the enumeration has
wrapped. -/
noncomputable def savAdvance (s : List Bool) : List Bool :=
  selectHead (bumpFlag (frM (savTop s)))
    (mkSt [false] (stAns s) (stR s) [false] (savRest s))
    (mkSt [false] (stAns s) (stR s) []
      (pair (mkFrame (frKind (savTop s)) [false] (frLvl (savTop s)) (frU (savTop s))
        (frV (savTop s)) (bumpCode (frM (savTop s)))) (savRest s)))

/-- A returning subcall. -/
noncomputable def savReturn (s : List Bool) : List Bool :=
  selectHead (stRet s)
    (selectHead (frPh (savTop s))
      (mkSt [false] (stAns s) (stR s) [true] (savRest s))
      (mkSt [false] (stAns s) (stR s) []
        (pair (mkFrame (frKind (savTop s)) [true] (frLvl (savTop s)) (frU (savTop s))
          (frV (savTop s)) (frM (savTop s))) (savRest s))))
    (savAdvance s)

/-- A descending step: bottom out, or push the half being tried. -/
noncomputable def savDescend (tm : NTM k) (s : List Bool) : List Bool :=
  selectHead (emptyFlag (frLvl (savTop s)))
    (mkSt [false] (stAns s) (stR s)
      (selectHead (frKind (savTop s))
        (baseAcc tm (stR s) (savRuler k (stR s)) (frU (savTop s)))
        (baseReach tm (stR s) (frU (savTop s)) (frV (savTop s))))
      (savRest s))
    (mkSt [false] (stAns s) (stR s) [] (pair (savChild k s) (stStk s)))

/-- **One step of Savitch's recursion.** -/
noncomputable def savStep (tm : NTM k) (s : List Bool) : List Bool :=
  selectHead (stDone s)
    (mkSt (stAns s) (stAns s) (stR s) (stRet s) (stStk s))
    (selectHead (emptyFlag (stStk s))
      (mkSt [true] (stRet s) (stR s) (stRet s) (stStk s))
      (selectHead (emptyFlag (stRet s)) (savDescend tm s) (savReturn s)))

/-! ## The initial state -/

/-- The block ruler of the window, as a function of the input. -/
noncomputable def savR (qp : Polynomial ℕ) (x : List Bool) : List Bool := polyRuler (2 * qp + 2) x

theorem savR_eq (qp : Polynomial ℕ) (x : List Bool) :
    savR qp x = blockRuler (qp.eval x.length) := (blockRuler_eq_polyRuler qp x).symm

/-- The state Savitch's recursion starts from: one acceptance frame, at the
top level, on the code of the initial configuration. -/
noncomputable def savInit (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) : List Bool :=
  mkSt [false] [false] (savR qp x) []
    (pair (mkFrame [true] [false] (polyRuler lp x)
      (initRecord tm (savR qp x) x) (savZero k (savR qp x)) (savZero k (savR qp x))) [])

/-- **The function the space-bounded iteration runs.** The running state is the
first component and the input the second, so the very first call — on
`pair [] x` — is the one that builds the initial state. -/
noncomputable def savG (tm : NTM k) (qp lp : Polynomial ℕ) (z : List Bool) : List Bool :=
  pair (selectHead (emptyFlag (pairFst z))
    (savInit tm qp lp (pairSnd z)) (savStep tm (pairFst z))) (pairSnd z)

@[simp] theorem savG_pair (tm : NTM k) (qp lp : Polynomial ℕ) (s x : List Bool) :
    savG tm qp lp (pair s x)
      = pair (selectHead (emptyFlag s) (savInit tm qp lp x) (savStep tm s)) x := by
  rw [savG, pairFst_pair, pairSnd_pair]

theorem savG_nil (tm : NTM k) (qp lp : Polynomial ℕ) (x : List Bool) :
    savG tm qp lp (pair [] x) = pair (savInit tm qp lp x) x := by
  rw [savG_pair, emptyFlag_nil, selectHead]
  simp

theorem savG_step (tm : NTM k) (qp lp : Polynomial ℕ) (s x : List Bool) (hs : s ≠ []) :
    savG tm qp lp (pair s x) = pair (savStep tm s) x := by
  obtain ⟨b, t, rfl⟩ : ∃ b t, s = b :: t := by
    cases s with
    | nil => exact absurd rfl hs
    | cons b t => exact ⟨b, t, rfl⟩
  rw [savG_pair, emptyFlag_cons, selectHead]
  simp

/-! ## The step is polynomial-time -/

theorem savRulerFn_mem_FP (k : ℕ) {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => savRuler k (a z)) ∈ FP := wideRulerFn_mem_FP ha (codeBlocks k)

theorem savZeroFn_mem_FP (k : ℕ) {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => savZero k (a z)) ∈ FP :=
  padToFn_mem_FP (savRulerFn_mem_FP k ha) (constFn_mem_FP [])

theorem baseReachFn_mem_FP (tm : NTM k) {Rf uf vf : List Bool → List Bool}
    (hR : Rf ∈ FP) (hu : uf ∈ FP) (hv : vf ∈ FP) :
    (fun z => baseReach tm (Rf z) (uf z) (vf z)) ∈ FP :=
  orBitFn_mem_FP (eqFlagFn_mem_FP hu hv)
    (orBitFn_mem_FP (eqFlagFn_mem_FP (nstepFnFn_mem_FP tm false hR hu) hv)
      (eqFlagFn_mem_FP (nstepFnFn_mem_FP tm true hR hu) hv))

theorem baseAccFn_mem_FP (tm : NTM k) {Rf rlf uf : List Bool → List Bool}
    (hR : Rf ∈ FP) (hrl : rlf ∈ FP) (hu : uf ∈ FP) :
    (fun z => baseAcc tm (Rf z) (rlf z) (uf z)) ∈ FP :=
  orBitFn_mem_FP (acceptFlagFn_mem_FP _ hR hrl hu)
    (orBitFn_mem_FP (acceptFlagFn_mem_FP _ hR hrl (nstepFnFn_mem_FP tm false hR hu))
      (acceptFlagFn_mem_FP _ hR hrl (nstepFnFn_mem_FP tm true hR hu)))

theorem savStep_mem_FP (tm : NTM k) : savStep tm ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hdone := stDoneFn_mem_FP hid
  have hans := stAnsFn_mem_FP hid
  have hR := stRFn_mem_FP hid
  have hret := stRetFn_mem_FP hid
  have hstk := stStkFn_mem_FP hid
  have htop : (fun z => savTop z) ∈ FP := stkTopFn_mem_FP hstk
  have hrest : (fun z => savRest z) ∈ FP := stkRestFn_mem_FP hstk
  have hkind := frKindFn_mem_FP htop
  have hph := frPhFn_mem_FP htop
  have hlvl := frLvlFn_mem_FP htop
  have hu := frUFn_mem_FP htop
  have hv := frVFn_mem_FP htop
  have hm := frMFn_mem_FP htop
  have hzero := savZeroFn_mem_FP k hR
  have hchild : (fun z => savChild k z) ∈ FP :=
    Cobham.selectHeadFn_mem_FP hph
      (Cobham.selectHeadFn_mem_FP hkind
        (mkFrameFn_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [false])
          (dropOneFn_mem_FP hlvl) hm hzero hzero)
        (mkFrameFn_mem_FP (constFn_mem_FP [false]) (constFn_mem_FP [false])
          (dropOneFn_mem_FP hlvl) hm hv hzero))
      (mkFrameFn_mem_FP (constFn_mem_FP [false]) (constFn_mem_FP [false])
        (dropOneFn_mem_FP hlvl) hu hm hzero)
  have hadv : (fun z => savAdvance z) ∈ FP :=
    Cobham.selectHeadFn_mem_FP (bumpFlagFn_mem_FP hm)
      (mkStFn_mem_FP (constFn_mem_FP [false]) hans hR (constFn_mem_FP [false]) hrest)
      (mkStFn_mem_FP (constFn_mem_FP [false]) hans hR (constFn_mem_FP [])
        (Cobham.pairFn_mem_FP
          (mkFrameFn_mem_FP hkind (constFn_mem_FP [false]) hlvl hu hv
            (bumpCodeFn_mem_FP hm)) hrest))
  have hreturn : (fun z => savReturn z) ∈ FP :=
    Cobham.selectHeadFn_mem_FP hret
      (Cobham.selectHeadFn_mem_FP hph
        (mkStFn_mem_FP (constFn_mem_FP [false]) hans hR (constFn_mem_FP [true]) hrest)
        (mkStFn_mem_FP (constFn_mem_FP [false]) hans hR (constFn_mem_FP [])
          (Cobham.pairFn_mem_FP
            (mkFrameFn_mem_FP hkind (constFn_mem_FP [true]) hlvl hu hv hm) hrest)))
      hadv
  have hdescend : (fun z => savDescend tm z) ∈ FP :=
    Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hlvl)
      (mkStFn_mem_FP (constFn_mem_FP [false]) hans hR
        (Cobham.selectHeadFn_mem_FP hkind
          (baseAccFn_mem_FP tm hR (savRulerFn_mem_FP k hR) hu)
          (baseReachFn_mem_FP tm hR hu hv)) hrest)
      (mkStFn_mem_FP (constFn_mem_FP [false]) hans hR (constFn_mem_FP [])
        (Cobham.pairFn_mem_FP hchild hstk))
  exact Cobham.selectHeadFn_mem_FP hdone
    (mkStFn_mem_FP hans hans hR hret hstk)
    (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hstk)
      (mkStFn_mem_FP (constFn_mem_FP [true]) hret hR hret hstk)
      (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hret) hdescend hreturn))

theorem savRFn_mem_FP (qp : Polynomial ℕ) {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => savR qp (a z)) ∈ FP := polyRulerFn_mem_FP (2 * qp + 2) ha

theorem savInitFn_mem_FP (tm : NTM k) (qp lp : Polynomial ℕ)
    {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => savInit tm qp lp (a z)) ∈ FP := by
  have hR : (fun z => savR qp (a z)) ∈ FP := savRFn_mem_FP qp ha
  have hzero : (fun z => savZero k (savR qp (a z))) ∈ FP := savZeroFn_mem_FP k hR
  exact mkStFn_mem_FP (constFn_mem_FP [false]) (constFn_mem_FP [false]) hR
    (constFn_mem_FP [])
    (Cobham.pairFn_mem_FP
      (mkFrameFn_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [false])
        (polyRulerFn_mem_FP lp ha) (initRecordFn_mem_FP tm hR ha) hzero hzero)
      (constFn_mem_FP []))

theorem savG_mem_FP (tm : NTM k) (qp lp : Polynomial ℕ) : savG tm qp lp ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst := fstBlockOf_mem_FP hid
  have hsnd := sndBlockOf_mem_FP hid
  have hstep : (fun z => savStep tm (pairFst z)) ∈ FP := by
    have := mem_FP_comp hfst (savStep_mem_FP tm)
    exact this
  exact Cobham.pairFn_mem_FP
    (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hfst)
      (savInitFn_mem_FP tm qp lp hsnd) hstep) hsnd

end Complexity

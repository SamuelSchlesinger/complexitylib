/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchBits

/-!
# The tape of Savitch's stack machine

⚠️ Unreviewed by Bolton

Savitch's procedure is a recursion of polynomial depth, so it is a stack machine
whose stack is polynomially bounded. This file fixes how that stack is written on
a single bitstring, and gives every field's reader and writer inside the
polynomial-time algebra.

A **frame** carries the subproblem a level of the recursion is working on:

* `kind` — `[false]` for *is `v` reachable from `u`*, `[true]` for *is some
  accepting configuration reachable from `u`*;
* `ph` — `[false]` while the first half of the interval is being tried,
  `[true]` while the second is;
* `lvl` — the level, in unary: `2 ^ |lvl|` steps are allowed;
* `u`, `v` — the two endpoints (`v` is unused by an acceptance frame);
* `m` — the midpoint being tried, which doubles as the enumeration's counter.

A **stack** is a right-nested chain of pairs, empty stack being the empty string;
`pair` is never empty, so the two are told apart by a single flag.

The **state** carries the done flag (which is the bit `Complexity.SpaceIter`
watches), the answer, the block ruler the codes are written against, the value a
finished subcall is returning (`[]` while descending), and the stack.

## Main definitions

- `Complexity.mkFrame` and `Complexity.frKind`, … — a frame and its fields
- `Complexity.encStack`, `Complexity.stkTop`, `Complexity.stkRest` — the stack
- `Complexity.mkSt` and `Complexity.stDone`, … — the state and its fields

## Main results

- the `_mk` simp lemmas — every reader inverts the constructor
- `Complexity.mkFrameFn_mem_FP`, `Complexity.mkStFn_mem_FP`, and the readers' —
  all of it is in `FP`
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## Frames -/

/-- A frame of Savitch's recursion. -/
def mkFrame (kind ph lvl u v m : List Bool) : List Bool :=
  pair kind (pair ph (pair lvl (pair u (pair v m))))

/-- Which subproblem the frame is working on. -/
def frKind (f : List Bool) : List Bool := pairFst f

/-- Which half of the interval the frame is trying. -/
def frPh (f : List Bool) : List Bool := pairFst (pairSnd f)

/-- The frame's level, in unary. -/
def frLvl (f : List Bool) : List Bool := pairFst (pairSnd (pairSnd f))

/-- The frame's source endpoint. -/
def frU (f : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd f)))

/-- The frame's target endpoint. -/
def frV (f : List Bool) : List Bool :=
  pairFst (pairSnd (pairSnd (pairSnd (pairSnd f))))

/-- The midpoint the frame is trying. -/
def frM (f : List Bool) : List Bool :=
  pairSnd (pairSnd (pairSnd (pairSnd (pairSnd f))))

@[simp] theorem frKind_mk (kind ph lvl u v m : List Bool) :
    frKind (mkFrame kind ph lvl u v m) = kind := by simp [frKind, mkFrame]

@[simp] theorem frPh_mk (kind ph lvl u v m : List Bool) :
    frPh (mkFrame kind ph lvl u v m) = ph := by simp [frPh, mkFrame]

@[simp] theorem frLvl_mk (kind ph lvl u v m : List Bool) :
    frLvl (mkFrame kind ph lvl u v m) = lvl := by simp [frLvl, mkFrame]

@[simp] theorem frU_mk (kind ph lvl u v m : List Bool) :
    frU (mkFrame kind ph lvl u v m) = u := by simp [frU, mkFrame]

@[simp] theorem frV_mk (kind ph lvl u v m : List Bool) :
    frV (mkFrame kind ph lvl u v m) = v := by simp [frV, mkFrame]

@[simp] theorem frM_mk (kind ph lvl u v m : List Bool) :
    frM (mkFrame kind ph lvl u v m) = m := by simp [frM, mkFrame]

@[simp] theorem mkFrame_length (kind ph lvl u v m : List Bool) :
    (mkFrame kind ph lvl u v m).length
      = 2 * kind.length + 2 * ph.length + 2 * lvl.length + 2 * u.length + 2 * v.length +
        m.length + 10 := by
  rw [mkFrame, pair_length, pair_length, pair_length, pair_length, pair_length]
  omega

/-! ## Stacks -/

/-- A stack of frames, top first. -/
def encStack : List (List Bool) → List Bool
  | [] => []
  | f :: fs => pair f (encStack fs)

@[simp] theorem encStack_nil : encStack [] = [] := rfl

@[simp] theorem encStack_cons (f : List Bool) (fs : List (List Bool)) :
    encStack (f :: fs) = pair f (encStack fs) := rfl

/-- The frame on top of the stack. -/
def stkTop (S : List Bool) : List Bool := pairFst S

/-- The stack below the top frame. -/
def stkRest (S : List Bool) : List Bool := pairSnd S

@[simp] theorem stkTop_pair (f g : List Bool) : stkTop (pair f g) = f := by simp [stkTop]

@[simp] theorem stkRest_pair (f g : List Bool) : stkRest (pair f g) = g := by simp [stkRest]

theorem stkTop_cons (f : List Bool) (fs : List (List Bool)) :
    stkTop (encStack (f :: fs)) = f := by simp

theorem stkRest_cons (f : List Bool) (fs : List (List Bool)) :
    stkRest (encStack (f :: fs)) = encStack fs := by simp

/-- A stack is empty exactly when its encoding is. -/
theorem encStack_eq_nil_iff (fs : List (List Bool)) : encStack fs = [] ↔ fs = [] := by
  cases fs with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons f fs =>
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by simp)⟩
      rw [encStack_cons]
      intro hc
      have := congrArg List.length hc
      rw [pair_length] at this
      simp at this

@[simp] theorem encStack_length (fs : List (List Bool)) :
    (encStack fs).length = fs.foldr (fun f n => 2 * f.length + 2 + n) 0 := by
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [encStack_cons, pair_length, ih, List.foldr_cons]

/-! ## The state -/

/-- The machine's state: the done flag, the answer, the block ruler, the value a
finished subcall is returning, and the stack. -/
def mkSt (d a R ret stk : List Bool) : List Bool :=
  pair d (pair a (pair R (pair ret stk)))

/-- The done flag — the bit the iteration watches. -/
def stDone (s : List Bool) : List Bool := pairFst s

/-- The answer, once the recursion has produced one. -/
def stAns (s : List Bool) : List Bool := pairFst (pairSnd s)

/-- The block ruler the configuration codes are written against. -/
def stR (s : List Bool) : List Bool := pairFst (pairSnd (pairSnd s))

/-- The value a finished subcall is returning; `[]` while descending. -/
def stRet (s : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd s)))

/-- The stack. -/
def stStk (s : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd s)))

@[simp] theorem stDone_mk (d a R ret stk : List Bool) : stDone (mkSt d a R ret stk) = d := by
  simp [stDone, mkSt]

@[simp] theorem stAns_mk (d a R ret stk : List Bool) : stAns (mkSt d a R ret stk) = a := by
  simp [stAns, mkSt]

@[simp] theorem stR_mk (d a R ret stk : List Bool) : stR (mkSt d a R ret stk) = R := by
  simp [stR, mkSt]

@[simp] theorem stRet_mk (d a R ret stk : List Bool) : stRet (mkSt d a R ret stk) = ret := by
  simp [stRet, mkSt]

@[simp] theorem stStk_mk (d a R ret stk : List Bool) : stStk (mkSt d a R ret stk) = stk := by
  simp [stStk, mkSt]

@[simp] theorem mkSt_length (d a R ret stk : List Bool) :
    (mkSt d a R ret stk).length
      = 2 * d.length + 2 * a.length + 2 * R.length + 2 * ret.length + stk.length + 8 := by
  rw [mkSt, pair_length, pair_length, pair_length, pair_length]
  omega

/-- The head bit of the state is the done flag. -/
theorem mkSt_headD (b : Bool) (a R ret stk : List Bool) :
    (mkSt [b] a R ret stk).headD false = b := by
  rw [mkSt, pair_cons_eq]
  rfl

/-- A state is never empty. -/
theorem mkSt_ne_nil (d a R ret stk : List Bool) : mkSt d a R ret stk ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [mkSt_length] at this
  simp at this

/-! ## The readers and the constructors are polynomial-time -/

theorem fstBlockOf_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => pairFst (a z)) ∈ FP := by
  have := mem_FP_comp ha Cobham.fstBlock_mem_FP
  exact this

theorem sndBlockOf_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => pairSnd (a z)) ∈ FP := by
  have := mem_FP_comp ha Cobham.sndBlock_mem_FP
  exact this

theorem frKindFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => frKind (a z)) ∈ FP := fstBlockOf_mem_FP ha

theorem frPhFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => frPh (a z)) ∈ FP := fstBlockOf_mem_FP (sndBlockOf_mem_FP ha)

theorem frLvlFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => frLvl (a z)) ∈ FP :=
  fstBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP ha))

theorem frUFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => frU (a z)) ∈ FP :=
  fstBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP ha)))

theorem frVFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => frV (a z)) ∈ FP :=
  fstBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP
    (sndBlockOf_mem_FP ha))))

theorem frMFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => frM (a z)) ∈ FP :=
  sndBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP
    (sndBlockOf_mem_FP ha))))

theorem mkFrameFn_mem_FP {kf pf lf uf vf mf : List Bool → List Bool}
    (hk : kf ∈ FP) (hp : pf ∈ FP) (hl : lf ∈ FP) (hu : uf ∈ FP) (hv : vf ∈ FP)
    (hm : mf ∈ FP) :
    (fun z => mkFrame (kf z) (pf z) (lf z) (uf z) (vf z) (mf z)) ∈ FP :=
  Cobham.pairFn_mem_FP hk (Cobham.pairFn_mem_FP hp (Cobham.pairFn_mem_FP hl
    (Cobham.pairFn_mem_FP hu (Cobham.pairFn_mem_FP hv hm))))

theorem stkTopFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => stkTop (a z)) ∈ FP := fstBlockOf_mem_FP ha

theorem stkRestFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => stkRest (a z)) ∈ FP := sndBlockOf_mem_FP ha

theorem stDoneFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => stDone (a z)) ∈ FP := fstBlockOf_mem_FP ha

theorem stAnsFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => stAns (a z)) ∈ FP := fstBlockOf_mem_FP (sndBlockOf_mem_FP ha)

theorem stRFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => stR (a z)) ∈ FP :=
  fstBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP ha))

theorem stRetFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => stRet (a z)) ∈ FP :=
  fstBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP ha)))

theorem stStkFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => stStk (a z)) ∈ FP :=
  sndBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP (sndBlockOf_mem_FP ha)))

theorem mkStFn_mem_FP {df af Rf rf sf : List Bool → List Bool}
    (hd : df ∈ FP) (ha : af ∈ FP) (hR : Rf ∈ FP) (hr : rf ∈ FP) (hs : sf ∈ FP) :
    (fun z => mkSt (df z) (af z) (Rf z) (rf z) (sf z)) ∈ FP :=
  Cobham.pairFn_mem_FP hd (Cobham.pairFn_mem_FP ha (Cobham.pairFn_mem_FP hR
    (Cobham.pairFn_mem_FP hr hs)))

end Complexity

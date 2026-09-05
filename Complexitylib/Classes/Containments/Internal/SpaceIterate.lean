/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.Iterate
public import Complexitylib.Classes.Containments.Internal.PPTest
public import Complexitylib.Classes.Containments.Internal.PPBody
public import Complexitylib.Classes.Containments.Internal.PPLayout
public import Complexitylib.Models.TuringMachine.Hoare.StartInvariant
public import Complexitylib.Classes.Containments.Internal.PolyWindow

/-!
# Iterating a polynomial-time function in polynomial space

⚠️ Unreviewed by Bolton

A language decided by iterating a polynomial-time function on a polynomially
bounded state is in `PSPACE`, however many iterations it takes: the state is the
only thing that has to be stored, and the iteration count lives in a binary
counter of polynomially many bits. This is the machine-independent way into
`PSPACE`, the counterpart of what Cobham's theorem does for `P` — and it is what
Savitch's theorem needs, since Savitch's recursion is a stack machine whose step
is polynomial-time and whose stack is polynomially bounded.

The machine reuses the iteration machinery of
`Complexitylib.Classes.P.Cobham.Internal.Iterate` wholesale, on that file's own
layout: `Cobham.iterSetup` puts `pair [] x` in place, `Cobham.iterTail` builds
the entry shape, and `Cobham.iterBody` applies the function once and restores
it. Only the loop driver changes. `TM.forRegTM` counts in unary, which cannot
reach `2 ^ poly`, so the loop here is `TM.loopTM`, as in `PP ⊆ PSPACE` and
`PH ⊆ PSPACE`.

## No tape is added

Two of the layout's tapes are free for the loop's own use, so the machine needs
no tapes beyond the ones `Cobham.iterBody` already has — and therefore no
placement, and no parking of tapes a placement would freeze.

* `Cobham.resIdx`, the result tape, is blank at the start of every iteration:
  `TM.applyPre` puts `parkedBlank` there. That is the source the verdict cell is
  cleared from.
* `Cobham.rfIdx`, the fuel register of the unary loop that is not running here,
  is held fixed by `Cobham.iterBody` whatever it contains. That is where the
  iteration counter lives.

The machine never reads the counter: it is there so that
`TM.loopTM_hoareTime_indexed` can read the iteration index off the tapes for its
termination measure, which is why it may be binary and cost only polynomially
many cells.

## The loop's shape

The programmed function signals completion by putting a `1` at the head of its
state, and the loop's test is `TM.writeOutputBitTM` reading the state tape's
first cell — so the loop runs until the computation says it is done, and the
number of iterations never has to be represented. One more application after the
loop puts the verdict at the head of the state, and a second
`TM.writeOutputBitTM` publishes it.

## Main definitions

- `Complexity.SpaceIter.slotOf` — the verdict cell as a tape
- `Complexity.SpaceIter.headSym` — the symbol at the head of a state
- `Complexity.SpaceIter.iterBank` — the tape family of an iteration
- `Complexity.SpaceIter.bodyTM`, `testTM` — the loop
- `Complexity.SpaceIter.prologueTM`, `epilogueTM` — the two ends
- `Complexity.SpaceIter.spaceIterTM` — the whole machine
- `Complexity.SpaceIter.windowBound` — the polynomial window it keeps

## Main results

- `Complexity.SpaceIter.bodyTM_hoareTime` — one pass applies the function once
- `Complexity.SpaceIter.testTM_hoareTime` — the test publishes the state's head
- `Complexity.SpaceIter.loop_hoareTime` — the loop runs until the state is done
- `Complexity.SpaceIter.loop_keepsWindowOn` — one pass' width bounds the whole loop
- `Complexity.SpaceIter.spaceIterTM_hoareTime` — the machine publishes the answer
- `Complexity.SpaceIter.spaceIterTM_keepsWindow` — and keeps a polynomial window
- `Complexity.SpaceIter.mem_PSPACE_of_iterate` — so the language it decides is in
  `PSPACE`
-/

@[expose] public section

namespace Complexity

namespace SpaceIter

open TM

variable {k : ℕ}

/-! ## The verdict cell -/

/-- The output tape holding `s` in its verdict cell. -/
def slotOf (s : Γ) : Tape := parkedBlank.write s

@[simp] theorem slotOf_head (s : Γ) : (slotOf s).head = 1 := by
  rw [slotOf, Tape.write_head]
  rfl

@[simp] theorem slotOf_cells_one (s : Γ) : (slotOf s).cells 1 = s := by
  rw [slotOf, Tape.write, ite_eq_right (by show ¬ (1 : ℕ) = 0; omega)]
  show Function.update parkedBlank.cells parkedBlank.head s 1 = s
  rw [show parkedBlank.head = 1 from rfl]
  exact Function.update_self (β := fun _ => Γ) 1 s parkedBlank.cells

theorem slotOf_cells_of_ne (s : Γ) {c : ℕ} (hc : c ≠ 1) :
    (slotOf s).cells c = parkedBlank.cells c := by
  rw [slotOf, Tape.write, ite_eq_right (by show ¬ (1 : ℕ) = 0; omega)]
  exact Function.update_of_ne (by simpa using hc) _ _

@[simp] theorem slotOf_write (s t : Γ) : (slotOf s).write t = slotOf t := by
  refine Tape.ext (by rw [Tape.write_head, slotOf_head, slotOf_head]) (funext fun c => ?_)
  by_cases hc : c = 1
  · subst hc
    rw [Tape.write, ite_eq_right (by show ¬ (slotOf s).head = 0; rw [slotOf_head]; omega)]
    show Function.update (slotOf s).cells (slotOf s).head t 1 = _
    rw [slotOf_head, Function.update_self, slotOf_cells_one]
  · rw [Tape.write, ite_eq_right (by show ¬ (slotOf s).head = 0; rw [slotOf_head]; omega)]
    show Function.update (slotOf s).cells (slotOf s).head t c = _
    rw [slotOf_head, Function.update_of_ne (by simpa using hc),
      slotOf_cells_of_ne s hc, slotOf_cells_of_ne t hc]

@[simp] theorem slotOf_blank : slotOf Γ.blank = parkedBlank := by
  refine Tape.ext (by rw [slotOf_head]; rfl) (funext fun c => ?_)
  by_cases hc : c = 1
  · subst hc
    rw [slotOf_cells_one]
    exact (parkedBlank_cells 1).symm
  · exact slotOf_cells_of_ne Γ.blank hc

theorem slotOf_startInvariant (s : Γ) (hs : s ≠ Γ.start) :
    Tape.StartInvariant (slotOf s) := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [slotOf_cells_of_ne s (by omega)]
    exact startInvariant_initNil.1
  · by_cases hc1 : c = 1
    · subst hc1
      rw [slotOf_cells_one]
      exact hs
    · rw [slotOf_cells_of_ne s hc1]
      exact startInvariant_initNil.2 c (by omega)

theorem slotOf_parked (s : Γ) (hs : s ≠ Γ.start) : Parked (slotOf s) := by
  refine ⟨by rw [slotOf_head], fun c hc => ?_⟩
  by_cases hc1 : c = 1
  · subst hc1
    rw [slotOf_cells_one]
    exact hs
  · rw [slotOf_cells_of_ne s hc1]
    exact parked_parkedBlank.2 c (by omega)

/-! ## The symbol at the head of a state -/

/-- The symbol at the head of a state tape: the state's first bit, or blank. -/
def headSym (y : List Bool) : Γ := ((y.map Γ.ofBool)[0]?).getD Γ.blank

@[simp] theorem headSym_nil : headSym [] = Γ.blank := rfl

@[simp] theorem headSym_cons (b : Bool) (y : List Bool) :
    headSym (b :: y) = Γ.ofBool b := rfl

theorem headSym_eq_one_iff (y : List Bool) :
    (readBackWrite (headSym y)).toΓ = Γ.one ↔ y.headD false = true := by
  cases y with
  | nil => simp [headSym, readBackWrite]
  | cons b y => cases b <;> simp [headSym, readBackWrite, Γ.ofBool, Γw.toΓ]

theorem toΓ_readBackWrite_ne_start (g : Γ) : (readBackWrite g).toΓ ≠ Γ.start := by
  cases g <;> simp [readBackWrite, Γw.toΓ]

/-! ## Reading the iteration index off the tapes

`TM.loopTM_hoareTime_indexed` needs the iteration index as a function of the
configuration, for its termination measure. The counter carries it; this is the
ghost read, and nothing computes it. -/

theorem natTape_startInvariant (v : ℕ) : Tape.StartInvariant (natTape v) :=
  ⟨NTM.natTape_cells_zero v, fun j hj => (natTape_parked v).2 j hj⟩

theorem natTape_head_one (v : ℕ) : (natTape v).head = 1 :=
  (Tape.init_move_right_hasBinaryNat v).2.1

open Classical in
/-- The value a canonical binary register holds. -/
noncomputable def ctrValue (t : Tape) : ℕ :=
  if h : ∃ v, t = natTape v then h.choose else 0

@[simp] theorem ctrValue_natTape (v : ℕ) : ctrValue (natTape v) = v := by
  classical
  have hex : ∃ w, natTape v = natTape w := ⟨v, rfl⟩
  rw [ctrValue, dite_eq_left hex]
  generalize hgen : hex.choose = w
  have hc : natTape v = natTape w := hgen ▸ hex.choose_spec
  refine hasBinaryNat_value_unique (t := natTape v) ?_ (Tape.init_move_right_hasBinaryNat v)
  rw [hc]
  exact Tape.init_move_right_hasBinaryNat w

/-- The loop's index function: how far the counter has advanced past `start`.
The input and output tapes are ignored, but `TM.loopTM_hoareTime_indexed` takes
the index as a function of the whole configuration, so they have to be there. -/
@[nolint unusedArguments]
noncomputable def loopIdx (k start : ℕ) :
    Tape → (Fin (3 + (k + 2) + 0) → Tape) → Tape → ℕ :=
  fun _ work _ => ctrValue (work rfIdx) - start

/-! ## The tapes of an iteration -/

/-- The tape family at an iteration: the entry shape for `y` on the application
block, the counter on the fuel register, and the two fixed tapes. -/
noncomputable def iterBank (M : TM k) (y : List Bool) (inp₀ junkT : Tape)
    (H c : ℕ) : Fin (3 + (k + 2) + 0) → Tape :=
  fun i => if hi : placeWorkInMiddle 3 (k + 2) i
    then TM.applyPre M y inp₀ (placeWorkCoord 3 (k + 2) i hi)
    else bookTapes (natTape c) junkT H i

@[simp] theorem iterBank_app (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ)
    (j : Fin (k + 2)) :
    iterBank M y inp₀ junkT H c (appIdx j) = TM.applyPre M y inp₀ j := by
  rw [iterBank, dite_eq_left (appIdx_middle j)]
  congr 1
  exact placeWorkCoord_placeWorkIdx 3 0 j

theorem iterBank_book (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ)
    (i : Fin (3 + (k + 2) + 0)) (hi : ¬ placeWorkInMiddle 3 (k + 2) i) :
    iterBank M y inp₀ junkT H c i = bookTapes (natTape c) junkT H i := by
  rw [iterBank, dite_eq_right hi]

@[simp] theorem iterBank_rf (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ) :
    iterBank M y inp₀ junkT H c rfIdx = natTape c := by
  rw [iterBank_book M y inp₀ junkT H c rfIdx rfIdx_not_middle, bookTapes_rf]

@[simp] theorem iterBank_wf (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ) :
    iterBank M y inp₀ junkT H c wfIdx = regTape H := by
  rw [iterBank_book M y inp₀ junkT H c wfIdx wfIdx_not_middle, bookTapes_wf]

@[simp] theorem iterBank_junk (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ) :
    iterBank M y inp₀ junkT H c junkIdx = junkT := by
  rw [iterBank_book M y inp₀ junkT H c junkIdx junkIdx_not_middle, bookTapes_junk]

@[simp] theorem iterBank_res (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ) :
    iterBank M y inp₀ junkT H c resIdx = parkedBlank := by
  rw [resIdx, iterBank_app, TM.applyPre, Fin.snoc_last]

theorem iterBank_parked (M : TM k) (y : List Bool) (inp₀ junkT : Tape)
    (hjunkP : Parked junkT) (H c : ℕ) (i : Fin (3 + (k + 2) + 0)) :
    Parked (iterBank M y inp₀ junkT H c i) := by
  rcases Complexity.layout_cases i with h | h | h | ⟨j, h⟩
  · rw [h, iterBank_rf]
    exact natTape_parked c
  · rw [h, iterBank_wf]
    exact parked_regTape H
  · rw [h, iterBank_junk]
    exact hjunkP
  · rw [h, iterBank_app]
    exact ⟨le_of_eq (TM.applyPre_head M y inp₀ j).symm,
      fun c hc => (TM.applyPre_startInvariant M y inp₀ j).2 c hc⟩

/-- Every tape of the bank is parked at cell one. -/
theorem iterBank_head (M : TM k) (y : List Bool) (inp₀ junkT : Tape)
    (hjunkh : junkT.head ≤ 1) (H c : ℕ) (i : Fin (3 + (k + 2) + 0)) :
    (iterBank M y inp₀ junkT H c i).head ≤ 1 := by
  rcases Complexity.layout_cases i with h | h | h | ⟨j, h⟩
  · rw [h, iterBank_rf, natTape_head_one]
  · rw [h, iterBank_wf]
    exact le_of_eq (regT_head H)
  · rw [h, iterBank_junk]
    exact hjunkh
  · rw [h, iterBank_app]
    exact le_of_eq (TM.applyPre_head M y inp₀ j)

/-- A block family is the iteration bank as soon as it has the right tapes. -/
theorem iterBank_eq (M : TM k) (z : List Bool) (inp₀ junkT : Tape) (H c : ℕ)
    (W : Fin (3 + (k + 2) + 0) → Tape)
    (happ : ∀ j, W (appIdx j) = TM.applyPre M z inp₀ j)
    (hrf : W rfIdx = natTape c) (hwf : W wfIdx = regTape H) (hjunk : W junkIdx = junkT) :
    W = iterBank M z inp₀ junkT H c := by
  funext i
  rcases Complexity.layout_cases i with h | h | h | ⟨j, h⟩
  · rw [h, hrf, iterBank_rf]
  · rw [h, hwf, iterBank_wf]
  · rw [h, hjunk, iterBank_junk]
  · rw [h, happ j, iterBank_app]

/-- A parked bank survives a phase boundary. -/
theorem iterBank_trans (M : TM k) (y : List Bool) (inp₀ junkT : Tape)
    (hjunkP : Parked junkT) (H c : ℕ) :
    (fun i => transitionTape (iterBank M y inp₀ junkT H c i))
      = iterBank M y inp₀ junkT H c := by
  funext i
  exact transitionTape_eq_self (iterBank_parked M y inp₀ junkT hjunkP H c i).read_ne_start

/-- The counter is the only tape that changes when the count does. -/
theorem iterBank_succ (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ) :
    iterBank M y inp₀ junkT H (c + 1)
      = Function.update (iterBank M y inp₀ junkT H c) rfIdx (natTape (c + 1)) := by
  funext i
  by_cases hi : i = rfIdx
  · rw [hi, Function.update_self, iterBank_rf]
  · rw [Function.update_of_ne hi, iterBank, iterBank]
    by_cases hm : placeWorkInMiddle 3 (k + 2) i
    · rw [dite_eq_left hm, dite_eq_left hm]
    · rw [dite_eq_right hm, dite_eq_right hm]
      rcases Complexity.layout_cases i with h | h | h | ⟨j, h⟩
      · exact absurd h hi
      · rw [h, bookTapes_wf, bookTapes_wf]
      · rw [h, bookTapes_junk, bookTapes_junk]
      · exact absurd (h ▸ appIdx_middle j) hm

/-! ## The machine -/

/-- The loop body: clear the verdict cell, apply the function once, bump the
counter. -/
def bodyTM (M : TM k) : TM (3 + (k + 2) + 0) :=
  seqTM (seqTM (writeOutputBitTM resIdx) (iterBody M)) (binarySuccTM rfIdx)

/-- The loop test: publish the head symbol of the state. -/
def testTM (k : ℕ) : TM (3 + (k + 2) + 0) := writeOutputBitTM (vinIdx (k := k))

/-! ## The body's contract -/

/-- **Clearing the verdict cell**, from the blank result tape. -/
theorem clear_hoareTime (M : TM k) (y : List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hjunkP : Parked junkT) (H c : ℕ) (s : Γ)
    (hs : s ≠ Γ.start) :
    (writeOutputBitTM (resIdx (k := k))).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = slotOf s)
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = parkedBlank) 1 := by
  have hread : (iterBank M y inp₀ junkT H c (resIdx (k := k))).read = Γ.blank := by
    rw [iterBank_res]
    show parkedBlank.cells parkedBlank.head = Γ.blank
    rw [parkedBlank_cells]
    rfl
  refine (writeOutputBitTM_hoareTime_frame (resIdx (k := k)) inp₀
    (iterBank M y inp₀ junkT H c) (slotOf s) hinpP
    (fun i => iterBank_parked M y inp₀ junkT hjunkP H c i)
    (slotOf_parked s hs)).strengthen_post ?_
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨hi, hw, ?_⟩
  rw [ho, hread, show (readBackWrite Γ.blank).toΓ = Γ.blank from rfl, slotOf_write,
    slotOf_blank]

/-- **Applying the function once.** -/
theorem apply_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (y : List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H c : ℕ)
    (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H) (hGy : (G y).length + 1 ≤ H) :
    (iterBody M).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ work = iterBank M (G y) inp₀ junkT H c ∧
        out = parkedBlank)
      (T y.length + 1 + tailBound k H (G y).length) := by
  have hbody := iterBody_hoareTime M hcomp H y hHy hHT hGy inp₀ hinpP hinpSI
    (natTape c) junkT (natTape_parked c) (natTape_startInvariant c) hjunkP hjunkSI
  refine (hbody.weaken_pre ?_).strengthen_post ?_
  · rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, ho, fun j => by rw [hw, iterBank_app], by rw [hw, iterBank_rf],
      by rw [hw, iterBank_wf], by rw [hw, iterBank_junk]⟩
  · rintro inp work out ⟨hi, ho, hrf, hjunk, hwf, happ⟩
    exact ⟨hi, iterBank_eq M (G y) inp₀ junkT H c work happ hrf hwf hjunk, ho⟩

/-- **Bumping the counter.** -/
theorem bump_hoareTime (M : TM k) (y : List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hjunkP : Parked junkT) (H c : ℕ) :
    (binarySuccTM (rfIdx (k := k))).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H (c + 1) ∧
        out = parkedBlank)
      (binarySuccTime c) := by
  refine (binarySuccTM_hoareTime_pinned (rfIdx (k := k)) c inp₀
    (iterBank M y inp₀ junkT H c) parkedBlank (iterBank_rf M y inp₀ junkT H c)
    hinpP.read_ne_start
    (fun i _ => (iterBank_parked M y inp₀ junkT hjunkP H c i).read_ne_start)
    parked_parkedBlank.read_ne_start).strengthen_post ?_
  rintro inp work out ⟨hi, hw, ho⟩
  exact ⟨hi, by rw [hw, iterBank_succ], ho⟩

/-- **The loop body's contract.** -/
theorem bodyTM_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (y : List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H c : ℕ)
    (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H) (hGy : (G y).length + 1 ≤ H)
    (s : Γ) (hs : s ≠ Γ.start) :
    (bodyTM M).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = slotOf s)
      (fun inp work out => inp = inp₀ ∧
        work = iterBank M (G y) inp₀ junkT H (c + 1) ∧ out = parkedBlank)
      (1 + 1 + (T y.length + 1 + tailBound k H (G y).length) + 1 + binarySuccTime c) := by
  have htrans : ∀ (z : List Bool) (d : ℕ), ∀ inp work out,
      (inp = inp₀ ∧ work = iterBank M z inp₀ junkT H d ∧ out = parkedBlank) →
      (transitionInput inp = inp₀ ∧
        (fun i' => transitionTape (work i')) = iterBank M z inp₀ junkT H d ∧
        transitionTape out = parkedBlank) := by
    rintro z d inp work out ⟨hi, hw, ho⟩
    refine ⟨by rw [hi, transitionInput_eq_self hinpP.read_ne_start], ?_, ?_⟩
    · rw [hw, iterBank_trans M z inp₀ junkT hjunkP H d]
    · rw [ho]
      exact transitionTape_eq_self parked_parkedBlank.read_ne_start
  refine seqTM_hoareTime _ _
    (seqTM_hoareTime _ _
      (mid' := fun inp work out => inp = inp₀ ∧
        work = iterBank M y inp₀ junkT H c ∧ out = parkedBlank)
      (clear_hoareTime M y inp₀ junkT hinpP hjunkP H c s hs)
      (htrans y c)
      (apply_hoareTime M hcomp y inp₀ junkT hinpP hinpSI hjunkP hjunkSI H c hHy hHT hGy))
    (mid' := fun inp work out => inp = inp₀ ∧
      work = iterBank M (G y) inp₀ junkT H c ∧ out = parkedBlank)
    (htrans (G y) c)
    (bump_hoareTime M (G y) inp₀ junkT hinpP hjunkP H c)

/-! ## The test's contract -/

/-- The state tape of a bank reads the state's first symbol. -/
theorem iterBank_vin_read (M : TM k) (y : List Bool) (inp₀ junkT : Tape) (H c : ℕ) :
    (iterBank M y inp₀ junkT H c (vinIdx (k := k))).read = headSym y := by
  rw [vinIdx, iterBank_app, TM.applyPre, Fin.snoc_castSucc]
  show ((TM.retargetInputStartedCfg M y inp₀).work (Fin.last k)).read = headSym y
  rw [show (Fin.last k) = (⟨k, by omega⟩ : Fin (k + 1)) from rfl,
    TM.retargetInputStartedCfg_work_last]
  show (Tape.init (y.map Γ.ofBool)).cells ((Tape.init (y.map Γ.ofBool)).move Dir3.right).head
    = headSym y
  rw [show ((Tape.init (y.map Γ.ofBool)).move Dir3.right).head = 1 from rfl,
    show (1 : ℕ) = 0 + 1 from rfl, Tape.init_cells_succ]
  rfl

/-- **The loop's test.** It publishes the state's first symbol; the programmed
function signals completion by putting a `1` there. -/
theorem testTM_hoareTime (M : TM k) (y : List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hjunkP : Parked junkT) (H c : ℕ) :
    (testTM k).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = slotOf (readBackWrite (headSym y)).toΓ) 1 := by
  refine (writeOutputBitTM_hoareTime_frame (vinIdx (k := k)) inp₀
    (iterBank M y inp₀ junkT H c) parkedBlank hinpP
    (fun i => iterBank_parked M y inp₀ junkT hjunkP H c i)
    parked_parkedBlank).strengthen_post ?_
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨hi, hw, ?_⟩
  rw [ho, iterBank_vin_read]
  rfl

/-! ## The loop -/

/-- The verdict cell at the start of a pass: blank before the first test, the
previous test's verdict afterwards. -/
def slotSym (Y : ℕ → List Bool) (j : ℕ) : Γ :=
  if j = 0 then Γ.blank else (readBackWrite (headSym (Y j))).toΓ

theorem slotSym_ne_start (Y : ℕ → List Bool) (j : ℕ) : slotSym Y j ≠ Γ.start := by
  rw [slotSym]
  split
  · exact fun h => Γ.noConfusion h
  · exact toΓ_readBackWrite_ne_start _

/-- The loop's state after `j` passes, with the counter offset by its starting
value. -/
noncomputable def loopState (M : TM k) (Y : ℕ → List Bool) (inp₀ junkT : Tape)
    (H start j : ℕ) : TapePred (3 + (k + 2) + 0) :=
  fun inp work out => inp = inp₀ ∧
    work = iterBank M (Y j) inp₀ junkT H (start + j) ∧ out = slotOf (slotSym Y j)

theorem loopState_parked (M : TM k) (Y : ℕ → List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hjunkP : Parked junkT) (H start j : ℕ) :
    ∀ inp work out, loopState M Y inp₀ junkT H start j inp work out →
      LoopParked inp work out := by
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hi]; exact hinpP
  · intro i; rw [hw]
    exact iterBank_parked M (Y j) inp₀ junkT hjunkP H (start + j) i
  · rw [ho]; exact slotOf_parked _ (slotSym_ne_start Y j)
  · rw [ho]
    exact (slotOf_startInvariant _ (slotSym_ne_start Y j)).1
  · rw [ho]; exact slotOf_head _

/-- The tapes between the body and the test of a pass: the entry shape for the next
state, with the verdict cell cleared. -/
noncomputable def midState (M : TM k) (Y : ℕ → List Bool) (inp₀ junkT : Tape)
    (H start j : ℕ) : TapePred (3 + (k + 2) + 0) :=
  fun inp work out => inp = inp₀ ∧
    work = iterBank M (Y (j + 1)) inp₀ junkT H (start + (j + 1)) ∧ out = parkedBlank

/-- **The body of a pass** applies the function once and bumps the counter. -/
theorem body_pass (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (Y : ℕ → List Bool) (hY : ∀ i, Y (i + 1) = G (Y i))
    (inp₀ junkT : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H start N : ℕ)
    (hHy : ∀ i, i ≤ N → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i < N → 1 + T (Y i).length ≤ H)
    (j : ℕ) (hj : j < N) :
    (bodyTM M).HoareTime (loopState M Y inp₀ junkT H start j)
      (midState M Y inp₀ junkT H start j)
      (1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (start + j)) := by
  have hGy : (G (Y j)).length + 1 ≤ H := by
    rw [← hY j]
    exact hHy (j + 1) (by omega)
  have hbody := bodyTM_hoareTime M hcomp (Y j) inp₀ junkT hinpP hinpSI hjunkP hjunkSI
    H (start + j) (by have := hHy j (by omega); omega) (hHT j hj) hGy
    (slotSym Y j) (slotSym_ne_start Y j)
  rw [← hY j] at hbody
  refine (hbody.weaken_pre ?_).strengthen_post ?_
  · rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, hw, ho⟩
  · rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨hi, ?_, ho⟩
    rw [hw, show start + j + 1 = start + (j + 1) from by omega]

/-- The tapes between the body and the test are parked. -/
theorem midState_parked (M : TM k) (Y : ℕ → List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hjunkP : Parked junkT) (H start j : ℕ) :
    ∀ inp work out, midState M Y inp₀ junkT H start j inp work out →
      LoopParked inp work out := by
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hi]; exact hinpP
  · intro i; rw [hw]
    exact iterBank_parked M (Y (j + 1)) inp₀ junkT hjunkP H (start + (j + 1)) i
  · rw [ho]; exact parked_parkedBlank
  · rw [ho]
    exact (startInvariant_initNil.move Dir3.right).1
  · rw [ho]; rfl

/-- **The test of a pass** publishes the next state's head symbol. -/
theorem test_pass (M : TM k) (Y : ℕ → List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hjunkP : Parked junkT) (H start j : ℕ) :
    (testTM k).HoareTime (midState M Y inp₀ junkT H start j)
      (loopState M Y inp₀ junkT H start (j + 1)) 1 := by
  refine (testTM_hoareTime M (Y (j + 1)) inp₀ junkT hinpP hjunkP H
    (start + (j + 1))).strengthen_post ?_
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨hi, hw, ?_⟩
  rw [ho, slotSym, ite_eq_right (by omega)]

/-- **One pass of the loop.** The body applies the function once, and the test finds the
state not yet done, so the loop comes back to its start state one iteration on. -/
theorem loop_pass (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (Y : ℕ → List Bool) (hY : ∀ i, Y (i + 1) = G (Y i))
    (inp₀ junkT : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H start N : ℕ)
    (hHy : ∀ i, i ≤ N → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i < N → 1 + T (Y i).length ≤ H)
    (hcont : ∀ i, 0 < i → i < N → (Y i).headD false = false) (b : ℕ)
    (hb : ∀ j, j < N →
      1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (start + j) + 1 + 5 ≤ b) :
    ∀ j, j < N - 1 → ∀ inp work out, loopState M Y inp₀ junkT H start j inp work out →
      ∃ inp' work' out' t, 1 ≤ t ∧ t ≤ b ∧
        (loopTM (bodyTM M) (testTM k)).reachesIn t
          ⟨(loopTM (bodyTM M) (testTM k)).qstart, inp, work, out⟩
          ⟨(loopTM (bodyTM M) (testTM k)).qstart, inp', work', out'⟩ ∧
        loopState M Y inp₀ junkT H start (j + 1) inp' work' out' := by
  intro j hj inp work out hE
  have hjN : j < N := by omega
  have hcontinue := loopTM_continue_of_hoare _ _
    (body_pass M hcomp Y hY inp₀ junkT hinpP hinpSI hjunkP hjunkSI H start N hHy hHT j hjN)
    (test_pass M Y inp₀ junkT hinpP hjunkP H start j)
    (midState_parked M Y inp₀ junkT hinpP hjunkP H start j) ?_ inp work out hE
  · obtain ⟨inp', work', out', t, h1t, ht, hreach, hE'⟩ := hcontinue
    exact ⟨inp', work', out', t, h1t, le_trans ht (hb j hjN), hreach, hE'⟩
  rintro inp' work' out' hE'
  refine ⟨loopState_parked M Y inp₀ junkT hinpP hjunkP H start (j + 1) inp' work' out' hE',
    ?_⟩
  obtain ⟨-, -, ho⟩ := hE'
  rw [ho, slotOf_cells_one, slotSym, ite_eq_right (by omega)]
  intro hcon
  have hhd := (headSym_eq_one_iff (Y (j + 1))).mp hcon
  rw [hcont (j + 1) (by omega) (by omega)] at hhd
  exact Bool.noConfusion hhd

/-- **The last pass of the loop.** The body applies the function one final time, and the
test finds the state done, so the loop halts. -/
theorem loop_final (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (Y : ℕ → List Bool) (hY : ∀ i, Y (i + 1) = G (Y i))
    (inp₀ junkT : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H start N : ℕ)
    (hN : 1 ≤ N)
    (hHy : ∀ i, i ≤ N → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i < N → 1 + T (Y i).length ≤ H)
    (hdone : (Y N).headD false = true) (b : ℕ)
    (hb : ∀ j, j < N →
      1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (start + j) + 1 + 5 ≤ b) :
    ∀ inp work out, loopState M Y inp₀ junkT H start (N - 1) inp work out →
      ∃ c' t, t ≤ b ∧
        (loopTM (bodyTM M) (testTM k)).reachesIn t
          ⟨(loopTM (bodyTM M) (testTM k)).qstart, inp, work, out⟩ c' ∧
        (loopTM (bodyTM M) (testTM k)).halted c' ∧
        loopState M Y inp₀ junkT H start N c'.input c'.work c'.output := by
  intro inp work out hE
  have hlast : N - 1 + 1 = N := by omega
  have hhalt := loopTM_halt_of_hoare _ _
    (body_pass M hcomp Y hY inp₀ junkT hinpP hinpSI hjunkP hjunkSI H start N hHy hHT
      (N - 1) (by omega))
    (test_pass M Y inp₀ junkT hinpP hjunkP H start (N - 1))
    (midState_parked M Y inp₀ junkT hinpP hjunkP H start (N - 1)) ?_ inp work out hE
  · obtain ⟨c', t, ht, hreach, hhlt, hpost⟩ := hhalt
    refine ⟨c', t, le_trans ht (hb (N - 1) (by omega)), hreach, hhlt, ?_⟩
    rw [← hlast]
    exact hpost
  rintro inp' work' out' hE'
  refine ⟨loopState_parked M Y inp₀ junkT hinpP hjunkP H start (N - 1 + 1) inp' work'
    out' hE', ?_⟩
  obtain ⟨-, -, ho⟩ := hE'
  rw [ho, slotOf_cells_one, slotSym, ite_eq_right (by omega), hlast]
  exact (headSym_eq_one_iff (Y N)).mpr hdone

/-- **The loop's contract.** The loop runs until the state says it is done: `N`
passes, each applying the function once. -/
theorem loop_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (Y : ℕ → List Bool) (hY : ∀ i, Y (i + 1) = G (Y i))
    (inp₀ junkT : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H start N : ℕ)
    (hN : 1 ≤ N)
    (hHy : ∀ i, i ≤ N → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i < N → 1 + T (Y i).length ≤ H)
    (hcont : ∀ i, 0 < i → i < N → (Y i).headD false = false)
    (hdone : (Y N).headD false = true) (b : ℕ)
    (hb : ∀ j, j < N →
      1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (start + j) + 1 + 5 ≤ b) :
    (loopTM (bodyTM M) (testTM k)).HoareTime
      (loopState M Y inp₀ junkT H start 0) (loopState M Y inp₀ junkT H start N)
      ((N - 1 + 1) * b) := by
  refine loopTM_hoareTime_indexed _ _ (idx := loopIdx k start) ?_ ?_ ?_
  · rintro j inp work out ⟨hi, hw, ho⟩
    rw [loopIdx, hw, iterBank_rf, ctrValue_natTape]
    omega
  · intro j hj inp work out hE
    obtain ⟨inp', work', out', t, -, ht, hreach, hE'⟩ :=
      loop_pass M hcomp Y hY inp₀ junkT hinpP hinpSI hjunkP hjunkSI H start N hHy hHT
        hcont b hb j hj inp work out hE
    exact ⟨inp', work', out', t, ht, hreach, hE'⟩
  · exact loop_final M hcomp Y hY inp₀ junkT hinpP hinpSI hjunkP hjunkSI H start N hN
      hHy hHT hdone b hb

/-- **The loop's window.** Every configuration the loop passes through lies within one
pass of an indexed state, and each indexed state has every head parked at cell one, so a
window one pass wide holds for the whole run — however many passes it takes. -/
theorem loop_keepsWindowOn (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (Y : ℕ → List Bool) (hY : ∀ i, Y (i + 1) = G (Y i))
    (inp₀ junkT : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H start N : ℕ)
    (hN : 1 ≤ N)
    (hHy : ∀ i, i ≤ N → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i < N → 1 + T (Y i).length ≤ H)
    (hcont : ∀ i, 0 < i → i < N → (Y i).headD false = false)
    (hdone : (Y N).headD false = true) (b : ℕ)
    (hb : ∀ j, j < N →
      1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (start + j) + 1 + 5 ≤ b)
    (lx h₀ : ℕ) (hh₀ : 1 ≤ h₀) (hinph : inp₀.head ≤ lx + h₀ + 1)
    (hjunkh : junkT.head ≤ 1) :
    (loopTM (bodyTM M) (testTM k)).KeepsWindowOn
      (fun c => c.state = (loopTM (bodyTM M) (testTM k)).qstart ∧
        loopState M Y inp₀ junkT H start 0 c.input c.work c.output) lx (h₀ + b) := by
  have hkw := loopTM_keepsWindow_indexed (bodyTM M) (testTM k)
    (inputLength := lx) (space := h₀ + b)
    (loopState M Y inp₀ junkT H start) (N - 1) b
    (loop_pass M hcomp Y hY inp₀ junkT hinpP hinpSI hjunkP hjunkSI H start N hHy hHT
      hcont b hb)
    (fun inp work out hE => by
      obtain ⟨c', t, ht, hreach, hhlt, -⟩ :=
        loop_final M hcomp Y hY inp₀ junkT hinpP hinpSI hjunkP hjunkSI H start N hN
          hHy hHT hdone b hb inp work out hE
      exact ⟨c', t, ht, hreach, hhlt⟩)
    (fun j _ inp work out hE c t ht hreach => by
      obtain ⟨hi, hw, ho⟩ := hE
      obtain ⟨hbi, hbo, hbw⟩ :=
        head_le_start_add_of_reachesIn (loopTM (bodyTM M) (testTM k)) hreach
      dsimp only at hbi hbo hbw
      refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
      · have h1 := hbw i
        have h2 : (work i).head ≤ 1 := by
          rw [hw]
          exact iterBank_head M (Y j) inp₀ junkT hjunkh H (start + j) i
        omega
      · have h1 := hbi
        have h2 : inp.head ≤ lx + h₀ + 1 := by rw [hi]; exact hinph
        omega
      · have h1 := hbo
        have h2 : out.head ≤ 1 := by rw [ho]; exact le_of_eq (slotOf_head _)
        omega)
  rintro c ⟨hst, hE⟩ c' hreach
  refine hkw 0 (by omega) c.input c.work c.output hE c' ?_
  rwa [show (⟨(loopTM (bodyTM M) (testTM k)).qstart, c.input, c.work, c.output⟩ :
    Cfg (3 + (k + 2) + 0) _) = c from Cfg.ext hst.symm rfl rfl rfl]



/-! ## The prologue

`Cobham.iterSetup` puts `pair [] x` on the result tape with the bookkeeping
registers loaded, and `Cobham.iterTail` turns that into the entry shape the loop
starts from — exactly the two phases `Cobham.iterTM` opens with. -/

/-- The prologue: the setup, then the tail that builds the entry shape. -/
def prologueTM (k : ℕ) (p : Polynomial ℕ) : TM (3 + (k + 2) + 0) :=
  seqTM (iterSetup k p) (iterTail k)

/-- The prologue's running time, which is also the width its window needs. -/
def proBound (k : ℕ) (p : Polynomial ℕ) (H n : ℕ) : ℕ :=
  setupBound p n + 1 + tailBound k H (n + 2)

theorem one_le_proBound (k : ℕ) (p : Polynomial ℕ) (H n : ℕ) :
    1 ≤ proBound k p H n := by
  rw [proBound]
  omega

/-- The counter's starting value. `Cobham.iterSetup` leaves `|x|` in unary on the
fuel register, and a unary register of `n` ones read as a binary numeral is
`2 ^ n - 1`. -/
def startCount (n : ℕ) : ℕ := 2 ^ n - 1

theorem regTape_eq_natTape_startCount (n : ℕ) : regTape n = natTape (startCount n) :=
  NTM.regTape_eq_natTape n

/-- **The prologue's contract.** From the initial configuration's tapes it reaches
the loop's entry state for `pair [] x`, with the counter at `startCount |x|`. -/
theorem prologueTM_hoareTime (M : TM k) (p : Polynomial ℕ) (x : List Bool) (H : ℕ)
    (hH : H = p.eval x.length) (hHx : x.length + 4 ≤ H) :
    (prologueTM k p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (pair [] x) inp (regTape H) H (startCount x.length) ∧
        out = parkedBlank)
      (proBound k p H x.length) := by
  rw [proBound]
  have hplen : (pair [] x).length = x.length + 2 := by
    rw [pair_length]
    simp
    omega
  have hsetup := iterSetup_hoareTime (k := k) p x H hH hHx
  -- the seam: the setup's post, pushed through the phase boundary, is the tail's pre
  have hseam : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape),
      (Tape.StartInvariant inp ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (pair [] x) ∧
        (∀ j : Fin (k + 2), Tape.StartInvariant (work (appIdx j)) ∧
          (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        work rfIdx = regTape x.length ∧ work wfIdx = regTape H ∧
        work junkIdx = regTape H) →
      (Parked (transitionInput inp) ∧ Tape.StartInvariant (transitionInput inp) ∧
        transitionTape out = parkedBlank ∧
        ((fun i => transitionTape (work i)) resIdx).HasOutput (pair [] x) ∧
        (∀ j : Fin (k + 2),
          Tape.StartInvariant ((fun i => transitionTape (work i)) (appIdx j)) ∧
          ((fun i => transitionTape (work i)) (appIdx j)).head ≤ H ∧
          ∀ c, H < c → ((fun i => transitionTape (work i)) (appIdx j)).cells c = Γ.blank) ∧
        (fun i => transitionTape (work i)) rfIdx = regTape x.length ∧
        (fun i => transitionTape (work i)) wfIdx = regTape H ∧
        (fun i => transitionTape (work i)) junkIdx = regTape H) := by
    rintro inp work out ⟨hinpSI, rfl, hres, hbnd, hrf, hwf, hjunk⟩
    dsimp only
    have hinpEq : transitionInput inp = (⟨max inp.head 1, inp.cells⟩ : Tape) :=
      move_idleDir_eq_of_startInvariant hinpSI
    refine ⟨?_, ?_, transitionTape_eq_self parked_parkedBlank.read_ne_start, ?_,
      fun j => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hinpEq]; exact ⟨le_max_right _ _, fun c hc => hinpSI.2 c hc⟩
    · rw [hinpEq]; exact ⟨hinpSI.1, fun c hc => hinpSI.2 c hc⟩
    · exact (Tape.hasOutput_congr
        (transitionTape_cells _ (fun c hc => (hbnd (Fin.last (k + 1))).1.2 c hc)).symm _).mp hres
    · refine ⟨?_, fun c hc => ?_⟩
      · rw [transitionTape_cells _ (fun c' hc' => (hbnd j).1.2 c' hc')]
        exact (hbnd j).1.1
      · rw [transitionTape_cells _ (fun c' hc' => (hbnd j).1.2 c' hc')]
        exact (hbnd j).1.2 c hc
    · rw [transitionTape_of_startInvariant (hbnd j).1]
      show max (work (appIdx j)).head 1 ≤ H
      have := (hbnd j).2.1
      omega
    · intro c hc
      rw [transitionTape_cells _ (fun c' hc' => (hbnd j).1.2 c' hc')]
      exact (hbnd j).2.2 c hc
    · show transitionTape (work rfIdx) = regTape x.length
      rw [hrf]; exact transitionTape_eq_self (parked_regTape _).read_ne_start
    · show transitionTape (work wfIdx) = regTape H
      rw [hwf]; exact transitionTape_eq_self (parked_regTape H).read_ne_start
    · show transitionTape (work junkIdx) = regTape H
      rw [hjunk]; exact transitionTape_eq_self (parked_regTape H).read_ne_start
  have htail : (iterTail k).HoareTime
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (pair [] x) ∧
        (∀ j : Fin (k + 2), Tape.StartInvariant (work (appIdx j)) ∧
          (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        work rfIdx = regTape x.length ∧ work wfIdx = regTape H ∧
        work junkIdx = regTape H)
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (pair [] x) inp (regTape H) H (startCount x.length) ∧
        out = parkedBlank)
      (tailBound k H (x.length + 2)) := by
    rintro inp work out ⟨hP, hSI, ho, hres, hbnd, hrf, hwf, hjunk⟩
    obtain ⟨c', t, ht, hreach, hhalt, hi', ho', hrf', hjunk', hwf', happ'⟩ :=
      iterTail_hoareTime M H (pair [] x) (by omega) inp hP hSI (regTape x.length)
        (regTape H) (parked_regTape _) (startInvariant_regTape _) (parked_regTape H)
        (startInvariant_regTape H) inp work out ⟨rfl, ho, hres, hbnd, hrf, hwf, hjunk⟩
    refine ⟨c', t, by rw [hplen] at ht; exact ht, hreach, hhalt, by rw [hi']; exact hP,
      by rw [hi']; exact hSI, ?_, ho'⟩
    refine iterBank_eq M (pair [] x) c'.input (regTape H) H (startCount x.length) c'.work
      (fun j => by rw [happ' j, hi']) ?_ hwf' hjunk'
    rw [hrf', regTape_eq_natTape_startCount]
  exact seqTM_hoareTime _ _ hsetup hseam htail


/-! ## The epilogue

The loop leaves the state saying it is done; one more application turns that
state into the one whose head is the answer, and one more publication puts it in
the verdict cell. -/

theorem headSym_eq_zero_iff {y : List Bool} (hy : y ≠ []) :
    (readBackWrite (headSym y)).toΓ = Γ.zero ↔ y.headD false = false := by
  cases y with
  | nil => exact absurd rfl hy
  | cons b y => cases b <;> simp [headSym, readBackWrite, Γ.ofBool, Γw.toΓ]

/-- The epilogue: one more application, then publish the state's head. -/
def epilogueTM (M : TM k) : TM (3 + (k + 2) + 0) := seqTM (bodyTM M) (testTM k)

/-- **The epilogue's contract.** -/
theorem epilogueTM_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (y : List Bool) (inp₀ junkT : Tape)
    (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) (H c : ℕ)
    (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H) (hGy : (G y).length + 1 ≤ H)
    (s : Γ) (hs : s ≠ Γ.start) :
    (epilogueTM M).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterBank M y inp₀ junkT H c ∧
        out = slotOf s)
      (fun inp work out => inp = inp₀ ∧
        work = iterBank M (G y) inp₀ junkT H (c + 1) ∧
        out = slotOf (readBackWrite (headSym (G y))).toΓ)
      (1 + 1 + (T y.length + 1 + tailBound k H (G y).length) + 1 + binarySuccTime c
        + 1 + 1) := by
  refine seqTM_hoareTime _ _
    (bodyTM_hoareTime M hcomp y inp₀ junkT hinpP hinpSI hjunkP hjunkSI H c hHy hHT hGy s hs)
    ?_ (testTM_hoareTime M (G y) inp₀ junkT hinpP hjunkP H (c + 1))
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨by rw [hi, transitionInput_eq_self hinpP.read_ne_start], ?_, ?_⟩
  · rw [hw, iterBank_trans M (G y) inp₀ junkT hjunkP H (c + 1)]
  · rw [ho]
    exact transitionTape_eq_self parked_parkedBlank.read_ne_start

/-! ## The whole machine -/

/-- The iteration machine: prologue, loop, epilogue. -/
def spaceIterTM (M : TM k) (p : Polynomial ℕ) : TM (3 + (k + 2) + 0) :=
  seqTM (seqTM (prologueTM k p) (loopTM (bodyTM M) (testTM k))) (epilogueTM M)

/-- **The whole machine's contract.** From the initial tapes on `x` it halts with
the head symbol of `Y (N + 1)` in the verdict cell, where `Y` is the orbit of the
programmed function through `pair [] x` and `N` is the first positive index at
which the state says it is done. -/
theorem spaceIterTM_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (p : Polynomial ℕ) (x : List Bool) (H : ℕ)
    (hH : H = p.eval x.length) (hHx : x.length + 4 ≤ H)
    (Y : ℕ → List Bool) (hY0 : Y 0 = pair [] x) (hY : ∀ i, Y (i + 1) = G (Y i))
    (N : ℕ) (hN : 1 ≤ N)
    (hHy : ∀ i, i ≤ N + 1 → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i ≤ N → 1 + T (Y i).length ≤ H)
    (hcont : ∀ i, 0 < i → i < N → (Y i).headD false = false)
    (hdone : (Y N).headD false = true) (b : ℕ)
    (hb : ∀ j, j ≤ N →
      1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (startCount x.length + j) + 1 + 5 ≤ b) :
    (spaceIterTM M p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _inp _work out => out = slotOf (readBackWrite (headSym (Y (N + 1)))).toΓ)
      (proBound k p H x.length + 1 + (N - 1 + 1) * b + 1 + b) := by
  set start := startCount x.length with hstart
  set junkT : Tape := regTape H with hjunkT
  have hjunkP : Parked junkT := parked_regTape H
  have hjunkSI : Tape.StartInvariant junkT := startInvariant_regTape H
  -- the loop, with the input tape read off the configuration
  have hloop : (loopTM (bodyTM M) (testTM k)).HoareTime
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y 0) inp junkT H start ∧ out = parkedBlank)
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y N) inp junkT H (start + N) ∧
        out = slotOf (slotSym Y N)) ((N - 1 + 1) * b) := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    obtain ⟨c', t, ht, hreach, hhalt, hi', hw', ho'⟩ :=
      loop_hoareTime M hcomp Y hY inp junkT hP hSI hjunkP hjunkSI H start N hN
        (fun i hi => hHy i (by omega)) (fun i hi => hHT i (by omega)) hcont hdone b
        (fun j hj => hb j (by omega)) inp work out
        ⟨rfl, by rw [hw, show start + 0 = start from rfl],
          by rw [ho, slotSym, ite_eq_left rfl, slotOf_blank]⟩
    exact ⟨c', t, ht, hreach, hhalt, by rw [hi']; exact hP, by rw [hi']; exact hSI,
      by rw [hw', hi'], ho'⟩
  -- the epilogue, likewise
  have hepi : (epilogueTM M).HoareTime
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y N) inp junkT H (start + N) ∧
        out = slotOf (slotSym Y N))
      (fun _inp _work out => out = slotOf (readBackWrite (headSym (Y (N + 1)))).toΓ) b := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    obtain ⟨c', t, ht, hreach, hhalt, -, -, ho'⟩ :=
      epilogueTM_hoareTime M hcomp (Y N) inp junkT hP hSI hjunkP hjunkSI H (start + N)
        (by have := hHy N (by omega); omega) (hHT N le_rfl)
        (by rw [← hY N]; exact hHy (N + 1) le_rfl) (slotSym Y N) (slotSym_ne_start Y N)
        inp work out ⟨rfl, hw, ho⟩
    refine ⟨c', t, le_trans ht ?_, hreach, hhalt, ?_⟩
    · have := hb N le_rfl
      rw [← hY N]
      omega
    · rw [ho', hY N]
  -- the two seams
  have hseam1 : ∀ inp work out,
      (Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (pair [] x) inp junkT H start ∧ out = parkedBlank) →
      (Parked (transitionInput inp) ∧ Tape.StartInvariant (transitionInput inp) ∧
        (fun i => transitionTape (work i)) =
          iterBank M (Y 0) (transitionInput inp) junkT H start ∧
        transitionTape out = parkedBlank) := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    rw [transitionInput_eq_self hP.read_ne_start]
    refine ⟨hP, hSI, ?_, ?_⟩
    · rw [hw, hY0, iterBank_trans M (pair [] x) inp junkT hjunkP H start]
    · rw [ho]
      exact transitionTape_eq_self parked_parkedBlank.read_ne_start
  have hseam2 : ∀ inp work out,
      (Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y N) inp junkT H (start + N) ∧ out = slotOf (slotSym Y N)) →
      (Parked (transitionInput inp) ∧ Tape.StartInvariant (transitionInput inp) ∧
        (fun i => transitionTape (work i)) =
          iterBank M (Y N) (transitionInput inp) junkT H (start + N) ∧
        transitionTape out = slotOf (slotSym Y N)) := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    rw [transitionInput_eq_self hP.read_ne_start]
    refine ⟨hP, hSI, ?_, ?_⟩
    · rw [hw, iterBank_trans M (Y N) inp junkT hjunkP H (start + N)]
    · rw [ho]
      exact transitionTape_eq_self
        (slotOf_parked _ (slotSym_ne_start Y N)).read_ne_start
  exact seqTM_hoareTime _ _
    (seqTM_hoareTime _ _ (prologueTM_hoareTime M p x H hH hHx) hseam1 hloop) hseam2 hepi


/-! ## The machine's window

The prologue and the epilogue are short, so their windows come from their running
times. The loop's does not — it runs for as long as the programmed computation
does — but every configuration it passes through is within one pass of an indexed
state whose heads are all parked, so one pass' width is enough. -/

/-- A halting contract, read as a reachability fact about a configuration already in
the machine's start state. -/
theorem hoarePostOf {m : ℕ} {tm : TM m} {pre post : TapePred m} {bnd : ℕ}
    (h : tm.HoareTime pre post bnd) (c : Cfg m tm.Q) (hst : c.state = tm.qstart)
    (hpre : pre c.input c.work c.output) :
    ∃ e, tm.reaches c e ∧ tm.halted e ∧ post e.input e.work e.output := by
  obtain ⟨e, t, -, hreach, hhalt, hpost⟩ := h c.input c.work c.output hpre
  refine ⟨e, ?_, hhalt, hpost⟩
  rw [show (⟨tm.qstart, c.input, c.work, c.output⟩ : Cfg m tm.Q) = c from
    Cfg.ext hst.symm rfl rfl rfl] at hreach
  exact reaches_of_reachesIn hreach

/-- **The whole machine's window.** -/
theorem spaceIterTM_keepsWindow (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (p : Polynomial ℕ) (x : List Bool) (H : ℕ)
    (hH : H = p.eval x.length) (hHx : x.length + 4 ≤ H)
    (Y : ℕ → List Bool) (hY0 : Y 0 = pair [] x) (hY : ∀ i, Y (i + 1) = G (Y i))
    (N : ℕ) (hN : 1 ≤ N)
    (hHy : ∀ i, i ≤ N + 1 → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i ≤ N → 1 + T (Y i).length ≤ H)
    (hcont : ∀ i, 0 < i → i < N → (Y i).headD false = false)
    (hdone : (Y N).headD false = true) (b : ℕ)
    (hb : ∀ j, j ≤ N →
      1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (startCount x.length + j) + 1 + 5 ≤ b)
    (W : ℕ) (hW : proBound k p H x.length + 1 + b ≤ W) :
    ∀ c, (spaceIterTM M p).reaches ((spaceIterTM M p).initCfg x) c →
      c.WithinDecisionSpace x.length W := by
  have hproB1 : 1 ≤ proBound k p H x.length := one_le_proBound k p H x.length
  have hs : 1 ≤ W := by omega
  set junkT : Tape := regTape H with hjunkTdef
  have hjunkP : Parked junkT := parked_regTape H
  have hjunkSI : Tape.StartInvariant junkT := startInvariant_regTape H
  have hjunkh : junkT.head ≤ 1 := le_of_eq (regT_head H)
  set st := startCount x.length with hstdef
  -- the prologue, with the head bounds the downstream stages need
  have hproHT : (prologueTM k p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => (Parked inp ∧ Tape.StartInvariant inp ∧
          work = iterBank M (pair [] x) inp junkT H st ∧ out = parkedBlank) ∧
        (∀ i, (work i).head ≤ 0 + proBound k p H x.length) ∧
        inp.head ≤ 0 + proBound k p H x.length ∧
        out.head ≤ 0 + proBound k p H x.length)
      (proBound k p H x.length) :=
    (prologueTM_hoareTime M p x H hH hHx).headBound 0
      (by
        rintro inp work out ⟨hi, hw, ho⟩
        exact ⟨fun i => by rw [hw]; exact le_of_eq (Tape.init_head _),
          by rw [hi]; exact le_of_eq (Tape.init_head _),
          by rw [ho]; exact le_of_eq (Tape.init_head _)⟩)
  -- the loop, from the tapes the prologue leaves
  have hloopHT : (loopTM (bodyTM M) (testTM k)).HoareTime
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        inp.head ≤ proBound k p H x.length ∧
        work = iterBank M (Y 0) inp junkT H st ∧ out = parkedBlank)
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        inp.head ≤ proBound k p H x.length ∧
        work = iterBank M (Y N) inp junkT H (st + N) ∧ out = slotOf (slotSym Y N))
      ((N - 1 + 1) * b) := by
    rintro inp work out ⟨hP, hSI, hhead, hw, ho⟩
    obtain ⟨c', t, ht, hreach, hhalt, hi', hw', ho'⟩ :=
      loop_hoareTime M hcomp Y hY inp junkT hP hSI hjunkP hjunkSI H st N hN
        (fun i hi => hHy i (by omega)) (fun i hi => hHT i (by omega)) hcont hdone b
        (fun j hj => hb j (by omega)) inp work out
        ⟨rfl, by rw [hw, show st + 0 = st from rfl],
          by rw [ho, slotSym, ite_eq_left rfl, slotOf_blank]⟩
    exact ⟨c', t, ht, hreach, hhalt, by rw [hi']; exact hP, by rw [hi']; exact hSI,
      by rw [hi']; exact hhead, by rw [hw', hi'], ho'⟩
  -- the prologue and the loop, as one contract
  have hAHT : (seqTM (prologueTM k p) (loopTM (bodyTM M) (testTM k))).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        inp.head ≤ proBound k p H x.length ∧
        work = iterBank M (Y N) inp junkT H (st + N) ∧ out = slotOf (slotSym Y N))
      (proBound k p H x.length + 1 + (N - 1 + 1) * b) := by
    refine seqTM_hoareTime _ _ hproHT ?_ hloopHT
    rintro inp work out ⟨⟨hP, hSI, hw, ho⟩, hwh, hih, hoh⟩
    rw [transitionInput_eq_self hP.read_ne_start]
    refine ⟨hP, hSI, by omega, ?_, ?_⟩
    · rw [hw, hY0, iterBank_trans M (pair [] x) inp junkT hjunkP H st]
    · rw [ho]
      exact transitionTape_eq_self parked_parkedBlank.read_ne_start
  -- the three windows
  have w1 : (prologueTM k p).KeepsWindowOn
      (fun c => c.state = (prologueTM k p).qstart ∧
        (c.input = Tape.init (x.map Γ.ofBool) ∧ c.work = (fun _ => Tape.init []) ∧
          c.output = Tape.init [])) x.length W :=
    (keepsWindowOn_of_hoareTime (prologueTM_hoareTime M p x H hH hHx)
      (inputLength := x.length) (h₀ := 0)
      (fun inp work out hpre i => by rw [hpre.2.1]; exact le_of_eq (Tape.init_head _))
      (fun inp work out hpre => by rw [hpre.1, Tape.init_head]; omega)
      (fun inp work out hpre => by rw [hpre.2.2, Tape.init_head]; omega)).mono_space
      (by omega)
  have w2 : (loopTM (bodyTM M) (testTM k)).KeepsWindowOn
      (fun c => c.state = (loopTM (bodyTM M) (testTM k)).qstart ∧ Parked c.input ∧
        Tape.StartInvariant c.input ∧ c.input.head ≤ proBound k p H x.length ∧
        c.work = iterBank M (Y 0) c.input junkT H st ∧ c.output = parkedBlank)
      x.length W := by
    rintro c ⟨hst, hP, hSI, hhead, hw, ho⟩ c' hreach
    refine (loop_keepsWindowOn M hcomp Y hY c.input junkT hP hSI hjunkP hjunkSI H st N hN
      (fun i hi => hHy i (by omega)) (fun i hi => hHT i (by omega)) hcont hdone b
      (fun j hj => hb j (by omega)) x.length (proBound k p H x.length + 1) (by omega) (by omega)
      hjunkh).mono_space (by omega) c ⟨hst, rfl, ?_, ?_⟩ c' hreach
    · rw [hw, show st + 0 = st from rfl]
    · rw [ho, slotSym, ite_eq_left rfl, slotOf_blank]
  have w3 : (epilogueTM M).KeepsWindowOn
      (fun c => c.state = (epilogueTM M).qstart ∧ Parked c.input ∧
        Tape.StartInvariant c.input ∧ c.input.head ≤ proBound k p H x.length ∧
        c.work = iterBank M (Y N) c.input junkT H (st + N) ∧
        c.output = slotOf (slotSym Y N)) x.length W := by
    rintro c ⟨hst, hP, hSI, hhead, hw, ho⟩ c' hreach
    have hbN := hb N le_rfl
    refine (keepsWindowOn_of_hoareTime
      (epilogueTM_hoareTime M hcomp (Y N) c.input junkT hP hSI hjunkP hjunkSI H (st + N)
        (by have := hHy N (by omega); omega) (hHT N le_rfl)
        (by rw [← hY N]; exact hHy (N + 1) le_rfl) (slotSym Y N) (slotSym_ne_start Y N))
      (inputLength := x.length) (h₀ := proBound k p H x.length)
      (fun inp work out hpre i => by
        rw [hpre.2.1]
        exact le_trans (iterBank_head M (Y N) c.input junkT hjunkh H (st + N) i) hproB1)
      (fun inp work out hpre => by rw [hpre.1]; omega)
      (fun inp work out hpre => by
        rw [hpre.2.2, slotOf_head]
        omega)).mono_space ?_ c ⟨hst, rfl, hw, ho⟩ c' hreach
    rw [← hY N]
    omega
  -- compose
  have cA := seqTM_keepsWindowOn (prologueTM k p) (loopTM (bodyTM M) (testTM k)) hs
    (mid := fun inp work out => (Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (pair [] x) inp junkT H st ∧ out = parkedBlank) ∧
      (∀ i, (work i).head ≤ 0 + proBound k p H x.length) ∧
      inp.head ≤ 0 + proBound k p H x.length ∧
      out.head ≤ 0 + proBound k p H x.length)
    (fun c hc => by
      obtain ⟨hi, hw, ho⟩ := hc.2
      refine ⟨hc.1, ⟨⟨fun i => by rw [hw, Tape.init_head]; omega,
        by rw [hi, Tape.init_head]; omega⟩, by rw [ho, Tape.init_head]; omega⟩,
        ?_, ?_, ?_⟩
      · rw [hi]; exact Tape.StartInvariant.init_ofBool x
      · intro i; rw [hw]; exact Tape.StartInvariant.init_nil
      · rw [ho]; exact Tape.StartInvariant.init_nil)
    w1 (fun c hc => hoarePostOf hproHT c hc.1 hc.2) w2
    (fun inp work out h => by
      obtain ⟨⟨hP, hSI, hw, ho⟩, hwh, hih, hoh⟩ := h
      rw [transitionInput_eq_self hP.read_ne_start]
      refine ⟨rfl, hP, hSI, ?_, ?_, ?_⟩
      · show inp.head ≤ proBound k p H x.length
        omega
      · rw [hw, hY0, iterBank_trans M (pair [] x) inp junkT hjunkP H st]
      · rw [ho]
        exact transitionTape_eq_self parked_parkedBlank.read_ne_start)
  have cB := seqTM_keepsWindowOn (seqTM (prologueTM k p) (loopTM (bodyTM M) (testTM k)))
    (epilogueTM M) hs
    (mid := fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
      inp.head ≤ proBound k p H x.length ∧
      work = iterBank M (Y N) inp junkT H (st + N) ∧ out = slotOf (slotSym Y N))
    (fun c hc => by
      obtain ⟨d, hd, rfl⟩ := hc
      obtain ⟨hi, hw, ho⟩ := hd.2
      refine ⟨by
          rw [show (phase1Wrap (prologueTM k p) (loopTM (bodyTM M) (testTM k)) d).state
            = Sum.inl d.state from rfl, hd.1]
          rfl, ⟨⟨fun i => ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
      · show (d.work i).head ≤ W
        rw [hw, Tape.init_head]; omega
      · show d.input.head ≤ x.length + W + 1
        rw [hi, Tape.init_head]; omega
      · show d.output.head ≤ W + 1
        rw [ho, Tape.init_head]; omega
      · show Tape.StartInvariant d.input
        rw [hi]; exact Tape.StartInvariant.init_ofBool x
      · show ∀ i, Tape.StartInvariant (d.work i)
        intro i; rw [hw]; exact Tape.StartInvariant.init_nil
      · show Tape.StartInvariant d.output
        rw [ho]; exact Tape.StartInvariant.init_nil)
    cA
    (fun c hc => by
      obtain ⟨d, hd, rfl⟩ := hc
      exact hoarePostOf hAHT _ (by
        rw [show (phase1Wrap (prologueTM k p) (loopTM (bodyTM M) (testTM k)) d).state
          = Sum.inl d.state from rfl, hd.1]
        rfl) hd.2)
    w3
    (fun inp work out h => by
      obtain ⟨hP, hSI, hhead, hw, ho⟩ := h
      rw [transitionInput_eq_self hP.read_ne_start]
      refine ⟨rfl, hP, hSI, hhead, ?_, ?_⟩
      · rw [hw, iterBank_trans M (Y N) inp junkT hjunkP H (st + N)]
      · rw [ho]
        exact transitionTape_eq_self (slotOf_parked _ (slotSym_ne_start Y N)).read_ne_start)
  intro c hreach
  refine cB _ ⟨phase1Wrap (prologueTM k p) (loopTM (bodyTM M) (testTM k))
      ⟨(prologueTM k p).qstart, Tape.init (x.map Γ.ofBool), fun _ => Tape.init [],
        Tape.init []⟩,
    ⟨⟨(prologueTM k p).qstart, Tape.init (x.map Γ.ofBool), fun _ => Tape.init [],
      Tape.init []⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩, rfl⟩ c hreach


/-! ## Iterating a polynomial-time function in polynomial space

Everything above is stated for an explicit `H`, `N` and per-pass bound `b`. Here
they are supplied: `H` is the padding polynomial of `Cobham.iterTM`, `b` is one
pass' running time, and the window is their sum — a polynomial, because the only
unbounded quantity, the iteration count, enters only through the *number of bits*
of the counter. -/

/-- One pass' running time, as a function of the input length: an application of
the programmed function, the tail that restores the entry shape, and an increment
of a counter of `n + w(n) + 1` bits. -/
def passBound (k : ℕ) (tp p r w : Polynomial ℕ) (n : ℕ) : ℕ :=
  1 + 1 + (tp.eval (r.eval n) + 1 + tailBound k (p.eval n) (r.eval n)) + 1 +
    (2 * (n + w.eval n + 1) + 2) + 1 + 5

/-- The machine's window: the prologue, and one pass. -/
def windowBound (k : ℕ) (tp p r w : Polynomial ℕ) (n : ℕ) : ℕ :=
  proBound k p (p.eval n) n + 1 + passBound k tp p r w n

theorem polyBound_windowBound (k : ℕ) (tp p r w : Polynomial ℕ) :
    PolyBound (windowBound k tp p r w) := by
  have hcomp : PolyBound (fun n => tp.eval (r.eval n)) :=
    PolyBound.mono (PolyBound.eval (tp.comp r))
      (fun n => le_of_eq (by rw [Polynomial.eval_comp]))
  have hr : PolyBound (fun n => r.eval n) := PolyBound.eval r
  have hw : PolyBound (fun n => w.eval n) := PolyBound.eval w
  have hpass : PolyBound (passBound k tp p r w) := by
    rw [show passBound k tp p r w = fun n =>
      1 + 1 + (tp.eval (r.eval n) + 1 + tailBound k (p.eval n) (r.eval n)) + 1 +
        (2 * (n + w.eval n + 1) + 2) + 1 + 5 from rfl]
    exact PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      (PolyBound.add (PolyBound.const _) (PolyBound.const _))
      (PolyBound.add (PolyBound.add hcomp (PolyBound.const _))
        (polyBound_tailBound k p _ hr))) (PolyBound.const _))
      (PolyBound.add (PolyBound.mul (PolyBound.const 2)
        (PolyBound.add (PolyBound.add PolyBound.id hw) (PolyBound.const _)))
        (PolyBound.const _))) (PolyBound.const _)) (PolyBound.const _)
  rw [show windowBound k tp p r w = fun n =>
    setupBound p n + 1 + tailBound k (p.eval n) (n + 2) + 1 + passBound k tp p r w n from rfl]
  exact PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
    (polyBound_setupBound p) (PolyBound.const _))
    (polyBound_tailBound k p _ (PolyBound.add PolyBound.id (PolyBound.const _))))
    (PolyBound.const _)) hpass

/-- The counter never exceeds `2 ^ (n + w n + 1)`, so it takes `n + w n + 1` bits. -/
theorem startCount_add_size_le (n j W : ℕ) (hj : j ≤ 2 ^ W) :
    (startCount n + j).size ≤ n + W + 1 := by
  refine Nat.size_le.mpr ?_
  have h1 : startCount n < 2 ^ n := by
    rw [startCount]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ (n + W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ W ≤ 2 ^ (n + W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (2 : ℕ) ^ (n + W + 1) = 2 ^ (n + W) + 2 ^ (n + W) := by ring
  omega

/-- **Iterating a polynomial-time function on a polynomially bounded state is in
`PSPACE`**, however many iterations it takes. The function is applied to
`pair [] x` over and over; it signals completion by putting a `1` at the head of
its state, and the head of the state one application later is the answer. -/
theorem mem_PSPACE_of_iterate {L : Language} {G : List Bool → List Bool}
    (hG : G ∈ FP) (r w : Polynomial ℕ) (Nof : List Bool → ℕ)
    (hlen : ∀ (x : List Bool) (i : ℕ), i ≤ Nof x + 1 →
      (G^[i] (pair [] x)).length ≤ r.eval x.length)
    (hN1 : ∀ x : List Bool, 1 ≤ Nof x)
    (hNw : ∀ x : List Bool, Nof x ≤ 2 ^ w.eval x.length)
    (hcont : ∀ (x : List Bool) (i : ℕ), 0 < i → i < Nof x →
      (G^[i] (pair [] x)).headD false = false)
    (hdone : ∀ x : List Bool, (G^[Nof x] (pair [] x)).headD false = true)
    (hne : ∀ x : List Bool, G^[Nof x + 1] (pair [] x) ≠ [])
    (hans : ∀ x : List Bool, x ∈ L ↔ (G^[Nof x + 1] (pair [] x)).headD false = true) :
    L ∈ PSPACE := by
  obtain ⟨k, M, tp, hcomp⟩ := mem_FP_iff_computesInTime_polynomial.mp hG
  set p : Polynomial ℕ :=
    Polynomial.X + Polynomial.C 4 + r + Polynomial.C 1 + tp.comp r + Polynomial.C 1 with hpdef
  have hpeval : ∀ n, p.eval n = n + 4 + r.eval n + 1 + tp.eval (r.eval n) + 1 := by
    intro n
    rw [hpdef]
    simp [Polynomial.eval_comp]
  obtain ⟨q, hq⟩ := polyBound_windowBound k tp p r w
  -- the standing instances of the two contracts above, at a fixed input
  have key : ∀ x : List Bool,
      (∀ i, i ≤ Nof x + 1 → (G^[i] (pair [] x)).length + 1 ≤ p.eval x.length) ∧
      (∀ i, i ≤ Nof x → 1 + tp.eval (G^[i] (pair [] x)).length ≤ p.eval x.length) ∧
      (∀ j, j ≤ Nof x →
        1 + 1 + (tp.eval (G^[j] (pair [] x)).length + 1 +
            tailBound k (p.eval x.length) (G^[j + 1] (pair [] x)).length) + 1 +
          binarySuccTime (startCount x.length + j) + 1 + 5 ≤
        passBound k tp p r w x.length) := by
    intro x
    have hmono : ∀ i, i ≤ Nof x + 1 →
        tp.eval (G^[i] (pair [] x)).length ≤ tp.eval (r.eval x.length) := fun i hi =>
      polynomial_eval_mono_nat tp (hlen x i hi)
    refine ⟨fun i hi => by have := hlen x i hi; have := hpeval x.length; omega,
      fun i hi => by have := hmono i (by omega); have := hpeval x.length; omega,
      fun j hj => ?_⟩
    have h1 := hmono j (by omega)
    have h2 := tailBound_mono k (p.eval x.length) (hlen x (j + 1) (by omega))
    have h3 : binarySuccTime (startCount x.length + j) ≤
        2 * (x.length + w.eval x.length + 1) + 2 := by
      have h4 := binarySuccTime_le (startCount x.length + j)
      have h5 := startCount_add_size_le x.length j (w.eval x.length)
        (le_trans hj (hNw x))
      omega
    rw [passBound]
    omega
  refine mem_PSPACE_of_polyWindow (spaceIterTM M p) q (fun x c' hreach => ?_) (fun x => ?_)
  · obtain ⟨hHy, hHT, hb⟩ := key x
    exact spaceIterTM_keepsWindow M hcomp p x (p.eval x.length) rfl
      (by have := hpeval x.length; omega) (fun i => G^[i] (pair [] x)) (by simp)
      (fun i => Function.iterate_succ_apply' G i (pair [] x)) (Nof x) (hN1 x) hHy hHT
      (hcont x) (hdone x) (passBound k tp p r w x.length) hb (q.eval x.length)
      (hq x.length) c' hreach
  · obtain ⟨hHy, hHT, hb⟩ := key x
    obtain ⟨c', t, -, hreach, hhalt, hpost⟩ :=
      spaceIterTM_hoareTime M hcomp p x (p.eval x.length) rfl
        (by have := hpeval x.length; omega) (fun i => G^[i] (pair [] x)) (by simp)
        (fun i => Function.iterate_succ_apply' G i (pair [] x)) (Nof x) (hN1 x) hHy hHT
        (hcont x) (hdone x) (passBound k tp p r w x.length) hb
        (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
    refine ⟨c', reaches_of_reachesIn hreach, hhalt, fun hx => ?_, fun hx => ?_⟩
    · rw [hpost, slotOf_cells_one]
      exact (headSym_eq_one_iff _).mpr ((hans x).mp hx)
    · rw [hpost, slotOf_cells_one]
      refine (headSym_eq_zero_iff (hne x)).mpr ?_
      cases hbb : (G^[Nof x + 1] (pair [] x)).headD false with
      | false => rfl
      | true => exact absurd ((hans x).mpr hbb) hx

end SpaceIter

end Complexity

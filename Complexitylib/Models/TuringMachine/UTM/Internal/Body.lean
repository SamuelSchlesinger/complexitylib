/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.UTM.Internal.Desc
public import Complexitylib.Models.TuringMachine.UTM.Internal.VTape
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-!
# The universal machine's loop body

One simulated step of the interpreted description: own halt check, peek
(capture the at-origin flags of the three virtual tapes), seek to the entry
region, first-match key scan, action copy to scratch, apply, or the
no-match default; then cleanup. See `docs/UTM-design.md` (appendix) for the
full state-machine design and the correspondence tricks (q'-length sync via
the state tape, uniform mismatch path, sanitized default moves).

Tape layout: 0 vInput, 1 vWork, 2 vOut (virtual tapes, +1-shift
representation, `VTape.lean`), 3 state, 4 desc, 5 scratch. The real input
and output tapes are untouched (the loop verdict on the output tape is
written by the halt-test machine, not the body).

This file defines the machine only; its `HoareTime` spec and the
correspondence with `TMDesc.toTM.step` live in `BodyInternal.lean` (M3).
-/

@[expose] public section

namespace Complexity

namespace TM.UTMBody

/-- At-origin flags for the three virtual tapes (input, work, output):
    `true` = the simulated head is at position 0 (reading `▷`), captured by
    the peek phase and threaded through the match/apply phases. -/
abbrev VFlags := Bool × Bool × Bool

set_option synthInstance.maxSize 1024 in
set_option maxHeartbeats 1600000 in
/-- Control states of the body machine. See the design appendix. -/
inductive BodyQ where
  /-- Halt check: skip desc field 1 (qstart). -/
  | hc0
  /-- Halt check: lockstep-compare state tape vs desc field 2 (qhalt). -/
  | hc1
  /-- Machine already halted: rewind state, then desc, exit as no-op. -/
  | haltRewS | haltRewD
  /-- Not halted: rewind state, then desc, proceed to peek. -/
  | preRewS | preRewD
  /-- Peek: virtual heads step left, read (▷ ⟺ at sim-origin), step back. -/
  | peek1 | peek2
  /-- Seek desc head past two `□`s to the entry region. -/
  | seek1 (f : VFlags) | seek2 (f : VFlags)
  /-- Key scan: state field (lockstep with state tape). -/
  | cmpQ (f : VFlags)
  /-- Key scan: the six symbol cells (vs live virtual reads). -/
  | cmpS (f : VFlags) (idx : Fin 6)
  /-- Mismatch: skip desc to the cell after the next `□`. -/
  | skipSeg (f : VFlags)
  /-- After a `□`: another `□` means no-match (default); else next segment. -/
  | segCheck (f : VFlags)
  /-- Mismatch cleanup: blank-rewind scratch. -/
  | mmScr (f : VFlags)
  /-- Mismatch cleanup: rewind state head, then resume the key scan. -/
  | rewindSt (f : VFlags)
  /-- Copy the q' field to scratch, state head counting down (trick 1). -/
  | copyQ' (f : VFlags)
  /-- Copy the ten action cells to scratch. -/
  | copyAct (f : VFlags) (j : Fin 10)
  /-- Apply: rewind scratch. -/
  | appRewScr (f : VFlags)
  /-- Apply: overwrite the state tape with the new state (trick 2). -/
  | appQ' (f : VFlags)
  /-- Apply: decode five 2-cell action groups and act (trick 6). -/
  | appAct (f : VFlags) (g : Fin 5) (pending : Option Bool)
  /-- Default path: blank-rewind scratch, blank state, copy qhalt field. -/
  | dfScr | dfStRew | dfBlank | dfStRew2 | dfDescRew | dfSkip | dfCopy
  | dfStRew3 | dfDescRew2
  /-- Cleanup after apply: blank-rewind scratch, rewind state and desc. -/
  | clScr | clSt | clDesc
  /-- Body halt state. -/
  | bodyDone
  deriving DecidableEq, Fintype

open BodyQ

/-- Tape indices, for readability (0 vInput, 1 vWork, 2 vOut, 3 state,
    4 desc, 5 scratch). -/
def vIn : Fin 6 := 0
/-- Work-tape index of the simulated work tape. -/
def vWk : Fin 6 := 1
/-- Work-tape index of the simulated output tape. -/
def vOut : Fin 6 := 2
/-- Work-tape index of the state tape. -/
def stT : Fin 6 := 3
/-- Work-tape index of the description tape. -/
def dsT : Fin 6 := 4
/-- Work-tape index of the scratch tape. -/
def scT : Fin 6 := 5

/-- The simulated read of a virtual tape: `▷` at the origin, else the live
    cell under the (stationary) shadow head. -/
def simRead (flag : Bool) (live : Γ) : Γ :=
  if flag then Γ.start else live

/-- Bit value of a desc-tape cell (`Γ.one ↦ true`, all else `false`). -/
def cellBit (g : Γ) : Bool := g = Γ.one

/-- A bit as the `Γ` symbol a desc-tape cell should hold. -/
def bitCell (b : Bool) : Γ := if b then Γ.one else Γ.zero

/-- Decode a 2-bit group as a write symbol (must match `decΓw`):
    `00→0, 01→1, 10→□, 11→□`. -/
def grpΓw (b₀ b₁ : Bool) : Γw :=
  match b₀, b₁ with
  | false, false => .zero
  | false, true  => .one
  | _,     _     => .blank

/-- Decode a 2-bit group as a direction (must match `decDir`):
    `00→left, 01→right, 10→stay, 11→stay`. -/
def grpDir (b₀ b₁ : Bool) : Dir3 :=
  match b₀, b₁ with
  | false, false => .left
  | false, true  => .right
  | _,     _     => .stay

/-- The expected desc cell at key-symbol index `idx` (0,1 = input symbol's
    two encoding bits; 2,3 = work; 4,5 = output), given the flags and live
    virtual reads. -/
def keyCell (f : VFlags) (v0 v1 v2 : Γ) (idx : Fin 6) : Γ :=
  let enc0 := (simRead f.1 v0).encode
  let enc1 := (simRead f.2.1 v1).encode
  let enc2 := (simRead f.2.2 v2).encode
  match idx with
  | 0 => bitCell enc0[0]!
  | 1 => bitCell enc0[1]!
  | 2 => bitCell enc1[0]!
  | 3 => bitCell enc1[1]!
  | 4 => bitCell enc2[0]!
  | 5 => bitCell enc2[1]!

-- ════════════════════════════════════════════════════════════════════════
-- Transition action builders
-- ════════════════════════════════════════════════════════════════════════

/-- A per-tape action: write this symbol and move this way (direction is
    sanitized against `▷` by the builder). `none` = idle. -/
abbrev TapeActs := Fin 6 → Option (Γw × Dir3)

/-- Build a full δ output from per-work-tape actions; the real input and
    output tapes always idle. Directions are sanitized (`▷ ⇒ right`), so
    `δ_right_of_start` holds by construction. -/
def mkAct (q' : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ) (acts : TapeActs) :
    BodyQ × (Fin 6 → Γw) × Γw × Dir3 × (Fin 6 → Dir3) × Dir3 :=
  (q',
   fun i => match acts i with
     | some (w, _) => w
     | none => readBackWrite (wH i),
   readBackWrite oH,
   idleDir iH,
   fun i => match acts i with
     | some (_, d) => if wH i = Γ.start then Dir3.right else d
     | none => idleDir (wH i),
   idleDir oH)

/-- All tapes idle. -/
def idle (q' : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ) :=
  mkAct q' iH wH oH (fun _ => none)

/-- One active tape. -/
def act1 (q' : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ)
    (t : Fin 6) (w : Γw) (d : Dir3) :=
  mkAct q' iH wH oH (fun i => if i = t then some (w, d) else none)

/-- Two active tapes. -/
def act2 (q' : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ)
    (t₁ : Fin 6) (w₁ : Γw) (d₁ : Dir3) (t₂ : Fin 6) (w₂ : Γw) (d₂ : Dir3) :=
  mkAct q' iH wH oH
    (fun i => if i = t₁ then some (w₁, d₁) else if i = t₂ then some (w₂, d₂) else none)

/-- Three active tapes. -/
def act3 (q' : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ)
    (t₁ : Fin 6) (w₁ : Γw) (d₁ : Dir3) (t₂ : Fin 6) (w₂ : Γw) (d₂ : Dir3)
    (t₃ : Fin 6) (w₃ : Γw) (d₃ : Dir3) :=
  mkAct q' iH wH oH
    (fun i => if i = t₁ then some (w₁, d₁) else if i = t₂ then some (w₂, d₂)
      else if i = t₃ then some (w₃, d₃) else none)

/-- Rewind step for one tape: left until `▷`, bounce right, and continue as
    `next`. -/
def rewStep (cur next : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ) (t : Fin 6) :=
  if wH t = Γ.start then act1 next iH wH oH t (readBackWrite (wH t)) .right
  else act1 cur iH wH oH t (readBackWrite (wH t)) .left

/-- Blank-rewind step for one tape: blank the cell, move left; at `▷`
    bounce right and continue as `next`. -/
def blankRewStep (cur next : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ) (t : Fin 6) :=
  if wH t = Γ.start then act1 next iH wH oH t (readBackWrite (wH t)) .right
  else act1 cur iH wH oH t Γw.blank .left

-- ════════════════════════════════════════════════════════════════════════
-- The transition function
-- ════════════════════════════════════════════════════════════════════════

/-- The body machine's transition function. -/
def bodyδ (q : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ) :
    BodyQ × (Fin 6 → Γw) × Γw × Dir3 × (Fin 6 → Dir3) × Dir3 :=
  let st := wH stT
  let dc := wH dsT
  let sc := wH scT
  match q with
  | hc0 =>
      act1 (if dc = Γ.blank then hc1 else hc0) iH wH oH
        dsT (readBackWrite dc) .right
  | hc1 =>
      if st = Γ.blank ∧ dc = Γ.blank then idle haltRewS iH wH oH
      else if st ≠ Γ.blank ∧ dc ≠ Γ.blank ∧ st = dc then
        act2 hc1 iH wH oH stT (readBackWrite st) .right dsT (readBackWrite dc) .right
      else idle preRewS iH wH oH
  | haltRewS => rewStep haltRewS haltRewD iH wH oH stT
  | haltRewD => rewStep haltRewD bodyDone iH wH oH dsT
  | preRewS => rewStep preRewS preRewD iH wH oH stT
  | preRewD => rewStep preRewD peek1 iH wH oH dsT
  | peek1 =>
      act3 peek2 iH wH oH
        vIn (readBackWrite (wH vIn)) .left
        vWk (readBackWrite (wH vWk)) .left
        vOut (readBackWrite (wH vOut)) .left
  | peek2 =>
      act3 (seek1 (wH vIn = Γ.start, wH vWk = Γ.start, wH vOut = Γ.start)) iH wH oH
        vIn (readBackWrite (wH vIn)) .right
        vWk (readBackWrite (wH vWk)) .right
        vOut (readBackWrite (wH vOut)) .right
  | seek1 f =>
      act1 (if dc = Γ.blank then seek2 f else seek1 f) iH wH oH
        dsT (readBackWrite dc) .right
  | seek2 f =>
      act1 (if dc = Γ.blank then cmpQ f else seek2 f) iH wH oH
        dsT (readBackWrite dc) .right
  | cmpQ f =>
      if st = Γ.blank then idle (cmpS f 0) iH wH oH
      else if dc ≠ Γ.blank ∧ st = dc then
        act2 (cmpQ f) iH wH oH stT (readBackWrite st) .right dsT (readBackWrite dc) .right
      else idle (skipSeg f) iH wH oH
  | cmpS f idx =>
      if dc = keyCell f (wH vIn) (wH vWk) (wH vOut) idx ∧ dc ≠ Γ.blank then
        if h : idx.val < 5 then
          act1 (cmpS f ⟨idx.val + 1, by omega⟩) iH wH oH dsT (readBackWrite dc) .right
        else
          -- key fully matched: desc to the value, state pre-step left (trick 1)
          act2 (copyQ' f) iH wH oH dsT (readBackWrite dc) .right
            stT (readBackWrite st) .left
      else idle (skipSeg f) iH wH oH
  | copyQ' f =>
      if st = Γ.start then
        -- w cells copied; forced bounce lands the state head at cell 1
        act1 (copyAct f 0) iH wH oH stT (readBackWrite st) .right
      else if dc = Γ.blank then idle (skipSeg f) iH wH oH
      else
        act3 (copyQ' f) iH wH oH
          scT (readBackWrite dc) .right
          dsT (readBackWrite dc) .right
          stT (readBackWrite st) .left
  | copyAct f j =>
      if dc = Γ.blank then idle (skipSeg f) iH wH oH
      else
        act2 (if h : j.val < 9 then copyAct f ⟨j.val + 1, by omega⟩ else appRewScr f)
          iH wH oH scT (readBackWrite dc) .right dsT (readBackWrite dc) .right
  | skipSeg f =>
      act1 (if dc = Γ.blank then segCheck f else skipSeg f) iH wH oH
        dsT (readBackWrite dc) .right
  | segCheck f =>
      if dc = Γ.blank then
        -- no-match: default transition; sanitized virtual moves (trick 4)
        act3 dfScr iH wH oH
          vIn (readBackWrite (wH vIn)) (if f.1 then .right else .stay)
          vWk (readBackWrite (wH vWk)) (if f.2.1 then .right else .stay)
          vOut (readBackWrite (wH vOut)) (if f.2.2 then .right else .stay)
      else idle (mmScr f) iH wH oH
  | mmScr f => blankRewStep (mmScr f) (rewindSt f) iH wH oH scT
  | rewindSt f => rewStep (rewindSt f) (cmpQ f) iH wH oH stT
  | appRewScr f => rewStep (appRewScr f) (appQ' f) iH wH oH scT
  | appQ' f =>
      if st = Γ.blank then idle (appAct f 0 none) iH wH oH
      else
        act2 (appQ' f) iH wH oH
          stT (readBackWrite sc) .right
          scT (readBackWrite sc) .right
  | appAct f g pending =>
      match pending with
      | none => act1 (appAct f g (some (cellBit sc))) iH wH oH
          scT (readBackWrite sc) .right
      | some b₀ =>
        let b₁ := cellBit sc
        match g with
        | 0 => -- write ww on vWork (suppressed at origin)
          act2 (appAct f 1 none) iH wH oH
            scT (readBackWrite sc) .right
            vWk (if f.2.1 then Γw.blank else grpΓw b₀ b₁) .stay
        | 1 => -- write wo on vOut (suppressed at origin)
          act2 (appAct f 2 none) iH wH oH
            scT (readBackWrite sc) .right
            vOut (if f.2.2 then Γw.blank else grpΓw b₀ b₁) .stay
        | 2 => -- move vInput
          act2 (appAct f 3 none) iH wH oH
            scT (readBackWrite sc) .right
            vIn (readBackWrite (wH vIn)) (if f.1 then .right else grpDir b₀ b₁)
        | 3 => -- move vWork
          act2 (appAct f 4 none) iH wH oH
            scT (readBackWrite sc) .right
            vWk (readBackWrite (wH vWk)) (if f.2.1 then .right else grpDir b₀ b₁)
        | 4 => -- move vOut, then cleanup
          act2 clScr iH wH oH
            scT (readBackWrite sc) .right
            vOut (readBackWrite (wH vOut)) (if f.2.2 then .right else grpDir b₀ b₁)
  | dfScr => blankRewStep dfScr dfStRew iH wH oH scT
  | dfStRew => rewStep dfStRew dfBlank iH wH oH stT
  | dfBlank =>
      if st = Γ.blank then idle dfStRew2 iH wH oH
      else act1 dfBlank iH wH oH stT Γw.blank .right
  | dfStRew2 => rewStep dfStRew2 dfDescRew iH wH oH stT
  | dfDescRew => rewStep dfDescRew dfSkip iH wH oH dsT
  | dfSkip =>
      act1 (if dc = Γ.blank then dfCopy else dfSkip) iH wH oH
        dsT (readBackWrite dc) .right
  | dfCopy =>
      if dc = Γ.blank then idle dfStRew3 iH wH oH
      else
        act2 dfCopy iH wH oH
          stT (readBackWrite dc) .right
          dsT (readBackWrite dc) .right
  | dfStRew3 => rewStep dfStRew3 dfDescRew2 iH wH oH stT
  | dfDescRew2 => rewStep dfDescRew2 bodyDone iH wH oH dsT
  | clScr => blankRewStep clScr clSt iH wH oH scT
  | clSt => rewStep clSt clDesc iH wH oH stT
  | clDesc => rewStep clDesc bodyDone iH wH oH dsT
  | bodyDone => idle bodyDone iH wH oH

/-- Every direction `mkAct` emits obeys the `▷ ⇒ right` discipline. -/
theorem mkAct_right_of_start (q' : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ)
    (acts : TapeActs) :
    let (_, _, _, inDir, workDirs, outDir) := mkAct q' iH wH oH acts
    (iH = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wH i = Γ.start → workDirs i = Dir3.right) ∧
    (oH = Γ.start → outDir = Dir3.right) := by
  refine ⟨fun h => idleDir_right_of_start h, fun i h => ?_, fun h => idleDir_right_of_start h⟩
  dsimp only [mkAct]
  cases acts i with
  | none => exact idleDir_right_of_start h
  | some wd => simp [h]

/-- Every arm of `bodyδ` is a `mkAct`, so the direction discipline holds
    uniformly. -/
theorem bodyδ_shape (q : BodyQ) (iH : Γ) (wH : Fin 6 → Γ) (oH : Γ) :
    ∃ q' acts, bodyδ q iH wH oH = mkAct q' iH wH oH acts := by
  cases q with
  | appAct f g pending =>
    rcases pending with _ | b₀
    · exact ⟨_, _, rfl⟩
    · fin_cases g <;> exact ⟨_, _, rfl⟩
  | cmpS f idx =>
    simp only [bodyδ, idle, act1, act2]
    split_ifs <;> exact ⟨_, _, rfl⟩
  | _ =>
    simp only [bodyδ, idle, act1, act2, act3, rewStep, blankRewStep]
    first
      | exact ⟨_, _, rfl⟩
      | (split_ifs <;> exact ⟨_, _, rfl⟩)

/-- The body machine. -/
def bodyTM : TM 6 where
  Q := BodyQ
  qstart := hc0
  qhalt := bodyDone
  δ := bodyδ
  δ_right_of_start := by
    intro q iH wH oH
    obtain ⟨q', acts, heq⟩ := bodyδ_shape q iH wH oH
    rw [heq]
    exact mkAct_right_of_start q' iH wH oH acts

end TM.UTMBody

end Complexity

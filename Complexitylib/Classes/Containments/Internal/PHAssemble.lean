/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHPrologue
public import Complexitylib.Classes.Containments.Internal.PHLoop
public import Complexitylib.Classes.Containments.Internal.PHEpilogue

/-!
# The witness enumerator, assembled

⚠️ Unreviewed by Bolton

Five phases: park every head off the marker, copy the input, rewind what the copy left mid-scan,
fill the registers, run the counting loop, and publish whether any witness was accepted.

## Main results

- `PolyExists.enumTM` — the machine
- `PolyExists.enumPark_hoareTime` — its first phase, which parks the initial configuration
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- **The witness enumerator.** -/
def enumTM (M : TM k) (p q : Polynomial ℕ) : TM (enumTapes k) :=
  TM.seqTM TM.skipTM
    (TM.seqTM (TM.copyInputToWorkTM (xIdx k))
      (TM.seqTM (TM.parkRewindTM [xIdx k])
        (TM.seqTM (prologueTM k p q)
          (TM.seqTM (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)))
            (epilogueTM k)))))

/-- **The parking phase.** The initial configuration has every head on the left marker, and no
stage of a composed machine can be entered that way; one step moves them all off. -/
theorem enumPark_hoareTime (k : ℕ) (x : List Bool) :
    (TM.skipTM (n := enumTapes k)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init ([] : List Γ)) ∧ out = Tape.init ([] : List Γ))
      (fun inp work out => inp = strTape x ∧ work = (fun _ => TM.blankTape) ∧
        out = TM.blankTape)
      1 := by
  have hblank : Tape.StartInvariant (Tape.init ([] : List Γ)) := Tape.StartInvariant.init_nil
  have hinit : Tape.StartInvariant (Tape.init (x.map Γ.ofBool)) :=
    Tape.StartInvariant.init_ofBool x
  have hb : (⟨max (Tape.init ([] : List Γ)).head 1, (Tape.init ([] : List Γ)).cells⟩ : Tape)
      = TM.blankTape := by
    refine Tape.ext rfl (funext fun j => ?_)
    show (Tape.init ([] : List Γ)).cells j = _
    rw [TM.blankTape, Tape.move_cells]
  have hi : (⟨max (Tape.init (x.map Γ.ofBool)).head 1, (Tape.init (x.map Γ.ofBool)).cells⟩ :
      Tape) = strTape x := by
    refine Tape.ext rfl (funext fun j => ?_)
    show (Tape.init (x.map Γ.ofBool)).cells j = _
    rw [strTape, Tape.move_cells]
  refine (TM.parkAll_hoareTime (Tape.init (x.map Γ.ofBool))
    (fun _ => Tape.init ([] : List Γ)) (Tape.init ([] : List Γ)) hinit (fun _ => hblank)
    hblank).strengthen_post ?_
  rintro inp work out ⟨hinp, hwork, hout⟩
  exact ⟨by rw [hinp, hi], funext fun i => by rw [hwork i, hb], by rw [hout, hb]⟩

/-- The state the copy phase leaves. -/
def afterCopyX (k : ℕ) (x : List Bool) : TM.TapePred (enumTapes k) := fun inp work out =>
  inp.cells = (strTape x).cells ∧ inp.head = x.length + 1 ∧
  (∀ i, i ≠ xIdx k → work i = TM.blankTape) ∧
  (work (xIdx k)).HasBinaryPrefix x ∧ (work (xIdx k)).cells 0 = Γ.start ∧
  out = TM.blankTape

theorem afterCopyX_parked (k : ℕ) (x : List Bool) {inp : Tape}
    {work : Fin (enumTapes k) → Tape} {out : Tape} (h : afterCopyX k x inp work out) :
    TM.Parked inp ∧ (∀ i, TM.Parked (work i)) ∧ TM.Parked out := by
  obtain ⟨hic, hih, hother, hx, hx0, ho⟩ := h
  have hIp : TM.Parked inp := by
    refine ⟨by omega, fun j hj => ?_⟩
    rw [hic]
    exact (strTape_parked x).2 j hj
  have hxP : TM.Parked (work (xIdx k)) := by
    refine ⟨by rw [hx.1]; omega, fun j hj => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    by_cases hlt : i < x.length
    · rw [hx.2.1 i hlt]
      cases x[i] <;> simp [Γ.ofBool]
    · rw [hx.2.2 i (by omega)]
      simp
  refine ⟨hIp, fun i => ?_, by rw [ho]; exact TM.blankTape_parked⟩
  by_cases hi : i = xIdx k
  · rw [hi]; exact hxP
  · rw [hother i hi]; exact TM.blankTape_parked

/-- Every tape the copy phase leaves is parked, so the boundary after it is the identity. -/
theorem afterCopyX_trans (k : ℕ) (x : List Bool) (inp : Tape)
    (work : Fin (enumTapes k) → Tape) (out : Tape) (h : afterCopyX k x inp work out) :
    afterCopyX k x (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
      (TM.transitionTape out) := by
  obtain ⟨hIp, hwP, hoP⟩ := afterCopyX_parked k x h
  obtain ⟨h1, h2, h3⟩ := trans_id_of_parked hIp hwP hoP
  rw [h1, h2, h3]
  exact h

/-- **The rewinding phase.** The copy left the input and its own target mid-scan; this puts both
back at cell one, which pins the bank the prologue starts from. -/
theorem rewindX_hoareTime (k : ℕ) (x : List Bool) (B : ℕ) (hB : x.length + 1 ≤ B) :
    (TM.parkRewindTM [xIdx k]).HoareTime
      (afterCopyX k x)
      (fun inp work out => inp = strTape x ∧ work = copiedBank k x ∧ out = TM.blankTape)
      (1 + 1 + (2 * (max (B + 2) (1 * (B + 3) + 1) + 1) + 1)) := by
  intro inp work out hpre
  obtain ⟨hIp, hwP, hoP⟩ := afterCopyX_parked k x hpre
  obtain ⟨hic, hih, hother, hx, hx0, ho⟩ := hpre
  have hB1 : 1 ≤ B := by omega
  have hSIw : ∀ i, Tape.StartInvariant (work i) := by
    intro i
    by_cases hi : i = xIdx k
    · rw [hi]
      exact ⟨hx0, fun j hj => (hwP (xIdx k)).2 j hj⟩
    · rw [hother i hi]
      exact TM.blankTape_startInvariant
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpw, hpo⟩ :=
    TM.parkRewindTM_hoareTime [xIdx k] (List.nodup_singleton _) B hB1 inp work out
      ⟨by rw [hic]; exact (strTape_startInvariant x).1, fun j hj => hIp.2 j hj⟩
      hSIw (by rw [ho]; exact TM.blankTape_startInvariant)
      (by omega) (fun j hj => by rw [List.mem_singleton.mp hj, hx.1]; omega)
      inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_, ?_⟩
  · rw [hpi]
    exact Tape.ext rfl hic
  · rw [hpw]
    funext j
    by_cases hj : j = xIdx k
    · rw [hj]
      show (if xIdx k ∈ [xIdx k] then (⟨1, (work (xIdx k)).cells⟩ : Tape) else _)
        = copiedBank k x (xIdx k)
      rw [ite_eq_left (List.mem_singleton.mpr rfl), copiedBank, Function.update_self]
      exact Tape.eq_init_move_right_of_hasBinaryString
        (Tape.hasBinaryString_of_hasBinaryPrefix hx rfl rfl) hx0
    · show (if j ∈ [xIdx k] then _ else TM.parkTape (work j)) = copiedBank k x j
      rw [ite_eq_right (fun hmem => hj (List.mem_singleton.mp hmem)), copiedBank_of_ne k x j hj,
        hother j hj, TM.parkTape]
      exact Tape.ext rfl rfl
  · rw [hpo, ho, TM.parkTape]
    exact Tape.ext rfl rfl

/-- The enumerator's running time: its six phases and the five boundaries between them. -/
def enumTime (p q : Polynomial ℕ) (lx : ℕ) (B N bBody bTest A : ℕ) : ℕ :=
  1 + 1 + ((lx + 1) + 1 +
    ((1 + 1 + (2 * (max (B + 2) (1 * (B + 3) + 1) + 1) + 1)) + 1 +
      (prologueTime p q lx + 1 +
        (N * (bBody + bTest + 5) + 1 + epilogueTime A))))

/-- **The enumerator, contracted.** From its initial configuration the machine ends with `1` in
the verdict slot exactly when some witness of the admitted lengths was accepted. -/
theorem enumTM_hoareTime (M : TM k) {L' : Language} {T S : ℕ → ℕ}
    (hdec : M.DecidesInTime L' T) (hdecS : M.DecidesInSpace L' S)
    (p q : Polynomial ℕ) (x : List Bool) (N H B Hb bBody bTest : ℕ)
    (hNdef : N = 2 ^ (p.eval x.length + 1) - 1) (hHdef : H = q.eval x.length)
    (hN : 1 ≤ N) (hB1 : 1 ≤ B) (hBx : x.length + 1 ≤ B) (hHb1 : 1 ≤ Hb)
    (hpair : ∀ v, v < N → 1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B)
    (hspace : ∀ v, v < N → (pair x (dropTop (v + 1))).length +
      S (pair x (dropTop (v + 1))).length + 2 ≤ Hb)
    (hHbH : Hb + 1 ≤ H)
    (hlenH : ∀ v, v < N → (pair x (dropTop (v + 1))).length + 1 ≤ H)
    (hbodyB : ∀ v, v < N → bodyTime k x T H Hb B v (NTM.tally (enumP L' x) v)
      (NTM.tally (fun u => !enumP L' x u) v) ≤ bBody)
    (heqB : ∀ v, v < N → 1 + 1 + TM.binaryEqTime (v + 1).bits N.bits ≤ B)
    (htestB : ∀ v, v < N → testTime B N v ≤ bTest) :
    (enumTM M p q).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init ([] : List Γ)) ∧ out = Tape.init ([] : List Γ))
      (fun _inp _work out => out = NTM.outSlot (TM.readBackWrite (Γ.ofBool
        (decide (0 < NTM.tally (enumP L' x) N)))))
      (enumTime p q x.length B N bBody bTest (NTM.tally (enumP L' x) N)) := by
  set I : Tape := strTape x with hI
  have hIp : TM.Parked I := strTape_parked x
  have hIsi : Tape.StartInvariant I := strTape_startInvariant x
  have hIhead : I.head = 1 := rfl
  have hIz : I.cells 0 = Γ.start := (strTape_startInvariant x).1
  have hpinned : ∀ (W : Fin (enumTapes k) → Tape) (O : Tape), (∀ i, TM.Parked (W i)) →
      TM.Parked O → ∀ inp work out, (inp = I ∧ work = W ∧ out = O) →
      (TM.transitionInput inp = I ∧ (fun i => TM.transitionTape (work i)) = W ∧
        TM.transitionTape out = O) := by
    rintro W O hW hO inp work out ⟨rfl, rfl, rfl⟩
    exact trans_id_of_parked hIp hW hO
  have hepi := epilogueTM_hoareTime k x N H (NTM.tally (enumP L' x) N)
    (NTM.tally (fun u => !enumP L' x u) N) I hIp hIsi
  have hloop := enumLoop_hoareTime M hdec hdecS x N H hN I hIp hIsi hIhead hIz B Hb bBody bTest
    hB1 hHb1 hpair hspace hHbH hlenH hbodyB heqB htestB
  have hloop' : (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).HoareTime
      (NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H 1) (enumP L' x) 0)
      (fun inp work out => inp = I ∧
        work = enumBank k x N H N (NTM.tally (enumP L' x) N)
          (NTM.tally (fun u => !enumP L' x u) N) ∧ out = NTM.outSlot Γw.one)
      (N * (bBody + bTest + 5)) := by
    refine hloop.strengthen_post ?_
    rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, hw, by rw [ho, ite_eq_left rfl]⟩
  have h56 := TM.seqTM_hoareTime _ _ hloop'
    (hpinned _ _ (enumBank_parked k x N H N _ _) (NTM.outSlot_parked _)) hepi
  have hprol : (prologueTM k p q).HoareTime
      (fun inp work out => inp = I ∧ work = copiedBank k x ∧ out = TM.blankTape)
      (fun inp work out => inp = I ∧ work = enumBank k x N H 0 0 0 ∧ out = TM.blankTape)
      (prologueTime p q x.length) := by
    refine (prologueTM_hoareTime k p q x).strengthen_post ?_
    rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨hi, ?_, ho⟩
    rw [hw, hNdef, hHdef]
  have htrans45 : ∀ inp work out, (inp = I ∧ work = enumBank k x N H 0 0 0 ∧
      out = TM.blankTape) →
      NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H 1) (enumP L' x) 0
        (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
        (TM.transitionTape out) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    obtain ⟨h1, h2, h3⟩ := trans_id_of_parked hIp (enumBank_parked k x N H 0 0 0)
      TM.blankTape_parked
    rw [h1, h2, h3]
    exact ⟨rfl, rfl, Γw.blank, by decide, NTM.outSlot_blank_eq_blankTape.symm⟩
  have h46 := TM.seqTM_hoareTime _ _ hprol htrans45 h56
  have h36 := TM.seqTM_hoareTime _ _ (rewindX_hoareTime k x B hBx)
    (hpinned _ _ (copiedBank_parked k x) TM.blankTape_parked) h46
  have h26 := TM.seqTM_hoareTime _ _ (copyX_hoareTime k x)
    (fun inp work out h => afterCopyX_trans k x inp work out h) h36
  exact TM.seqTM_hoareTime _ _ (enumPark_hoareTime k x)
    (hpinned _ _ (fun _ => TM.blankTape_parked) TM.blankTape_parked) h26

end PolyExists

end Complexity

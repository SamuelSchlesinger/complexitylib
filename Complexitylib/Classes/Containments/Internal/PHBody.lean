/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHBank
public import Complexitylib.Classes.Containments.Internal.PHEmit
public import Complexitylib.Classes.Containments.Internal.PHMatrix
public import Complexitylib.Classes.Containments.Internal.PPBody
public import Complexitylib.Classes.Containments.Internal.PPTest
public import Complexitylib.Models.TuringMachine.Subroutines.CopyToVirtualInput
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryBump
public import Complexitylib.Models.TuringMachine.Hoare.StartInvariant

/-!
# One pass of the witness enumerator

⚠️ Unreviewed by Bolton

An iteration takes the count `v`, tests the witness it denotes, and leaves the loop one count
further along. In order:

1. blank the verdict slot, so the pass starts from a known output;
2. emit `pair x w` onto the first pair tape;
3. rewind the input copy, the witness, and that tape, which the emitter left mid-scan;
4. copy the pair into virtual-input shape on the tape the matrix machine reads;
5. run the matrix machine, which writes its verdict to the verdict tape;
6. rewind the verdict tape, since the matrix machine left its head wherever it halted;
7. publish that verdict into the slot;
8. bump the tally the slot names and advance the counter;
9. advance the witness in step with the counter;
10. blank everything the pass dirtied.

Steps 8 and 10 are the counting machine's own — `TM.tallyBumpTM` and `TM.wipeRewindTM` — and step
9 is what makes the loop's resting bank depend on the count.

## Main results

- `PolyExists.copyPairTM` — the copy into virtual-input shape
- `PolyExists.bodyTM` — one pass of the enumerator
- `PolyExists.enumBank` — the tapes an iteration starts from, and its values at the named indices
- `PolyExists.blankSlot_hoareTime` — the first stage's contract
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- Move the emitted pair onto the tape the matrix machine reads, in the shape it expects. -/
def copyPairTM (k : ℕ) : TM (enumTapes k) :=
  TM.seqTM (TM.copyWorkToWorkTM (y1Idx k) (yIdx k)) (TM.rewindWorkTM (yIdx k))

/-- **One pass of the witness enumerator.** -/
def bodyTM (M : TM k) : TM (enumTapes k) :=
  TM.seqTM (TM.writeOutputBitTM (zIdx k))
    (TM.seqTM (emitTM k)
      (TM.seqTM (TM.parkRewindTM [xIdx k, wIdx k, y1Idx k])
        (TM.seqTM (copyPairTM k)
          (TM.seqTM (matrixTM M)
            (TM.seqTM (TM.parkRewindTM [vIdx k])
              (TM.seqTM (TM.writeOutputBitTM (vIdx k))
                (TM.seqTM (TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k))
                  (TM.seqTM (TM.binaryBumpTM (wIdx k))
                    (TM.wipeRewindTM (scratchTargets k) (regIdx k))))))))))

/-! ## The bank the loop rests in -/

/-- The tapes at count `v` with tallies `a` and `r`: the loop's three registers over the resting
bank. -/
def enumBank (k : ℕ) (x : List Bool) (N H v a r : ℕ) : Fin (enumTapes k) → Tape :=
  tallyWork (cIdx k) (aIdx k) (rIdx k) (enumRest k x N H (v + 1)) (v, a, r)

/-- A tape that is none of the loop's three registers rests where the bank puts it. -/
theorem enumBank_of_ne (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k))
    (hc : i ≠ cIdx k) (ha : i ≠ aIdx k) (hr : i ≠ rIdx k) :
    enumBank k x N H v a r i = enumRest k x N H (v + 1) i := by
  rw [enumBank, tallyWork]
  dsimp only
  rw [ite_eq_right hc, ite_eq_right ha, ite_eq_right hr]

theorem ne_tallyRegs {k : ℕ} (i : Fin (enumTapes k))
    (h2 : i.val ≠ 3 + k + 2) (h5 : i.val ≠ 3 + k + 5) (h8 : i.val ≠ 3 + k + 8) :
    i ≠ cIdx k ∧ i ≠ aIdx k ∧ i ≠ rIdx k :=
  ⟨Fin.ne_of_val_ne h2, Fin.ne_of_val_ne h5, Fin.ne_of_val_ne h8⟩

theorem x_ne_regs (k : ℕ) : xIdx k ≠ cIdx k ∧ xIdx k ≠ aIdx k ∧ xIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show (0 : ℕ) ≠ 3 + k + 2; omega) (by show (0 : ℕ) ≠ 3 + k + 5; omega)
    (by show (0 : ℕ) ≠ 3 + k + 8; omega)

theorem w_ne_regs (k : ℕ) : wIdx k ≠ cIdx k ∧ wIdx k ≠ aIdx k ∧ wIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show (1 : ℕ) ≠ 3 + k + 2; omega) (by show (1 : ℕ) ≠ 3 + k + 5; omega)
    (by show (1 : ℕ) ≠ 3 + k + 8; omega)

theorem y1_ne_regs (k : ℕ) : y1Idx k ≠ cIdx k ∧ y1Idx k ≠ aIdx k ∧ y1Idx k ≠ rIdx k :=
  ne_tallyRegs _ (by show (2 : ℕ) ≠ 3 + k + 2; omega) (by show (2 : ℕ) ≠ 3 + k + 5; omega)
    (by show (2 : ℕ) ≠ 3 + k + 8; omega)

theorem y_ne_regs (k : ℕ) : yIdx k ≠ cIdx k ∧ yIdx k ≠ aIdx k ∧ yIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show 3 + k ≠ 3 + k + 2; omega) (by show 3 + k ≠ 3 + k + 5; omega)
    (by show 3 + k ≠ 3 + k + 8; omega)

theorem v_ne_regs (k : ℕ) : vIdx k ≠ cIdx k ∧ vIdx k ≠ aIdx k ∧ vIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show 3 + k + 1 ≠ 3 + k + 2; omega) (by show 3 + k + 1 ≠ 3 + k + 5; omega)
    (by show 3 + k + 1 ≠ 3 + k + 8; omega)

theorem n_ne_regs (k : ℕ) : nIdx k ≠ cIdx k ∧ nIdx k ≠ aIdx k ∧ nIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show 3 + k + 3 ≠ 3 + k + 2; omega) (by show 3 + k + 3 ≠ 3 + k + 5; omega)
    (by show 3 + k + 3 ≠ 3 + k + 8; omega)

theorem res_ne_regs (k : ℕ) : resIdx k ≠ cIdx k ∧ resIdx k ≠ aIdx k ∧ resIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show 3 + k + 4 ≠ 3 + k + 2; omega) (by show 3 + k + 4 ≠ 3 + k + 5; omega)
    (by show 3 + k + 4 ≠ 3 + k + 8; omega)

theorem z_ne_regs (k : ℕ) : zIdx k ≠ cIdx k ∧ zIdx k ≠ aIdx k ∧ zIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show 3 + k + 6 ≠ 3 + k + 2; omega) (by show 3 + k + 6 ≠ 3 + k + 5; omega)
    (by show 3 + k + 6 ≠ 3 + k + 8; omega)

theorem reg_ne_regs (k : ℕ) : regIdx k ≠ cIdx k ∧ regIdx k ≠ aIdx k ∧ regIdx k ≠ rIdx k :=
  ne_tallyRegs _ (by show 3 + k + 7 ≠ 3 + k + 2; omega) (by show 3 + k + 7 ≠ 3 + k + 5; omega)
    (by show 3 + k + 7 ≠ 3 + k + 8; omega)

@[simp] theorem enumBank_x (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (xIdx k) = strTape x := by
  rw [enumBank_of_ne k x N H v a r _ (x_ne_regs k).1 (x_ne_regs k).2.1 (x_ne_regs k).2.2,
    enumRest_x]

@[simp] theorem enumBank_w (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (wIdx k) = strTape (dropTop (v + 1)) := by
  rw [enumBank_of_ne k x N H v a r _ (w_ne_regs k).1 (w_ne_regs k).2.1 (w_ne_regs k).2.2,
    enumRest_w]

/-- Every scratch tape rests blank. -/
theorem enumRest_blank (k : ℕ) (x : List Bool) (N H v : ℕ) (i : Fin (enumTapes k))
    (hx : i ≠ xIdx k) (hw : i ≠ wIdx k) (hn : i ≠ nIdx k) (hreg : i ≠ regIdx k) :
    enumRest k x N H v i = TM.blankTape := by
  rw [enumRest, ite_eq_right hx, ite_eq_right hw, ite_eq_right hn, ite_eq_right hreg]

theorem enumBank_blank (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k))
    (hc : i ≠ cIdx k) (ha : i ≠ aIdx k) (hr : i ≠ rIdx k)
    (hx : i ≠ xIdx k) (hw : i ≠ wIdx k) (hn : i ≠ nIdx k) (hreg : i ≠ regIdx k) :
    enumBank k x N H v a r i = TM.blankTape := by
  rw [enumBank_of_ne k x N H v a r i hc ha hr,
    enumRest_blank k x N H (v + 1) i hx hw hn hreg]

@[simp] theorem enumBank_y1 (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (y1Idx k) = TM.blankTape :=
  enumBank_blank k x N H v a r _ (y1_ne_regs k).1 (y1_ne_regs k).2.1 (y1_ne_regs k).2.2
    (Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 0; omega))
    (Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 1; omega))
    (Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 3 + k + 3; omega))
    (Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 3 + k + 7; omega))

@[simp] theorem enumBank_z (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (zIdx k) = TM.blankTape :=
  enumBank_blank k x N H v a r _ (z_ne_regs k).1 (z_ne_regs k).2.1 (z_ne_regs k).2.2
    (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 0; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 1; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 3; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 7; omega))

/-- **The bank is parked on every tape.** -/
theorem enumBank_parked (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k)) :
    TM.Parked (enumBank k x N H v a r i) := by
  rw [enumBank, tallyWork]
  dsimp only
  split
  · exact natTape_parked _
  · split
    · exact natTape_parked _
    · split
      · exact natTape_parked _
      · exact enumRest_parked k x N H (v + 1) i

theorem natTape_startInvariant (v : ℕ) : Tape.StartInvariant (natTape v) :=
  ⟨NTM.natTape_cells_zero v, fun j hj => (natTape_parked v).2 j hj⟩

theorem strTape_cells_zero (l : List Bool) : (strTape l).cells 0 = Γ.start :=
  (strTape_startInvariant l).1

/-- **The bank satisfies the left-marker invariant on every tape**, which every rewind, park and
wipe downstream asks of the tapes it carries. -/
theorem enumBank_startInvariant (k : ℕ) (x : List Bool) (N H v a r : ℕ)
    (i : Fin (enumTapes k)) : Tape.StartInvariant (enumBank k x N H v a r i) := by
  rw [enumBank, tallyWork]
  dsimp only
  split
  · exact natTape_startInvariant _
  · split
    · exact natTape_startInvariant _
    · split
      · exact natTape_startInvariant _
      · rw [enumRest]
        split
        · exact strTape_startInvariant x
        · split
          · exact strTape_startInvariant _
          · split
            · exact natTape_startInvariant N
            · split
              · exact regTape_startInvariant H
              · exact TM.blankTape_startInvariant

/-- **Every tape of the bank is parked at cell one.** -/
theorem enumBank_head (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k)) :
    (enumBank k x N H v a r i).head = 1 := by
  have hle : (enumBank k x N H v a r i).head ≤ 1 := by
    rw [enumBank, tallyWork]
    dsimp only
    split
    · exact le_of_eq (Tape.init_move_right_hasBinaryNat _).2.1
    · split
      · exact le_of_eq (Tape.init_move_right_hasBinaryNat _).2.1
      · split
        · exact le_of_eq (Tape.init_move_right_hasBinaryNat _).2.1
        · exact enumRest_head k x N H (v + 1) i
  have hge : 1 ≤ (enumBank k x N H v a r i).head := (enumBank_parked k x N H v a r i).1
  omega

theorem natTape_head_one (v : ℕ) : (natTape v).head = 1 :=
  (Tape.init_move_right_hasBinaryNat v).2.1

/-- **The body's first stage: blank the verdict slot.** The loop returns to its start state with
the previous check's verdict still in the slot; everything downstream — the emitter, the matrix
machine, the wipe — needs the real output tape blank. -/
theorem blankSlot_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) :
    (TM.writeOutputBitTM (zIdx k)).HoareTime
      (fun inp work out => inp = I ∧ work = enumBank k x N H v a r ∧
        ∃ s : Γw, s ≠ Γw.one ∧ out = NTM.outSlot s)
      (fun inp work out => inp = I ∧ work = enumBank k x N H v a r ∧ out = TM.blankTape)
      1 := by
  intro inp work out hpre
  obtain ⟨hi, hw, s, -, ho⟩ := hpre
  refine (TM.writeOutputBitTM_hoareTime_frame (zIdx k) I (enumBank k x N H v a r)
    (NTM.outSlot s) hI (enumBank_parked k x N H v a r) (NTM.outSlot_parked _)).strengthen_post
    (post' := fun inp work out => inp = I ∧ work = enumBank k x N H v a r ∧
      out = TM.blankTape) ?_ inp work out ⟨hi, hw, ho⟩
  rintro inp' work' out' ⟨hi', hw', ho'⟩
  refine ⟨hi', hw', ?_⟩
  have hread : (enumBank k x N H v a r (zIdx k)).read = Γ.blank := by
    rw [enumBank_z]
    exact Tape.init_nil_move_right_read
  rw [ho', hread, ← NTM.outSlot_blank_eq_blankTape]
  show (NTM.outSlot s).write (TM.readBackWrite Γ.blank).toΓ = _
  exact NTM.outSlot_write s Γw.blank

theorem blankTape_eq_parkedBlank : TM.blankTape = TM.parkedBlank := rfl

/-- The tapes after the pair has been emitted and everything the emitter scanned rewound: the
bank, with the pair now on its tape. -/
def afterPair (k : ℕ) (x : List Bool) (N H v a r : ℕ) : Fin (enumTapes k) → Tape :=
  Function.update (enumBank k x N H v a r) (y1Idx k) (strTape (pair x (dropTop (v + 1))))

/-- What the emitter leaves behind: the pair on its tape, both sources with their cells intact,
every other tape untouched, and no head further out than the stage is long. -/
def midEmit (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (B : ℕ) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  inp = I ∧ out = TM.blankTape ∧
  (∀ i, ¬ TM.placeWorkInMiddle (post := k + 9) 0 3 i → work i = enumBank k x N H v a r i) ∧
  (work (xIdx k)).cells = (strTape x).cells ∧
  (work (wIdx k)).cells = (strTape (dropTop (v + 1))).cells ∧
  (work (y1Idx k)).HasBinaryPrefix (pair x (dropTop (v + 1))) ∧
  (∀ i, Tape.StartInvariant (work i)) ∧ (∀ i, (work i).head ≤ B)

/-- **The emitting stage's contract.** -/
theorem emit_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hISI : Tape.StartInvariant I) (B : ℕ)
    (hB : 1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B) :
    (emitTM k).HoareTime
      (fun inp work out => inp = I ∧ work = enumBank k x N H v a r ∧ out = TM.blankTape)
      (midEmit k x N H v a r I B)
      (TM.pairInputWorkTime x (dropTop (v + 1))) := by
  have hbase := emitTM_hoareTime k x (dropTop (v + 1)) (strTape x) rfl
    (Tape.hasOutput_of_hasBinaryString (strTape_hasBinaryString x)) (strTape_startInvariant x)
    (enumBank k x N H v a r)
    (fun i _ => enumBank_startInvariant k x N H v a r i)
    (fun i _ => le_of_eq (enumBank_head k x N H v a r i).symm)
  rintro inp work out ⟨hi, hw, ho⟩
  obtain ⟨c', t, ht, hreach, hhalt, hframe, hxc, hxout, hwc, hy1, hoeq⟩ :=
    hbase inp work out ⟨fun i _ => by rw [hw], by rw [hw, enumBank_x],
      by rw [hw, enumBank_w]; rfl, by rw [hw, enumBank_y1, blankTape_eq_parkedBlank],
      by rw [ho, blankTape_eq_parkedBlank]⟩
  have hSI := TM.reachesIn_startInvariant hreach (by rw [hi]; exact hISI)
    (fun i => by rw [hw]; exact enumBank_startInvariant k x N H v a r i)
    (by rw [ho]; exact TM.blankTape_startInvariant)
  obtain ⟨-, -, hwork⟩ := TM.head_le_start_add_of_reachesIn (emitTM k) hreach
  dsimp only at hwork
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_, hframe, hxc, hwc, hy1, hSI.2.1, fun i => ?_⟩
  · rw [← hi]
    exact TM.reachesIn_input_eq_of_idlesInput
      (show TM.IdlesInput (emitTM k) from fun _ _ _ _ => rfl) hreach (by rw [hi]; exact hI)
  · rw [hoeq, blankTape_eq_parkedBlank]
  · have h1 := hwork i
    have h2 : (work i).head = 1 := by rw [hw]; exact enumBank_head k x N H v a r i
    omega

theorem pairTargets_nodup (k : ℕ) :
    ([xIdx k, wIdx k, y1Idx k] : List (Fin (enumTapes k))).Nodup := by
  have h01 : xIdx k ≠ wIdx k := Fin.ne_of_val_ne (by show (0 : ℕ) ≠ 1; omega)
  have h02 : xIdx k ≠ y1Idx k := Fin.ne_of_val_ne (by show (0 : ℕ) ≠ 2; omega)
  have h12 : wIdx k ≠ y1Idx k := Fin.ne_of_val_ne (by show (1 : ℕ) ≠ 2; omega)
  simp [h01, h02, h12]

/-- A tape of the layout is one of the three the emitter touches exactly when it is inside the
emitter's block. -/
theorem mem_pairTargets_iff (k : ℕ) (j : Fin (enumTapes k)) :
    j ∈ ([xIdx k, wIdx k, y1Idx k] : List (Fin (enumTapes k))) ↔
      TM.placeWorkInMiddle (post := k + 9) 0 3 j := by
  constructor
  · intro h
    refine ⟨Nat.zero_le _, ?_⟩
    rcases List.mem_cons.mp h with h | h
    · rw [h]; show (0 : ℕ) < 0 + 3; omega
    · rcases List.mem_cons.mp h with h | h
      · rw [h]; show (1 : ℕ) < 0 + 3; omega
      · rcases List.mem_cons.mp h with h | h
        · rw [h]; show (2 : ℕ) < 0 + 3; omega
        · exact absurd h (List.not_mem_nil)
  · rintro ⟨-, hlt⟩
    have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases hcases with h | h | h
    · exact List.mem_cons.mpr (Or.inl (Fin.ext h))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (Fin.ext h))))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_cons.mpr (Or.inl (Fin.ext h))))))

/-- **The rewinding stage's contract.** The emitter left three heads mid-scan; this puts them
back at cell one, which pins every tape again. -/
theorem parkPair_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hISI : Tape.StartInvariant I) (hIhead : I.head = 1) (B : ℕ) (hB : 1 ≤ B) :
    (TM.parkRewindTM [xIdx k, wIdx k, y1Idx k]).HoareTime
      (midEmit k x N H v a r I B)
      (fun inp work out => inp = I ∧ work = afterPair k x N H v a r ∧ out = TM.blankTape)
      (1 + 1 + (2 * (max (B + 2) (3 * (B + 3) + 1) + 1) + 1)) := by
  rintro inp work out ⟨hi, ho, hframe, hxc, hwc, hy1, hSI, hhead⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpw, hpo⟩ :=
    TM.parkRewindTM_hoareTime [xIdx k, wIdx k, y1Idx k] (pairTargets_nodup k) B hB inp work out
      (by rw [hi]; exact hISI) hSI (by rw [ho]; exact TM.blankTape_startInvariant)
      (by rw [hi, hIhead]; exact hB) (fun j _ => hhead j)
      inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_, ?_⟩
  · rw [hpi, hi]
    exact Tape.ext hIhead.symm rfl
  · rw [hpw]
    funext j
    by_cases hj : j ∈ ([xIdx k, wIdx k, y1Idx k] : List (Fin (enumTapes k)))
    · rw [ite_eq_left hj]
      rcases List.mem_cons.mp hj with h | h
      · rw [h, afterPair, Function.update_of_ne
          (Fin.ne_of_val_ne (by show (0 : ℕ) ≠ 2; omega)), enumBank_x]
        exact Tape.ext rfl hxc
      · rcases List.mem_cons.mp h with h | h
        · rw [h, afterPair, Function.update_of_ne
            (Fin.ne_of_val_ne (by show (1 : ℕ) ≠ 2; omega)), enumBank_w]
          exact Tape.ext rfl hwc
        · rcases List.mem_cons.mp h with h | h
          · rw [h, afterPair, Function.update_self]
            exact Tape.eq_init_move_right_of_hasBinaryString
              (Tape.hasBinaryString_of_hasBinaryPrefix hy1 rfl rfl) (hSI (y1Idx k)).1
          · exact absurd h (List.not_mem_nil)
    · rw [ite_eq_right hj]
      have hout : ¬ TM.placeWorkInMiddle (post := k + 9) 0 3 j :=
        fun hm => hj ((mem_pairTargets_iff k j).mpr hm)
      have hwj : work j = enumBank k x N H v a r j := hframe j hout
      have hne : j ≠ y1Idx k := fun h => hj (by rw [h]; simp)
      rw [afterPair, Function.update_of_ne hne, ← hwj, TM.parkTape]
      refine Tape.ext ?_ rfl
      show max (work j).head 1 = (work j).head
      rw [hwj, enumBank_head]
      omega
  · rw [hpo, ho, TM.parkTape]
    refine Tape.ext ?_ rfl
    show max TM.blankTape.head 1 = TM.blankTape.head
    rfl

/-- **Every tape of the scratch block rests blank**: the emitter's target, the matrix machine's
own tapes, the tape it reads and the one it writes. -/
theorem enumBank_blank_of_val (k : ℕ) (x : List Bool) (N H v a r : ℕ)
    (i : Fin (enumTapes k)) (h2 : 2 ≤ i.val) (hlt : i.val < 3 + k + 2) :
    enumBank k x N H v a r i = TM.blankTape :=
  enumBank_blank k x N H v a r i
    (Fin.ne_of_val_ne (by show i.val ≠ 3 + k + 2; omega))
    (Fin.ne_of_val_ne (by show i.val ≠ 3 + k + 5; omega))
    (Fin.ne_of_val_ne (by show i.val ≠ 3 + k + 8; omega))
    (Fin.ne_of_val_ne (by show i.val ≠ 0; omega))
    (Fin.ne_of_val_ne (by show i.val ≠ 1; omega))
    (Fin.ne_of_val_ne (by show i.val ≠ 3 + k + 3; omega))
    (Fin.ne_of_val_ne (by show i.val ≠ 3 + k + 7; omega))

@[simp] theorem enumBank_y (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (yIdx k) = TM.blankTape :=
  enumBank_blank_of_val k x N H v a r _ (by show 2 ≤ 3 + k; omega)
    (by show 3 + k < 3 + k + 2; omega)

@[simp] theorem enumBank_v (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (vIdx k) = TM.blankTape :=
  enumBank_blank_of_val k x N H v a r _ (by show 2 ≤ 3 + k + 1; omega)
    (by show 3 + k + 1 < 3 + k + 2; omega)

/-- The tapes after the pair has been moved into the shape the matrix machine reads: the emitter's
target keeps its contents with its head left past them, and the matrix machine's input tape now
holds the pair. -/
def afterCopy (k : ℕ) (x : List Bool) (N H v a r : ℕ) : Fin (enumTapes k) → Tape :=
  Function.update
    (Function.update (enumBank k x N H v a r) (yIdx k) (strTape (pair x (dropTop (v + 1)))))
    (y1Idx k)
    (⟨(pair x (dropTop (v + 1))).length + 1, (strTape (pair x (dropTop (v + 1)))).cells⟩ : Tape)

/-- **The copying stage's contract.** -/
theorem copyPair_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) :
    (copyPairTM k).HoareTime
      (fun inp work out => inp = I ∧ work = afterPair k x N H v a r ∧ out = TM.blankTape)
      (fun inp work out => inp = I ∧ work = afterCopy k x N H v a r ∧ out = TM.blankTape)
      (2 * (pair x (dropTop (v + 1))).length + 5) := by
  have hne : y1Idx k ≠ yIdx k := Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 3 + k; omega)
  have hsrc : afterPair k x N H v a r (y1Idx k) = strTape (pair x (dropTop (v + 1))) := by
    rw [afterPair, Function.update_self]
  have hdst : afterPair k x N H v a r (yIdx k) = TM.blankTape := by
    rw [afterPair, Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k ≠ 2; omega)),
      enumBank_y]
  have hpark : ∀ i, TM.Parked (afterPair k x N H v a r i) := by
    intro i
    rw [afterPair]
    by_cases hi : i = y1Idx k
    · rw [hi, Function.update_self]
      exact strTape_parked _
    · rw [Function.update_of_ne hi]
      exact enumBank_parked k x N H v a r i
  rintro inp work out ⟨rfl, rfl, rfl⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpo, hpdst, hpsrcCells, hpsrcHead, hpother⟩ :=
    TM.copyToVirtualInput_hoareTime (y1Idx k) (yIdx k) hne (pair x (dropTop (v + 1))) inp
      (afterPair k x N H v a r) TM.blankTape
      (by rw [hsrc]; rfl)
      (by rw [hsrc]; exact Tape.hasOutput_of_hasBinaryString (strTape_hasBinaryString _))
      (by rw [hsrc]; exact strTape_parked _)
      (by rw [hdst]; rfl)
      hI TM.blankTape_parked
      (fun i _ _ => hpark i)
      inp (afterPair k x N H v a r) TM.blankTape ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, hpi, ?_, hpo⟩
  funext j
  by_cases hj : j = y1Idx k
  · rw [hj, afterCopy, Function.update_self]
    refine Tape.ext ?_ ?_
    · rw [hpsrcHead]
    · rw [hpsrcCells, hsrc]
  · by_cases hj' : j = yIdx k
    · rw [hj', hpdst, afterCopy, Function.update_of_ne hne.symm, Function.update_self]
      rfl
    · rw [hpother j hj hj', afterCopy, Function.update_of_ne hj, Function.update_of_ne hj',
        afterPair, Function.update_of_ne hj]

/-- **The layout and the placement agree.** The tapes the copy stage leaves behind are exactly
the ones the placed matrix machine expects to be entered with: its own scratch blank, the pair on
the tape it reads, the verdict tape blank, and the enumerator's registers on either side. -/
theorem matrixEntry_afterCopy (M : TM k) (x : List Bool) (N H v a r : ℕ) (I : Tape) :
    matrixEntry M (afterCopy k x N H v a r) (pair x (dropTop (v + 1))) I
      = afterCopy k x N H v a r := by
  funext i
  rw [matrixEntry]
  by_cases hi : TM.placeWorkInMiddle 3 (k + 2) i
  · rw [dite_eq_left hi]
    set j := TM.placeWorkCoord 3 (k + 2) i hi with hjdef
    have hival : i.val = 3 + j.val := by
      rw [hjdef]
      show i.val = 3 + (i.val - 3)
      have := hi.1
      omega
    refine Fin.lastCases (motive := fun j' => ∀ (hj : j = j'),
      TM.applyPre M (pair x (dropTop (v + 1))) I j' = afterCopy k x N H v a r i) ?_ ?_ j rfl
    · intro hj
      have hi' : i = vIdx k := by
        apply Fin.ext
        rw [hival, hj]
        show 3 + (k + 1) = 3 + k + 1
        omega
      rw [TM.applyPre, Fin.snoc_last, hi', afterCopy,
        Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 1 ≠ 2; omega)),
        Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 1 ≠ 3 + k; omega)), enumBank_v]
      rfl
    · intro j' hj
      by_cases hjk : j'.val < k
      · have hi' : (2 : ℕ) ≤ i.val ∧ i.val < 3 + k + 2 := by
          rw [hival, hj]
          show 2 ≤ 3 + j'.val ∧ 3 + j'.val < 3 + k + 2
          omega
        rw [TM.applyPre, Fin.snoc_castSucc]
        show (if j'.val < k then (Tape.init ([] : List Γ)).move Dir3.right
          else (Tape.init ((pair x (dropTop (v + 1))).map Γ.ofBool)).move Dir3.right) = _
        rw [ite_eq_left hjk, afterCopy,
          Function.update_of_ne (Fin.ne_of_val_ne (by rw [hival, hj]; show 3 + j'.val ≠ 2; omega)),
          Function.update_of_ne
            (Fin.ne_of_val_ne (by rw [hival, hj]; show 3 + j'.val ≠ 3 + k; omega)),
          enumBank_blank_of_val k x N H v a r i hi'.1 hi'.2]
        rfl
      · have hjk' : j'.val = k := by
          have := j'.isLt
          omega
        have hi' : i = yIdx k := by
          apply Fin.ext
          rw [hival, hj]
          show 3 + j'.val = 3 + k
          omega
        rw [TM.applyPre, Fin.snoc_castSucc]
        show (if j'.val < k then (Tape.init ([] : List Γ)).move Dir3.right
          else (Tape.init ((pair x (dropTop (v + 1))).map Γ.ofBool)).move Dir3.right) = _
        rw [ite_eq_right hjk, hi', afterCopy,
          Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k ≠ 2; omega)),
          Function.update_self]
        rfl
  · rw [dite_eq_right hi]

theorem afterCopy_startInvariant (k : ℕ) (x : List Bool) (N H v a r : ℕ)
    (i : Fin (enumTapes k)) : Tape.StartInvariant (afterCopy k x N H v a r i) := by
  rw [afterCopy]
  by_cases h1 : i = y1Idx k
  · rw [h1, Function.update_self]
    exact ⟨(strTape_startInvariant (pair x (dropTop (v + 1)))).1,
      fun j hj => (strTape_startInvariant (pair x (dropTop (v + 1)))).2 j hj⟩
  · rw [Function.update_of_ne h1]
    by_cases h2 : i = yIdx k
    · rw [h2, Function.update_self]
      exact strTape_startInvariant _
    · rw [Function.update_of_ne h2]
      exact enumBank_startInvariant k x N H v a r i

theorem afterCopy_head_pos (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k)) :
    1 ≤ (afterCopy k x N H v a r i).head := by
  rw [afterCopy]
  by_cases h1 : i = y1Idx k
  · rw [h1, Function.update_self]
    show 1 ≤ (pair x (dropTop (v + 1))).length + 1
    omega
  · rw [Function.update_of_ne h1]
    by_cases h2 : i = yIdx k
    · rw [h2, Function.update_self]
      exact le_of_eq rfl
    · rw [Function.update_of_ne h2]
      exact (enumBank_parked k x N H v a r i).1

/-- **The evaluating stage's contract, in the enumerator's own terms.** -/
theorem matrix_hoareTime (M : TM k) {L : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTime L T)
    (hdecS : M.DecidesInSpace L S)
    (x : List Bool) (N H v a r : ℕ) (I : Tape) (hI : TM.Parked I) (hISI : Tape.StartInvariant I)
    (Hb : ℕ) (hHS : (pair x (dropTop (v + 1))).length +
      S (pair x (dropTop (v + 1))).length + 2 ≤ Hb) :
    (matrixTM M).HoareTime
      (fun inp work out => inp = I ∧ work = afterCopy k x N H v a r ∧ out = TM.blankTape)
      (fun inp work out => inp = I ∧ out = TM.blankTape ∧
        (pair x (dropTop (v + 1)) ∈ L → (work (vIdx k)).cells 1 = Γ.one) ∧
        (pair x (dropTop (v + 1)) ∉ L → (work (vIdx k)).cells 1 = Γ.zero) ∧
        (∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → work i = afterCopy k x N H v a r i) ∧
        (∀ i, TM.placeWorkInMiddle 3 (k + 2) i →
          Tape.StartInvariant (work i) ∧ (work i).head ≤ Hb ∧
            ∀ j, Hb < j → (work i).cells j = Γ.blank))
      (T (pair x (dropTop (v + 1))).length) := by
  have h := matrixTM_hoareTime M hdec hdecS (pair x (dropTop (v + 1))) I hI hISI
    (afterCopy k x N H v a r)
    (fun i _ => afterCopy_startInvariant k x N H v a r i)
    (fun i _ => afterCopy_head_pos k x N H v a r i) Hb hHS
  rw [matrixEntry_afterCopy] at h
  exact h

/-- What the matrix machine leaves behind: its verdict on the verdict tape, the enumerator's own
tapes untouched, and its block dirty but bounded. -/
def midMatrix (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  inp = I ∧ out = TM.blankTape ∧
  ((work (vIdx k)).cells 1 = Γ.one ↔ b = true) ∧
  (∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → work i = afterCopy k x N H v a r i) ∧
  (∀ i, TM.placeWorkInMiddle 3 (k + 2) i →
    Tape.StartInvariant (work i) ∧ (work i).head ≤ Hb ∧
      ∀ j, Hb < j → (work i).cells j = Γ.blank)

/-- The evaluating stage, with its verdict read as a Boolean. -/
theorem matrix_hoareTime_bool (M : TM k) {L : Language} {T S : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (hdecS : M.DecidesInSpace L S)
    (x : List Bool) (N H v a r : ℕ) (I : Tape) (hI : TM.Parked I) (hISI : Tape.StartInvariant I)
    (Hb : ℕ) (hHS : (pair x (dropTop (v + 1))).length +
      S (pair x (dropTop (v + 1))).length + 2 ≤ Hb) (b : Bool)
    (hb : b = true ↔ pair x (dropTop (v + 1)) ∈ L) :
    (matrixTM M).HoareTime
      (fun inp work out => inp = I ∧ work = afterCopy k x N H v a r ∧ out = TM.blankTape)
      (midMatrix k x N H v a r I Hb b)
      (T (pair x (dropTop (v + 1))).length) := by
  refine (matrix_hoareTime M hdec hdecS x N H v a r I hI hISI Hb hHS).strengthen_post ?_
  rintro inp work out ⟨hi, ho, hone, hzero, hframe, hblock⟩
  refine ⟨hi, ho, ?_, hframe, hblock⟩
  by_cases hmem : pair x (dropTop (v + 1)) ∈ L
  · rw [hone hmem]
    simp [hb.mpr hmem]
  · rw [hzero hmem]
    constructor
    · intro hcon
      exact absurd hcon (by decide)
    · intro hcon
      exact absurd (hb.mp hcon) hmem

/-- The verdict tape rewound: the pass can read the bit it published. -/
def midParked (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  inp = I ∧ out = TM.blankTape ∧
  ((work (vIdx k)).read = Γ.one ↔ b = true) ∧
  (∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → work i = afterCopy k x N H v a r i) ∧
  (∀ i, TM.Parked (work i)) ∧
  (∀ i, TM.placeWorkInMiddle 3 (k + 2) i →
    Tape.StartInvariant (work i) ∧ (work i).head ≤ Hb + 1 ∧
      ∀ j, Hb < j → (work i).cells j = Γ.blank)

/-- **Rewinding the verdict tape.** The matrix machine halts wherever it likes; the bit it wrote
is at cell one, so the head has to go back there before the pass can publish it. -/
theorem parkVerdict_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hISI : Tape.StartInvariant I) (hIhead : I.head = 1) (Hb : ℕ) (hHb : 1 ≤ Hb) (b : Bool) :
    (TM.parkRewindTM [vIdx k]).HoareTime
      (midMatrix k x N H v a r I Hb b)
      (midParked k x N H v a r I Hb b)
      (1 + 1 + (2 * (max (Hb + 2) (1 * (Hb + 3) + 1) + 1) + 1)) := by
  rintro inp work out ⟨hi, ho, hverdict, hframe, hblock⟩
  have hSI : ∀ i, Tape.StartInvariant (work i) := by
    intro i
    by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
    · exact (hblock i hm).1
    · rw [hframe i hm]
      exact afterCopy_startInvariant k x N H v a r i
  have hmid : TM.placeWorkInMiddle 3 (k + 2) (vIdx k) := vIdx_inMiddle k
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpw, hpo⟩ :=
    TM.parkRewindTM_hoareTime [vIdx k] (List.nodup_singleton _) Hb hHb inp work out
      (by rw [hi]; exact hISI) hSI (by rw [ho]; exact TM.blankTape_startInvariant)
      (by rw [hi, hIhead]; exact hHb)
      (fun j hj => by
        rw [List.mem_singleton.mp hj]
        exact (hblock (vIdx k) hmid).2.1)
      inp work out ⟨rfl, rfl, rfl⟩
  have hvw : c'.work (vIdx k) = (⟨1, (work (vIdx k)).cells⟩ : Tape) := by
    rw [hpw]
    show (if vIdx k ∈ [vIdx k] then (⟨1, (work (vIdx k)).cells⟩ : Tape) else _) = _
    rw [ite_eq_left (List.mem_singleton.mpr rfl)]
  have hother : ∀ j, j ≠ vIdx k → c'.work j = TM.parkTape (work j) := by
    intro j hj
    rw [hpw]
    show (if j ∈ [vIdx k] then _ else TM.parkTape (work j)) = _
    rw [ite_eq_right (fun hmem => hj (List.mem_singleton.mp hmem))]
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpi, hi]
    exact Tape.ext hIhead.symm rfl
  · rw [hpo, ho, TM.parkTape]
    exact Tape.ext rfl rfl
  · rw [hvw]
    show (work (vIdx k)).cells 1 = Γ.one ↔ b = true
    exact hverdict
  · intro i hm
    have hne : i ≠ vIdx k := fun h => hm (h ▸ hmid)
    rw [hother i hne, hframe i hm, TM.parkTape]
    refine Tape.ext ?_ rfl
    show max (afterCopy k x N H v a r i).head 1 = (afterCopy k x N H v a r i).head
    have := afterCopy_head_pos k x N H v a r i
    omega
  · intro i
    by_cases hi' : i = vIdx k
    · rw [hi', hvw]
      exact ⟨le_of_eq rfl, fun j hj => (hSI (vIdx k)).2 j hj⟩
    · rw [hother i hi']
      exact TM.parkTape_parked (hSI i)
  · intro i hm
    by_cases hi' : i = vIdx k
    · rw [hi', hvw]
      refine ⟨⟨(hSI (vIdx k)).1, fun j hj => (hSI (vIdx k)).2 j hj⟩, ?_, ?_⟩
      · show (1 : ℕ) ≤ Hb + 1
        omega
      · rw [hi'] at hm
        exact (hblock (vIdx k) hm).2.2
    · rw [hother i hi', TM.parkTape]
      refine ⟨⟨(hSI i).1, fun j hj => (hSI i).2 j hj⟩, ?_, (hblock i hm).2.2⟩
      show max (work i).head 1 ≤ Hb + 1
      have := (hblock i hm).2.1
      omega

/-- Reading a cell back as a writable symbol turns it into `1` exactly when it was `1`. -/
theorem readBackWrite_one_iff (s : Γ) : TM.readBackWrite s = Γw.one ↔ s = Γ.one := by
  cases s <;> simp [TM.readBackWrite]

/-- The verdict published into the slot, where the tally bump can branch on it. -/
def midPublish (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  inp = I ∧ (∃ s : Γw, (s = Γw.one ↔ b = true) ∧ out = NTM.outSlot s) ∧
  (∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → work i = afterCopy k x N H v a r i) ∧
  (∀ i, TM.Parked (work i)) ∧
  (∀ i, TM.placeWorkInMiddle 3 (k + 2) i →
    Tape.StartInvariant (work i) ∧ (work i).head ≤ Hb + 1 ∧
      ∀ j, Hb < j → (work i).cells j = Γ.blank)

/-- **Publishing the verdict.** The bit under the verdict tape's head is copied into the output
slot, which is the only channel between a work tape and the real output. -/
theorem publishVerdict_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (Hb : ℕ) (b : Bool) :
    (TM.writeOutputBitTM (vIdx k)).HoareTime
      (midParked k x N H v a r I Hb b)
      (midPublish k x N H v a r I Hb b)
      1 := by
  rintro inp work out ⟨hi, ho, hverdict, hframe, hpark, hblock⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpw, hpo⟩ :=
    TM.writeOutputBitTM_hoareTime_frame (vIdx k) inp work out (by rw [hi]; exact hI) hpark
      (by rw [ho]; exact TM.blankTape_parked) inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, by rw [hpi, hi], ?_, ?_, ?_, ?_⟩
  · refine ⟨TM.readBackWrite ((work (vIdx k)).read), ?_, ?_⟩
    · rw [readBackWrite_one_iff]
      exact hverdict
    · rw [hpo, ho, ← NTM.outSlot_blank_eq_blankTape]
      exact NTM.outSlot_write Γw.blank _
  · intro i hm
    rw [hpw]
    exact hframe i hm
  · intro i
    rw [hpw]
    exact hpark i
  · intro i hm
    rw [hpw]
    exact hblock i hm

@[simp] theorem enumBank_c (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (cIdx k) = natTape v := by
  rw [enumBank, tallyWork]
  dsimp only
  rw [ite_eq_left rfl]

@[simp] theorem enumBank_a (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (aIdx k) = natTape a := by
  rw [enumBank, tallyWork]
  dsimp only
  rw [ite_eq_right (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 2; omega)), ite_eq_left rfl]

@[simp] theorem enumBank_r (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (rIdx k) = natTape r := by
  rw [enumBank, tallyWork]
  dsimp only
  rw [ite_eq_right (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 2; omega)),
    ite_eq_right (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 5; omega)), ite_eq_left rfl]

theorem afterCopy_of_ne (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k))
    (h1 : i ≠ y1Idx k) (h2 : i ≠ yIdx k) :
    afterCopy k x N H v a r i = enumBank k x N H v a r i := by
  rw [afterCopy, Function.update_of_ne h1, Function.update_of_ne h2]

/-- A tape outside the matrix machine's block is neither of the two the copy stage disturbed. -/
theorem afterCopy_outside (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k))
    (hm : ¬ TM.placeWorkInMiddle 3 (k + 2) i) (h1 : i ≠ y1Idx k) :
    afterCopy k x N H v a r i = enumBank k x N H v a r i :=
  afterCopy_of_ne k x N H v a r i h1 (fun h => hm (h ▸ yIdx_inMiddle k))

/-- What the tally bump leaves: the counter advanced, one tally bumped, and the slot blank
again. -/
def midBump (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  inp = I ∧ out = TM.blankTape ∧
  work (cIdx k) = natTape (v + 1) ∧
  work (aIdx k) = natTape (a + if b then 1 else 0) ∧
  work (rIdx k) = natTape (r + if b then 0 else 1) ∧
  (∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → i ≠ cIdx k → i ≠ aIdx k → i ≠ rIdx k →
    work i = afterCopy k x N H v a r i) ∧
  (∀ i, TM.Parked (work i)) ∧ (∀ i, (work i).cells 0 = Γ.start) ∧
  (∀ i, TM.placeWorkInMiddle 3 (k + 2) i →
    (work i).head ≤ Hb + 1 ∧ ∀ j, Hb < j → (work i).cells j = Γ.blank)

/-- **The tally bump.** The slot the previous stage published names which tally to advance; the
counter advances with it, and the slot is blanked so that the wipe can run. -/
theorem tallyBump_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIz : I.cells 0 = Γ.start) (Hb : ℕ) (b : Bool) :
    (TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k)).HoareTime
      (midPublish k x N H v a r I Hb b)
      (midBump k x N H v a r I Hb b)
      (3 * (max (1 + 1 + max (TM.binarySuccTime a) (TM.binarySuccTime r) + 5)
        (TM.binarySuccTime v) + 1) + 1) := by
  rintro inp work out ⟨hi, ⟨s, hs, ho⟩, hframe, hpark, hblock⟩
  have hzero : ∀ i, (work i).cells 0 = Γ.start := by
    intro i
    by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
    · exact (hblock i hm).1.1
    · rw [hframe i hm]
      exact (afterCopy_startInvariant k x N H v a r i).1
  have hy1 : y1Idx k ≠ cIdx k ∧ y1Idx k ≠ aIdx k ∧ y1Idx k ≠ rIdx k := y1_ne_regs k
  have hcout : ¬ TM.placeWorkInMiddle 3 (k + 2) (cIdx k) :=
    fun hm => absurd (show (3 + k + 2 : ℕ) < 3 + (k + 2) from hm.2) (by omega)
  have haout : ¬ TM.placeWorkInMiddle 3 (k + 2) (aIdx k) :=
    fun hm => absurd (show (3 + k + 5 : ℕ) < 3 + (k + 2) from hm.2) (by omega)
  have hrout : ¬ TM.placeWorkInMiddle 3 (k + 2) (rIdx k) :=
    fun hm => absurd (show (3 + k + 8 : ℕ) < 3 + (k + 2) from hm.2) (by omega)
  have hc : work (cIdx k) = natTape v := by
    rw [hframe (cIdx k) hcout,
      afterCopy_outside k x N H v a r _ hcout (fun h => hy1.1 h.symm), enumBank_c]
  have ha : work (aIdx k) = natTape a := by
    rw [hframe (aIdx k) haout,
      afterCopy_outside k x N H v a r _ haout (fun h => hy1.2.1 h.symm), enumBank_a]
  have hr : work (rIdx k) = natTape r := by
    rw [hframe (rIdx k) hrout,
      afterCopy_outside k x N H v a r _ hrout (fun h => hy1.2.2 h.symm), enumBank_r]
  have hzblank : (work (zIdx k)).read = Γ.blank := by
    have hzout : ¬ TM.placeWorkInMiddle 3 (k + 2) (zIdx k) :=
      fun hm => absurd (show (3 + k + 6 : ℕ) < 3 + (k + 2) from hm.2) (by omega)
    rw [hframe (zIdx k) hzout,
      afterCopy_outside k x N H v a r _ hzout
        (fun h => absurd (show (3 + k + 6 : ℕ) = 2 from congrArg Fin.val h) (by omega)),
      enumBank_blank k x N H v a r _ (z_ne_regs k).1 (z_ne_regs k).2.1 (z_ne_regs k).2.2
        (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 0; omega))
        (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 1; omega))
        (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 3; omega))
        (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 7; omega))]
    exact Tape.init_nil_move_right_read
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpw, hpo⟩ :=
    TM.tallyBumpTM_hoareTime (cIdx k) (aIdx k) (rIdx k) (zIdx k)
      (Fin.ne_of_val_ne (by show 3 + k + 2 ≠ 3 + k + 5; omega))
      (Fin.ne_of_val_ne (by show 3 + k + 2 ≠ 3 + k + 8; omega))
      (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 2; omega))
      (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 5; omega))
      (Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 8; omega))
      v a r b s hs inp work (by rw [hi]; exact hI) (by rw [hi]; exact hIz) hpark hzero
      hc ha hr hzblank inp work out ⟨rfl, rfl, ho⟩
  have hupd : ∀ i, i ≠ cIdx k → i ≠ aIdx k → i ≠ rIdx k → c'.work i = work i := by
    intro i h1 h2 h3
    rw [hpw, Function.update_of_ne h1]
    split
    · rw [Function.update_of_ne h2]
    · rw [Function.update_of_ne h3]
  refine ⟨c', t, ht, hreach, hhalt, by rw [hpi, hi], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpo, ← NTM.outSlot_blank_eq_blankTape]
  · rw [hpw, Function.update_self]
  · rw [hpw, Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 2; omega))]
    by_cases hb : b
    · rw [ite_eq_left hb, Function.update_self, ite_eq_left hb]
    · rw [ite_eq_right hb, Function.update_of_ne
        (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 8; omega)), ha, ite_eq_right hb]
      rfl
  · rw [hpw, Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 2; omega))]
    by_cases hb : b
    · rw [ite_eq_left hb, Function.update_of_ne
        (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 5; omega)), hr, ite_eq_left hb]
      rfl
    · rw [ite_eq_right hb, Function.update_self, ite_eq_right hb]
  · intro i hm h1 h2 h3
    rw [hupd i h1 h2 h3]
    exact hframe i hm
  · intro i
    by_cases h1 : i = cIdx k
    · rw [h1, hpw, Function.update_self]
      exact natTape_parked _
    · by_cases h2 : i = aIdx k
      · rw [h2, hpw, Function.update_of_ne
          (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 2; omega))]
        split
        · rw [Function.update_self]
          exact natTape_parked _
        · rw [Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 8; omega))]
          exact hpark _
      · by_cases h3 : i = rIdx k
        · rw [h3, hpw, Function.update_of_ne
            (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 2; omega))]
          split
          · rw [Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 5; omega))]
            exact hpark _
          · rw [Function.update_self]
            exact natTape_parked _
        · rw [hupd i h1 h2 h3]
          exact hpark i
  · intro i
    by_cases h1 : i = cIdx k
    · rw [h1, hpw, Function.update_self]
      exact NTM.natTape_cells_zero _
    · by_cases h2 : i = aIdx k
      · rw [h2, hpw, Function.update_of_ne
          (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 2; omega))]
        split
        · rw [Function.update_self]
          exact NTM.natTape_cells_zero _
        · rw [Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 8; omega))]
          exact hzero _
      · by_cases h3 : i = rIdx k
        · rw [h3, hpw, Function.update_of_ne
            (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 2; omega))]
          split
          · rw [Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 3 + k + 5; omega))]
            exact hzero _
          · rw [Function.update_self]
            exact NTM.natTape_cells_zero _
        · rw [hupd i h1 h2 h3]
          exact hzero i
  · intro i hm
    have h1 : i ≠ cIdx k := fun h => hcout (h ▸ hm)
    have h2 : i ≠ aIdx k := fun h => haout (h ▸ hm)
    have h3 : i ≠ rIdx k := fun h => hrout (h ▸ hm)
    rw [hupd i h1 h2 h3]
    exact ⟨(hblock i hm).2.1, (hblock i hm).2.2⟩

/-- The witness advanced in step with the counter. -/
def midBumped (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool) :
    TM.TapePred (enumTapes k) := fun inp work out =>
  inp = I ∧ out = TM.blankTape ∧
  work (cIdx k) = natTape (v + 1) ∧
  work (aIdx k) = natTape (a + if b then 1 else 0) ∧
  work (rIdx k) = natTape (r + if b then 0 else 1) ∧
  work (wIdx k) = strTape (dropTop (v + 1 + 1)) ∧
  (∀ i, ¬ TM.placeWorkInMiddle 3 (k + 2) i → i ≠ cIdx k → i ≠ aIdx k → i ≠ rIdx k →
    i ≠ wIdx k → work i = afterCopy k x N H v a r i) ∧
  (∀ i, TM.Parked (work i)) ∧ (∀ i, (work i).cells 0 = Γ.start) ∧
  (∀ i, TM.placeWorkInMiddle 3 (k + 2) i →
    (work i).head ≤ Hb + 1 ∧ ∀ j, Hb < j → (work i).cells j = Γ.blank)

/-- **Advancing the witness.** The counter has just moved on, and `TM.binaryBumpTM` moves the
witness with it: `PolyExists.dropTop_succ` says the string the next count denotes is exactly the
zero-extending increment of this one. -/
theorem witnessBump_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (Hb : ℕ) (b : Bool) :
    (TM.binaryBumpTM (wIdx k)).HoareTime
      (midBump k x N H v a r I Hb b)
      (midBumped k x N H v a r I Hb b)
      (TM.binaryBumpTime (dropTop (v + 1))) := by
  rintro inp work out ⟨hi, ho, hc, ha, hr, hframe, hpark, hzero, hblock⟩
  have hwout : ¬ TM.placeWorkInMiddle 3 (k + 2) (wIdx k) :=
    fun hm => absurd (show (3 : ℕ) ≤ 1 from hm.1) (by omega)
  have hw : work (wIdx k) = strTape (dropTop (v + 1)) := by
    rw [hframe (wIdx k) hwout
      (Fin.ne_of_val_ne (by show (1 : ℕ) ≠ 3 + k + 2; omega))
      (Fin.ne_of_val_ne (by show (1 : ℕ) ≠ 3 + k + 5; omega))
      (Fin.ne_of_val_ne (by show (1 : ℕ) ≠ 3 + k + 8; omega)),
      afterCopy_outside k x N H v a r _ hwout
        (Fin.ne_of_val_ne (by show (1 : ℕ) ≠ 2; omega)), enumBank_w]
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpother, hpbits, hpcell0, hpo⟩ :=
    TM.binaryBumpTM_hoareTime_frame (wIdx k) (dropTop (v + 1)) inp work out
      (by rw [hw]; exact strTape_hasBinaryString _)
      (by rw [hw]; exact strTape_cells_zero _)
      (by rw [hi]; exact hI.2 _ hI.1)
      (fun i _ => (hpark i).2 _ (hpark i).1)
      (by rw [ho]; exact TM.blankTape_parked.2 _ TM.blankTape_parked.1)
      inp work out ⟨rfl, rfl, rfl⟩
  have hwnew : c'.work (wIdx k) = strTape (dropTop (v + 1 + 1)) := by
    have hbits : (c'.work (wIdx k)).HasBinaryString (dropTop (v + 1 + 1)) := by
      have heq : BinaryBump.bump (dropTop (v + 1)) = dropTop (v + 1 + 1) := by
        rw [bump_eq_bumpLE, ← dropTop_succ (by omega)]
      rw [← heq]
      exact hpbits
    exact Tape.eq_init_move_right_of_hasBinaryString hbits hpcell0
  refine ⟨c', t, ht, hreach, hhalt, by rw [hpi, hi], by rw [hpo, ho], ?_, ?_, ?_, hwnew, ?_, ?_,
    ?_, ?_⟩
  · rw [hpother (cIdx k) (Fin.ne_of_val_ne (by show 3 + k + 2 ≠ 1; omega))]
    exact hc
  · rw [hpother (aIdx k) (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 1; omega))]
    exact ha
  · rw [hpother (rIdx k) (Fin.ne_of_val_ne (by show 3 + k + 8 ≠ 1; omega))]
    exact hr
  · intro i hm h1 h2 h3 h4
    rw [hpother i h4]
    exact hframe i hm h1 h2 h3
  · intro i
    by_cases hiw : i = wIdx k
    · rw [hiw, hwnew]
      exact strTape_parked _
    · rw [hpother i hiw]
      exact hpark i
  · intro i
    by_cases hiw : i = wIdx k
    · rw [hiw, hwnew]
      exact strTape_cells_zero _
    · rw [hpother i hiw]
      exact hzero i
  · intro i hm
    have hiw : i ≠ wIdx k := fun h => hwout (h ▸ hm)
    rw [hpother i hiw]
    exact hblock i hm

/-- The resting bank depends on the count only through the witness. -/
theorem enumRest_eq_of_ne_w (k : ℕ) (x : List Bool) (N H v v' : ℕ) (i : Fin (enumTapes k))
    (hw : i ≠ wIdx k) : enumRest k x N H v i = enumRest k x N H v' i := by
  rw [enumRest, enumRest]
  by_cases hx : i = xIdx k
  · rw [ite_eq_left hx, ite_eq_left hx]
  · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hw, ite_eq_right hw]

/-- **The wipe, and the bridge back to the loop invariant.** Blanking everything the pass dirtied
turns the bank into the one the loop's state names at the next count. -/
theorem wipe_hoareTime (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hISI : Tape.StartInvariant I) (Hb : ℕ) (b : Bool)
    (hHb : Hb + 1 ≤ H) (hpairH : (pair x (dropTop (v + 1))).length + 1 ≤ H) :
    (TM.wipeRewindTM (scratchTargets k) (regIdx k)).HoareTime
      (midBumped k x N H v a r I Hb b)
      (fun inp work out => inp = I ∧
        work = enumBank k x N H (v + 1) (a + if b then 1 else 0) (r + if b then 0 else 1) ∧
        out = TM.blankTape)
      ((scratchTargets k).length * (H + 4) + H * 4 + 8 + 1 +
        ((scratchTargets k).length * (H + 4) + 1)) := by
  rintro inp work out ⟨hi, ho, hc, ha, hr, hw, hframe, hpark, hzero, hblock⟩
  have hregout : ¬ TM.placeWorkInMiddle 3 (k + 2) (regIdx k) :=
    fun hm => absurd (show (3 + k + 7 : ℕ) < 3 + (k + 2) from hm.2) (by omega)
  have hregmem : regIdx k ∉ scratchTargets k := (not_mem_scratchTargets k).2.2.2.2.2.2.2.1
  have hreg : work (regIdx k) = TM.regTape H := by
    rw [hframe (regIdx k) hregout
      (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 3 + k + 2; omega))
      (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 3 + k + 5; omega))
      (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 3 + k + 8; omega))
      (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 1; omega)),
      afterCopy_outside k x N H v a r _ hregout
        (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 2; omega)),
      enumBank_of_ne k x N H v a r _
        (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 3 + k + 2; omega))
        (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 3 + k + 5; omega))
        (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 3 + k + 8; omega)), enumRest, ite_eq_right
        (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 0; omega)), ite_eq_right
        (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 1; omega)), ite_eq_right
        (Fin.ne_of_val_ne (by show 3 + k + 7 ≠ 3 + k + 3; omega)), ite_eq_left rfl]
  have hy1 : work (y1Idx k) =
      (⟨(pair x (dropTop (v + 1))).length + 1, (strTape (pair x (dropTop (v + 1)))).cells⟩ :
        Tape) := by
    have hy1out : ¬ TM.placeWorkInMiddle 3 (k + 2) (y1Idx k) :=
      fun hm => absurd (show (3 : ℕ) ≤ 2 from hm.1) (by omega)
    rw [hframe (y1Idx k) hy1out (y1_ne_regs k).1 (y1_ne_regs k).2.1 (y1_ne_regs k).2.2
      (Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 1; omega)), afterCopy, Function.update_self]
  obtain ⟨c', t, ht, hreach, hhalt, hpi, hpw, hpo⟩ :=
    TM.wipeRewindTM_hoareTime (scratchTargets k) (scratchTargets_nodup k) (regIdx k) hregmem H
      inp work out (by rw [hi]; exact hISI) (by rw [hi]; exact hI) ho
      (fun j _ => ⟨hzero j, fun i hi' => (hpark j).2 i hi'⟩)
      (fun j hj => by
        by_cases hjy : j = y1Idx k
        · rw [hjy, hy1]
          show (pair x (dropTop (v + 1))).length + 1 ≤ H
          omega
        · have hjm : TM.placeWorkInMiddle 3 (k + 2) j := by
            have hv := scratchTargets_val k j hj
            refine ⟨?_, by omega⟩
            rcases Nat.lt_or_ge j.val 3 with h | h
            · exact absurd (Fin.ext (show j.val = 2 by omega)) hjy
            · exact h
          have := (hblock j hjm).1
          omega)
      (fun j hj i hi' => by
        by_cases hjy : j = y1Idx k
        · rw [hjy, hy1]
          show (strTape (pair x (dropTop (v + 1)))).cells i = Γ.blank
          obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
          exact (strTape_hasBinaryString (pair x (dropTop (v + 1)))).2.2 m (by omega)
        · have hjm : TM.placeWorkInMiddle 3 (k + 2) j := by
            have hv := scratchTargets_val k j hj
            refine ⟨?_, by omega⟩
            rcases Nat.lt_or_ge j.val 3 with h | h
            · exact absurd (Fin.ext (show j.val = 2 by omega)) hjy
            · exact h
          exact (hblock j hjm).2 i (by omega))
      hreg (fun j _ hj => hpark j)
      inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, by rw [hpi, hi], ?_, by rw [hpo, ho]⟩
  rw [hpw]
  funext j
  by_cases hj : j ∈ scratchTargets k
  · rw [ite_eq_left hj]
    have hv := scratchTargets_val k j hj
    exact (enumBank_blank_of_val k x N H (v + 1) (a + if b then 1 else 0)
      (r + if b then 0 else 1) j hv.1 hv.2).symm
  · rw [ite_eq_right hj]
    by_cases h1 : j = cIdx k
    · rw [h1, hc, enumBank_c]
    · by_cases h2 : j = aIdx k
      · rw [h2, ha, enumBank_a]
      · by_cases h3 : j = rIdx k
        · rw [h3, hr, enumBank_r]
        · by_cases h4 : j = wIdx k
          · rw [h4, hw, enumBank_w]
          · have hjm : ¬ TM.placeWorkInMiddle 3 (k + 2) j := by
              intro hm
              refine hj ?_
              rw [scratchTargets]
              refine List.mem_cons.mpr (Or.inr (List.mem_append.mpr ?_))
              rcases Nat.lt_or_ge j.val (3 + k) with h | h
              · exact Or.inl ((mem_matrixTapes_iff k j).mpr ⟨hm.1, h⟩)
              · rcases Nat.lt_or_ge j.val (3 + k + 1) with h' | h'
                · exact Or.inr (List.mem_cons.mpr (Or.inl (Fin.ext
                    (show j.val = 3 + k by omega))))
                · exact Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                    (Or.inl (Fin.ext (show j.val = 3 + k + 1 by
                      have := show j.val < 3 + (k + 2) from hm.2
                      omega))))))
            rw [hframe j hjm h1 h2 h3 h4, afterCopy_outside k x N H v a r j hjm
              (fun h => hj (by rw [h, scratchTargets]; exact List.mem_cons_self ..)),
              enumBank_of_ne k x N H v a r j h1 h2 h3,
              enumBank_of_ne k x N H (v + 1) _ _ j h1 h2 h3]
            exact enumRest_eq_of_ne_w k x N H (v + 1) (v + 1 + 1) j h4

/-! ## Chaining the pass -/

/-- A phase boundary parks every tape it crosses. -/
theorem transitionTape_park {t : Tape} (h : Tape.StartInvariant t) :
    TM.transitionTape t = (⟨max t.head 1, t.cells⟩ : Tape) := by
  rw [TM.transitionTape, TM.writeAndMove_readBack_of_startInvariant t h,
    TM.move_idleDir_eq_of_startInvariant h]

/-- A phase boundary is the identity on parked tapes. -/
theorem trans_id_of_parked {inp : Tape} {work : Fin (enumTapes k) → Tape} {out : Tape}
    (hi : TM.Parked inp) (hw : ∀ i, TM.Parked (work i)) (ho : TM.Parked out) :
    TM.transitionInput inp = inp ∧ (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  ⟨TM.transitionInput_eq_self hi.read_ne_start,
    funext fun i => TM.transitionTape_eq_self (hw i).read_ne_start,
    TM.transitionTape_eq_self ho.read_ne_start⟩

theorem afterPair_parked (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k)) :
    TM.Parked (afterPair k x N H v a r i) := by
  rw [afterPair]
  by_cases h : i = y1Idx k
  · rw [h, Function.update_self]
    exact strTape_parked _
  · rw [Function.update_of_ne h]
    exact enumBank_parked k x N H v a r i

theorem afterCopy_parked (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k)) :
    TM.Parked (afterCopy k x N H v a r i) :=
  ⟨afterCopy_head_pos k x N H v a r i,
    fun j hj => (afterCopy_startInvariant k x N H v a r i).2 j hj⟩

/-- **The seam after the emitter.** The emitter can leave a head on the marker; the boundary step
moves it off, and everything the next stage needs survives. -/
theorem midEmit_trans (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (hI : TM.Parked I)
    (B : ℕ) (hB : 1 ≤ B) (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midEmit k x N H v a r I B inp work out) :
    midEmit k x N H v a r I B (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨hi, ho, hframe, hxc, hwc, hy1, hSI, hhead⟩ := h
  have hpark : ∀ i, TM.transitionTape (work i) = (⟨max (work i).head 1, (work i).cells⟩ : Tape) :=
    fun i => transitionTape_park (hSI i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi, TM.transitionInput_eq_self hI.read_ne_start]
  · rw [ho, TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start]
  · intro i hm
    show TM.transitionTape (work i) = enumBank k x N H v a r i
    rw [hpark i, hframe i hm]
    refine Tape.ext ?_ rfl
    show max (enumBank k x N H v a r i).head 1 = (enumBank k x N H v a r i).head
    rw [enumBank_head]
    omega
  · show (TM.transitionTape (work (xIdx k))).cells = (strTape x).cells
    rw [hpark (xIdx k)]
    exact hxc
  · show (TM.transitionTape (work (wIdx k))).cells = (strTape (dropTop (v + 1))).cells
    rw [hpark (wIdx k)]
    exact hwc
  · show (TM.transitionTape (work (y1Idx k))).HasBinaryPrefix (pair x (dropTop (v + 1)))
    rw [hpark (y1Idx k)]
    refine ⟨?_, hy1.2.1, hy1.2.2⟩
    show max (work (y1Idx k)).head 1 = (pair x (dropTop (v + 1))).length + 1
    rw [hy1.1]
    omega
  · intro i
    show Tape.StartInvariant (TM.transitionTape (work i))
    rw [hpark i]
    exact ⟨(hSI i).1, fun j hj => (hSI i).2 j hj⟩
  · intro i
    show (TM.transitionTape (work i)).head ≤ B
    rw [hpark i]
    show max (work i).head 1 ≤ B
    have := hhead i
    omega

/-- **The seam after the matrix machine.** Same story: the machine may halt with a head on the
marker, and the boundary moves it off. -/
theorem midMatrix_trans (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (hI : TM.Parked I)
    (Hb : ℕ) (hHb : 1 ≤ Hb) (b : Bool) (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midMatrix k x N H v a r I Hb b inp work out) :
    midMatrix k x N H v a r I Hb b (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨hi, ho, hverdict, hframe, hblock⟩ := h
  have hSI : ∀ i, Tape.StartInvariant (work i) := by
    intro i
    by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
    · exact (hblock i hm).1
    · rw [hframe i hm]
      exact afterCopy_startInvariant k x N H v a r i
  have hpark : ∀ i, TM.transitionTape (work i) = (⟨max (work i).head 1, (work i).cells⟩ : Tape) :=
    fun i => transitionTape_park (hSI i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hi, TM.transitionInput_eq_self hI.read_ne_start]
  · rw [ho, TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start]
  · show (TM.transitionTape (work (vIdx k))).cells 1 = Γ.one ↔ b = true
    rw [hpark (vIdx k)]
    exact hverdict
  · intro i hm
    show TM.transitionTape (work i) = afterCopy k x N H v a r i
    rw [hpark i, hframe i hm]
    refine Tape.ext ?_ rfl
    show max (afterCopy k x N H v a r i).head 1 = (afterCopy k x N H v a r i).head
    have := afterCopy_head_pos k x N H v a r i
    omega
  · intro i hm
    show Tape.StartInvariant (TM.transitionTape (work i)) ∧
      (TM.transitionTape (work i)).head ≤ Hb ∧
      ∀ j, Hb < j → (TM.transitionTape (work i)).cells j = Γ.blank
    rw [hpark i]
    refine ⟨⟨(hSI i).1, fun j hj => (hSI i).2 j hj⟩, ?_, (hblock i hm).2.2⟩
    show max (work i).head 1 ≤ Hb
    have := (hblock i hm).2.1
    omega

/-- A predicate about parked tapes survives a phase boundary, since the boundary does not move
them. -/
theorem trans_of_parked_pred {P : TM.TapePred (enumTapes k)}
    {inp : Tape} {work : Fin (enumTapes k) → Tape} {out : Tape}
    (hi : TM.Parked inp) (hw : ∀ i, TM.Parked (work i)) (ho : TM.Parked out)
    (h : P inp work out) :
    P (TM.transitionInput inp) (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨h1, h2, h3⟩ := trans_id_of_parked hi hw ho
  rw [h1, h2, h3]
  exact h

/-- The pass's running time: its ten stages and the nine boundaries between them. -/
def bodyTime (k : ℕ) (x : List Bool) (T : ℕ → ℕ) (H Hb B v a r : ℕ) : ℕ :=
  1 + 1 + (TM.pairInputWorkTime x (dropTop (v + 1)) + 1 +
   ((1 + 1 + (2 * (max (B + 2) (3 * (B + 3) + 1) + 1) + 1)) + 1 +
    ((2 * (pair x (dropTop (v + 1))).length + 5) + 1 +
     (T (pair x (dropTop (v + 1))).length + 1 +
      ((1 + 1 + (2 * (max (Hb + 2) (1 * (Hb + 3) + 1) + 1) + 1)) + 1 +
       (1 + 1 +
        ((3 * (max (1 + 1 + max (TM.binarySuccTime a) (TM.binarySuccTime r) + 5)
            (TM.binarySuccTime v) + 1) + 1) + 1 +
         (TM.binaryBumpTime (dropTop (v + 1)) + 1 +
          ((scratchTargets k).length * (H + 4) + H * 4 + 8 + 1 +
            ((scratchTargets k).length * (H + 4) + 1))))))))))

/-- **One pass of the enumerator, contracted.** From the loop's state at count `v` the pass tests
the witness that count denotes, advances the counter and the witness, bumps the tally the verdict
names, and leaves the loop's state at count `v + 1`. -/
theorem bodyTM_hoareTime (M : TM k) {L : Language} {T S : ℕ → ℕ} (hdec : M.DecidesInTime L T)
    (hdecS : M.DecidesInSpace L S)
    (x : List Bool) (N H v a r : ℕ) (I : Tape) (hI : TM.Parked I) (hISI : Tape.StartInvariant I)
    (hIhead : I.head = 1) (hIz : I.cells 0 = Γ.start)
    (B Hb : ℕ) (hB : 1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B) (hB1 : 1 ≤ B)
    (hHb1 : 1 ≤ Hb)
    (hHS : (pair x (dropTop (v + 1))).length + S (pair x (dropTop (v + 1))).length + 2 ≤ Hb)
    (hHbH : Hb + 1 ≤ H) (hpairH : (pair x (dropTop (v + 1))).length + 1 ≤ H)
    (b : Bool) (hb : b = true ↔ pair x (dropTop (v + 1)) ∈ L) :
    (bodyTM M).HoareTime
      (fun inp work out => inp = I ∧ work = enumBank k x N H v a r ∧
        ∃ s : Γw, s ≠ Γw.one ∧ out = NTM.outSlot s)
      (fun inp work out => inp = I ∧
        work = enumBank k x N H (v + 1) (a + if b then 1 else 0) (r + if b then 0 else 1) ∧
        out = TM.blankTape)
      (bodyTime k x T H Hb B v a r) := by
  have hpinned : ∀ (W : Fin (enumTapes k) → Tape) (O : Tape), (∀ i, TM.Parked (W i)) →
      TM.Parked O → ∀ inp work out, (inp = I ∧ work = W ∧ out = O) →
      (TM.transitionInput inp = I ∧ (fun i => TM.transitionTape (work i)) = W ∧
        TM.transitionTape out = O) := by
    rintro W O hW hO inp work out ⟨rfl, rfl, rfl⟩
    exact trans_id_of_parked hI hW hO
  have h10 := wipe_hoareTime k x N H v a r I hI hISI Hb b hHbH hpairH
  have h9 := TM.seqTM_hoareTime _ _ (witnessBump_hoareTime k x N H v a r I hI Hb b)
    (fun inp work out h => trans_of_parked_pred (by rw [h.1]; exact hI) h.2.2.2.2.2.2.2.1 (by
      rw [h.2.1]; exact TM.blankTape_parked) h) h10
  have h8 := TM.seqTM_hoareTime _ _ (tallyBump_hoareTime k x N H v a r I hI hIz Hb b)
    (fun inp work out h => trans_of_parked_pred (by rw [h.1]; exact hI) h.2.2.2.2.2.2.1 (by
      rw [h.2.1]; exact TM.blankTape_parked) h) h9
  have h7 := TM.seqTM_hoareTime _ _ (publishVerdict_hoareTime k x N H v a r I hI Hb b)
    (fun inp work out h => trans_of_parked_pred (by rw [h.1]; exact hI) h.2.2.2.1 (by
      obtain ⟨s, -, hs⟩ := h.2.1
      rw [hs]
      exact NTM.outSlot_parked s) h) h8
  have h6 := TM.seqTM_hoareTime _ _
    (parkVerdict_hoareTime k x N H v a r I hISI hIhead Hb hHb1 b)
    (fun inp work out h => trans_of_parked_pred (by rw [h.1]; exact hI) h.2.2.2.2.1 (by
      rw [h.2.1]; exact TM.blankTape_parked) h) h7
  have h5 := TM.seqTM_hoareTime _ _
    (matrix_hoareTime_bool M hdec hdecS x N H v a r I hI hISI Hb hHS b hb)
    (fun inp work out h => midMatrix_trans k x N H v a r I hI Hb hHb1 b inp work out h) h6
  have h4 := TM.seqTM_hoareTime _ _ (copyPair_hoareTime k x N H v a r I hI)
    (hpinned _ _ (afterCopy_parked k x N H v a r) TM.blankTape_parked) h5
  have h3 := TM.seqTM_hoareTime _ _
    (parkPair_hoareTime k x N H v a r I hISI hIhead B hB1)
    (hpinned _ _ (afterPair_parked k x N H v a r) TM.blankTape_parked) h4
  have h2 := TM.seqTM_hoareTime _ _ (emit_hoareTime k x N H v a r I hI hISI B hB)
    (fun inp work out h => midEmit_trans k x N H v a r I hI B hB1 inp work out h) h3
  have h1 := TM.seqTM_hoareTime _ _ (blankSlot_hoareTime k x N H v a r I hI)
    (hpinned _ _ (enumBank_parked k x N H v a r) TM.blankTape_parked) h2
  exact h1

end PolyExists

end Complexity

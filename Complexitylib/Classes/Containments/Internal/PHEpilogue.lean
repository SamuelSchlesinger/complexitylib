/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHLoop
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub

/-!
# The enumerator's epilogue

⚠️ Unreviewed by Bolton

The loop leaves the accepting tally on `PolyExists.aIdx`, and the answer is whether it is
positive. A machine has no `>`; it has subtraction and a test against zero. So the epilogue makes
a one on the permanently blank tape, subtracts the tally from it — the difference is zero exactly
when the tally is positive — and tests that difference against zero, publishing the answer.

The two tapes it borrows for the test are the emitter's target and the matrix machine's input:
both are blank once the loop's last wipe has run, and nothing reads them again.

## Main results

- `PolyExists.epilogueTM` — the epilogue, and `PolyExists.epilogueTime` its running time
- `PolyExists.epilogueTM_hoareTime` — its contract: the slot ends holding `decide (0 < a)`
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- The epilogue's arithmetic: make a one, subtract the accepting tally from it. -/
def epiloguePreTM (k : ℕ) : TM (enumTapes k) :=
  TM.bigSeqTM [TM.binarySuccTM (zIdx k),
    TM.binaryRippleSubTM (zIdx k) (aIdx k) (resIdx k)]

/-- The epilogue's tail: put the test's answer at cell one and publish it. -/
def epiloguePostTM (k : ℕ) : TM (enumTapes k) :=
  TM.seqTM (TM.bigSeqTM ([yIdx k].map TM.rewindWorkTM)) (TM.writeOutputBitTM (yIdx k))

/-- **The enumerator's epilogue.** -/
def epilogueTM (k : ℕ) : TM (enumTapes k) :=
  TM.seqTM (epiloguePreTM k)
    (TM.seqTM (TM.binaryEqTM (resIdx k) (y1Idx k) (yIdx k)) (epiloguePostTM k))

/-- The bank the epilogue's arithmetic leaves behind. -/
def epilogueBank (k : ℕ) (x : List Bool) (N H A R : ℕ) : Fin (enumTapes k) → Tape :=
  Function.update (Function.update (enumBank k x N H N A R) (zIdx k) (natTape 1))
    (resIdx k) (natTape (1 - A))

theorem epilogueBank_parked (k : ℕ) (x : List Bool) (N H A R : ℕ) (j : Fin (enumTapes k)) :
    TM.Parked (epilogueBank k x N H A R j) := by
  rw [epilogueBank]
  by_cases h1 : j = resIdx k
  · rw [h1, Function.update_self]
    exact natTape_parked _
  · rw [Function.update_of_ne h1]
    by_cases h2 : j = zIdx k
    · rw [h2, Function.update_self]
      exact natTape_parked _
    · rw [Function.update_of_ne h2]
      exact enumBank_parked k x N H N A R j

theorem epilogueBank_cells_zero (k : ℕ) (x : List Bool) (N H A R : ℕ)
    (j : Fin (enumTapes k)) : (epilogueBank k x N H A R j).cells 0 = Γ.start := by
  rw [epilogueBank]
  by_cases h1 : j = resIdx k
  · rw [h1, Function.update_self]
    exact NTM.natTape_cells_zero _
  · rw [Function.update_of_ne h1]
    by_cases h2 : j = zIdx k
    · rw [h2, Function.update_self]
      exact NTM.natTape_cells_zero _
    · rw [Function.update_of_ne h2]
      exact (enumBank_startInvariant k x N H N A R j).1

/-- The state the epilogue's test leaves: every tape parked, and the answer bit sitting at cell
one of the register the test wrote to. -/
def afterEq (k : ℕ) (b : Bool) (I : Tape) (B : ℕ) : TM.TapePred (enumTapes k) :=
  fun inp work out => inp = I ∧ out = NTM.outSlot Γw.one ∧
    (∀ j, TM.Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) ∧
    (work (yIdx k)).head ≤ B ∧ (work (yIdx k)).cells 1 = Γ.ofBool b

/-- **The epilogue's publication.** Rewind the register holding the test's answer and copy its
bit into the output slot, where the surrounding obligation reads it. -/
theorem epiloguePostTM_hoareTime (k : ℕ) (b : Bool) (I : Tape) (B : ℕ) (hI : TM.Parked I) :
    (epiloguePostTM k).HoareTime
      (afterEq k b I B)
      (fun _inp _work out => out = NTM.outSlot (TM.readBackWrite (Γ.ofBool b)))
      (1 * (B + 3) + 1 + 1 + 1) := by
  intro inp work out hpre
  obtain ⟨hi, ho, hpark, hzero, hhead, hcell⟩ := hpre
  have hIp : TM.Parked inp := by rw [hi]; exact hI
  have hOp : TM.Parked out := by rw [ho]; exact NTM.outSlot_parked _
  set W' : Fin (enumTapes k) → Tape :=
    fun j => if j = yIdx k then (⟨1, (work (yIdx k)).cells⟩ : Tape) else work j with hW'
  have hW'P : ∀ j, TM.Parked (W' j) := by
    intro j
    simp only [hW']
    split
    · exact ⟨le_refl 1, fun i hi2 => (hpark (yIdx k)).2 i hi2⟩
    · exact hpark j
  have hrew : (TM.bigSeqTM ([yIdx k].map TM.rewindWorkTM)).HoareTime
      (fun inp' work' out' => inp' = inp ∧ work' = work ∧ out' = out)
      (fun inp' work' out' => inp' = inp ∧ work' = W' ∧ out' = out)
      (1 * (B + 3) + 1) := by
    refine ((TM.rewindList_hoareTime [yIdx k] (by simp) B inp work out hIp hOp hpark
      ?_).strengthen_post ?_).mono_bound (by simp)
    · intro j hj
      rw [List.mem_singleton.mp hj]
      exact ⟨hzero (yIdx k), hhead⟩
    · rintro inp' work' out' ⟨rfl, rfl, hin, hout⟩
      refine ⟨rfl, funext fun j => ?_, rfl⟩
      by_cases hj : j = yIdx k
      · rw [hj, hin (yIdx k) (by simp), hW']
        simp
      · rw [hout j (by simpa using hj), hW']
        simp [hj]
  have htrans : ∀ inp' work' out', (inp' = inp ∧ work' = W' ∧ out' = out) →
      (TM.transitionInput inp' = inp ∧ (fun i => TM.transitionTape (work' i)) = W' ∧
        TM.transitionTape out' = out) := by
    rintro inp' work' out' ⟨rfl, rfl, rfl⟩
    exact ⟨TM.transitionInput_eq_self hIp.read_ne_start,
      funext fun i => TM.transitionTape_eq_self (hW'P i).read_ne_start,
      TM.transitionTape_eq_self hOp.read_ne_start⟩
  have hpub : (TM.writeOutputBitTM (yIdx k)).HoareTime
      (fun inp' work' out' => inp' = inp ∧ work' = W' ∧ out' = out)
      (fun _inp _work out' => out' = NTM.outSlot (TM.readBackWrite (Γ.ofBool b))) 1 := by
    refine (TM.writeOutputBitTM_hoareTime_frame (yIdx k) inp W' out hIp hW'P hOp).strengthen_post
      ?_
    rintro inp' work' out' ⟨-, -, hout'⟩
    rw [hout', ho, show (W' (yIdx k)).read = Γ.ofBool b from by
      simp only [hW', ite_eq_left rfl]
      show (work (yIdx k)).cells 1 = _
      exact hcell]
    exact NTM.outSlot_write Γw.one (TM.readBackWrite (Γ.ofBool b))
  exact TM.seqTM_hoareTime _ _ hrew htrans hpub inp work out ⟨rfl, rfl, rfl⟩



/-- A counter tape holding zero is the blank tape. -/
theorem natTape_zero_eq : natTape 0 = TM.blankTape := by
  refine Tape.ext rfl (funext fun j => ?_)
  show ((Tape.init ((Nat.bits 0).map Γ.ofBool)).move Dir3.right).cells j
    = ((Tape.init ([] : List Γ)).move Dir3.right).cells j
  rw [show Nat.bits 0 = [] from by simp]
  rfl

/-- Strict order as a truncated subtraction, which is what a machine can test. -/
theorem lt_iff_succ_sub_zero (r a : ℕ) : r < a ↔ (r + 1) - a = 0 := by omega


theorem epilogueBank_res (k : ℕ) (x : List Bool) (N H A R : ℕ) :
    epilogueBank k x N H A R (resIdx k) = natTape (1 - A) := by
  rw [epilogueBank, Function.update_self]

theorem epilogueBank_y1 (k : ℕ) (x : List Bool) (N H A R : ℕ) :
    epilogueBank k x N H A R (y1Idx k) = TM.blankTape := by
  rw [epilogueBank, Function.update_of_ne (Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 3 + k + 4; omega)),
    Function.update_of_ne (Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 3 + k + 6; omega)), enumBank_y1]

theorem epilogueBank_y (k : ℕ) (x : List Bool) (N H A R : ℕ) :
    epilogueBank k x N H A R (yIdx k) = TM.blankTape := by
  rw [epilogueBank,
    Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k ≠ 3 + k + 4; omega)),
    Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k ≠ 3 + k + 6; omega)), enumBank_y]

/-- **The epilogue's test.** The difference is zero exactly when the accepting tally is
positive, so comparing it with zero decides the bounded existential. -/
theorem epilogueEq_hoareTime (k : ℕ) (x : List Bool) (N H A R : ℕ) (I : Tape) (hI : TM.Parked I)
    (hIsi : Tape.StartInvariant I) :
    (TM.binaryEqTM (resIdx k) (y1Idx k) (yIdx k)).HoareTime
      (fun inp work out => inp = I ∧ work = epilogueBank k x N H A R ∧
        out = NTM.outSlot Γw.one)
      (afterEq k (decide (0 < A)) I 2)
      (TM.binaryEqTime (1 - A).bits (0 : ℕ).bits) := by
  have hsz : resIdx k ≠ y1Idx k := Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 2; omega)
  have hsc : resIdx k ≠ yIdx k := Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k; omega)
  have hzc : y1Idx k ≠ yIdx k := Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 3 + k; omega)
  intro inp work out hpre
  obtain ⟨hi, hw, ho⟩ := hpre
  set W := epilogueBank k x N H A R with hWdef
  have hWP : ∀ j, TM.Parked (W j) := epilogueBank_parked k x N H A R
  have hWz : ∀ j, (W j).cells 0 = Γ.start := epilogueBank_cells_zero k x N H A R
  have hlhs : (W (resIdx k)).HasBinaryString (1 - A).bits := by
    rw [hWdef, epilogueBank_res k x N H A R]
    exact (Tape.init_move_right_hasBinaryNat _).2
  have hrhs : (W (y1Idx k)).HasBinaryString (0 : ℕ).bits := by
    rw [hWdef, epilogueBank_y1 k x N H A R,
      show TM.blankTape = natTape 0 from natTape_zero_eq.symm]
    exact (Tape.init_move_right_hasBinaryNat 0).2
  have hres : (W (yIdx k)).HasBinaryPrefix [] := by
    rw [hWdef, epilogueBank_y k x N H A R]
    refine ⟨rfl, nofun, fun i _ => ?_⟩
    show ((Tape.init ([] : List Γ)).move Dir3.right).cells (i + 1) = Γ.blank
    rw [Tape.move_cells, Tape.init_nil_cells_succ]
  have hIp : TM.Parked inp := by rw [hi]; exact hI
  have hOp : TM.Parked out := by rw [ho]; exact NTM.outSlot_parked _
  rw [hi, hw, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hinp', hres', hlhs', hlhsh, hrhs', hrhsh, hother', hout'⟩ :=
    TM.binaryEqTM_reachesIn_frame (resIdx k) (y1Idx k) (yIdx k) ⟨hsz, hsc, hzc⟩
      (1 - A).bits (0 : ℕ).bits I W (NTM.outSlot Γw.one) hlhs hrhs hres
      (by rw [← hi]; exact hIp.read_ne_start) (fun i _ _ _ => (hWP i).read_ne_start)
      (NTM.outSlot_parked _).read_ne_start
  obtain ⟨-, hSI', -⟩ := TM.startInvariant_reachesIn _ hreach hIsi
    (fun j => ⟨hWz j, fun i hi2 => (hWP j).2 i hi2⟩)
    ⟨rfl, fun j hj => (NTM.outSlot_parked Γw.one).2 j hj⟩
  have hbits : (decide ((1 - A).bits = (0 : ℕ).bits)) = decide (0 < A) := by
    refine decide_eq_decide.mpr ?_
    rw [show (1 - A) = (0 + 1) - A from by omega, lt_iff_succ_sub_zero]
    exact ⟨fun h => bits_injective h, fun h => by rw [h]⟩
  refine ⟨c', t, ht, hreach, hhalt, hinp', hout', fun j => ?_, fun j => (hSI' j).1, ?_, ?_⟩
  · refine ⟨?_, fun i hi2 => (hSI' j).2 i hi2⟩
    by_cases h1 : j = yIdx k
    · rw [h1, hres'.1]; omega
    by_cases h2 : j = resIdx k
    · rw [h2]; exact hlhsh
    by_cases h3 : j = y1Idx k
    · rw [h3]; exact hrhsh
    · rw [hother' j h2 h3 h1]; exact (hWP j).1
  · rw [hres'.1]
    simp
  · rw [hres'.2.1 0 (by simp), ← hbits]
    simp

theorem enumBank_z_eq_natTape (k : ℕ) (x : List Bool) (N H v a r : ℕ) :
    enumBank k x N H v a r (zIdx k) = natTape 0 := by
  rw [enumBank_z, natTape_zero_eq]

/-- **The epilogue's arithmetic.** Make a one on the blank tape, then subtract the accepting
tally from it; the difference is zero exactly when that tally is positive. -/
theorem epiloguePreTM_hoareTime (k : ℕ) (x : List Bool) (N H A R : ℕ) (I : Tape)
    (hI : TM.Parked I) :
    (epiloguePreTM k).HoareTime
      (fun inp work out => inp = I ∧ work = enumBank k x N H N A R ∧
        out = NTM.outSlot Γw.one)
      (fun inp work out => inp = I ∧ work = epilogueBank k x N H A R ∧
        out = NTM.outSlot Γw.one)
      (2 * (max (TM.binarySuccTime 0) (TM.binaryRippleSubTime 1 A) + 1) + 1) := by
  set B0 := enumBank k x N H N A R with hB0
  set B1 := Function.update B0 (zIdx k) (natTape 1) with hB1
  have hB1P : ∀ i, TM.Parked (B1 i) := by
    intro i
    rw [hB1]
    by_cases h : i = zIdx k
    · rw [h, Function.update_self]
      exact natTape_parked _
    · rw [Function.update_of_ne h]
      exact enumBank_parked k x N H N A R i
  have hstage : ∀ j, (hj : j < [TM.binarySuccTM (zIdx k),
      TM.binaryRippleSubTM (zIdx k) (aIdx k) (resIdx k)].length) →
      ([TM.binarySuccTM (zIdx k),
        TM.binaryRippleSubTM (zIdx k) (aIdx k) (resIdx k)][j]).HoareTime
        (fun inp work out => inp = I ∧
          work = (if j = 0 then B0 else B1) ∧ out = NTM.outSlot Γw.one)
        (fun inp work out => inp = I ∧
          work = (if j + 1 = 0 then B0 else if j + 1 = 1 then B1 else
            epilogueBank k x N H A R) ∧ out = NTM.outSlot Γw.one)
        (max (TM.binarySuccTime 0) (TM.binaryRippleSubTime 1 A)) := by
    intro j hj
    match j, hj with
    | 0, _ =>
      show (TM.binarySuccTM (zIdx k)).HoareTime _ _ _
      refine ((TM.binarySuccTM_hoareTime_pinned (zIdx k) 0 I B0 (NTM.outSlot Γw.one)
        (enumBank_z_eq_natTape k x N H N A R) hI.read_ne_start
        (fun i _ => (enumBank_parked k x N H N A R i).read_ne_start)
        (NTM.outSlot_parked _).read_ne_start).consequence
        (fun _ _ _ h => ⟨h.1, by rw [h.2.1]; rfl, h.2.2⟩) ?_ (le_max_left _ _))
      rintro inp work out ⟨hi, hw, ho⟩
      refine ⟨hi, ?_, ho⟩
      rw [hw]
      show Function.update B0 (zIdx k) (natTape (0 + 1)) = B1
      rw [hB1]
    | 1, _ =>
      show (TM.binaryRippleSubTM (zIdx k) (aIdx k) (resIdx k)).HoareTime _ _ _
      have hdist : TM.BinaryRippleSubDistinct (zIdx k) (aIdx k) (resIdx k) :=
        ⟨Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 5; omega),
          Fin.ne_of_val_ne (by show 3 + k + 6 ≠ 3 + k + 4; omega),
          Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 4; omega)⟩
      have hz : B1 (zIdx k) = natTape 1 := by rw [hB1, Function.update_self]
      have ha : B1 (aIdx k) = natTape A := by
        rw [hB1, Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 5 ≠ 3 + k + 6; omega)),
          hB0, enumBank_a]
      have hres : (B1 (resIdx k)).HasBinaryNat 0 := by
        rw [hB1, Function.update_of_ne (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 6; omega)),
          hB0, enumBank_blank k x N H N A R _ (res_ne_regs k).1 (res_ne_regs k).2.1
            (res_ne_regs k).2.2
            (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 0; omega))
            (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 1; omega))
            (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 3; omega))
            (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 7; omega)),
          ← natTape_zero_eq]
        exact Tape.init_move_right_hasBinaryNat 0
      refine ((TM.binaryRippleSubTM_hoareTime_pinned (zIdx k) (aIdx k) (resIdx k) hdist 1 A
        I B1 (NTM.outSlot Γw.one) hz ha hres hI
        (fun i _ _ _ => hB1P i) (NTM.outSlot_parked _)).consequence
        (fun _ _ _ h => h) ?_ (le_max_right _ _))
      rintro inp work out ⟨hi, hw, ho⟩
      refine ⟨hi, ?_, ho⟩
      rw [hw]
      show Function.update B1 (resIdx k) (natTape (1 - A)) = epilogueBank k x N H A R
      rw [epilogueBank, hB1]
  have h := TM.bigSeqTM_hoareTime_pinned
    [TM.binarySuccTM (zIdx k), TM.binaryRippleSubTM (zIdx k) (aIdx k) (resIdx k)] I
    (fun j => if j = 0 then B0 else if j = 1 then B1 else epilogueBank k x N H A R)
    (fun _ => NTM.outSlot Γw.one) (max (TM.binarySuccTime 0) (TM.binaryRippleSubTime 1 A))
    hI (fun j i => by
      split
      · exact enumBank_parked k x N H N A R i
      · split
        · exact hB1P i
        · exact epilogueBank_parked k x N H A R i)
    (fun _ => NTM.outSlot_parked _)
    (fun j hj => by
      have := hstage j hj
      match j, hj with
      | 0, _ => exact this
      | 1, _ => exact this)
  exact h

/-- The state between the epilogue's test and its publication survives a phase boundary: every
tape it names is parked, so the boundary is the identity. -/
theorem afterEq_trans (k : ℕ) (b : Bool) (I : Tape) (B : ℕ) (hI : TM.Parked I)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : afterEq k b I B inp work out) :
    afterEq k b I B (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
      (TM.transitionTape out) := by
  obtain ⟨hi, ho, hpark, hzero, hhead, hcell⟩ := h
  have hid : ∀ j, TM.transitionTape (work j) = work j :=
    fun j => TM.transitionTape_eq_self (hpark j).read_ne_start
  have hidI : TM.transitionInput inp = inp := by
    rw [hi]; exact TM.transitionInput_eq_self hI.read_ne_start
  have hidO : TM.transitionTape out = out := by
    rw [ho]; exact TM.transitionTape_eq_self (NTM.outSlot_parked _).read_ne_start
  rw [hidI, hidO, show (fun i => TM.transitionTape (work i)) = work from funext hid]
  exact ⟨hi, ho, hpark, hzero, hhead, hcell⟩

/-- The epilogue's running time: its three stages and the two boundaries between them. -/
def epilogueTime (A : ℕ) : ℕ :=
  (2 * (max (TM.binarySuccTime 0) (TM.binaryRippleSubTime 1 A) + 1) + 1) + 1 +
    (TM.binaryEqTime (1 - A).bits (0 : ℕ).bits + 1 + (1 * (2 + 3) + 1 + 1 + 1))

/-- **The epilogue's contract.** From the bank the loop leaves, the machine writes `1` into the
verdict slot exactly when some witness was accepted. -/
theorem epilogueTM_hoareTime (k : ℕ) (x : List Bool) (N H A R : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIsi : Tape.StartInvariant I) :
    (epilogueTM k).HoareTime
      (fun inp work out => inp = I ∧ work = enumBank k x N H N A R ∧
        out = NTM.outSlot Γw.one)
      (fun _inp _work out =>
        out = NTM.outSlot (TM.readBackWrite (Γ.ofBool (decide (0 < A)))))
      (epilogueTime A) := by
  have htrans1 : ∀ inp work out,
      (inp = I ∧ work = epilogueBank k x N H A R ∧ out = NTM.outSlot Γw.one) →
      (TM.transitionInput inp = I ∧
        (fun i => TM.transitionTape (work i)) = epilogueBank k x N H A R ∧
        TM.transitionTape out = NTM.outSlot Γw.one) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨TM.transitionInput_eq_self hI.read_ne_start,
      funext fun i => TM.transitionTape_eq_self (epilogueBank_parked k x N H A R i).read_ne_start,
      TM.transitionTape_eq_self (NTM.outSlot_parked _).read_ne_start⟩
  exact TM.seqTM_hoareTime _ _ (epiloguePreTM_hoareTime k x N H A R I hI) htrans1
    (TM.seqTM_hoareTime _ _ (epilogueEq_hoareTime k x N H A R I hI hIsi)
      (fun inp work out h => afterEq_trans k (decide (0 < A)) I 2 hI inp work out h)
      (epiloguePostTM_hoareTime k (decide (0 < A)) I 2 hI))

end PolyExists

end Complexity

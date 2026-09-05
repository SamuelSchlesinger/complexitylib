/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHBody
public import Complexitylib.Models.TuringMachine.Subroutines.Internal
public import Complexitylib.Models.TuringMachine.Subroutines.ParkRewind
public import Complexitylib.Models.TuringMachine.Registers.InputLen
public import Complexitylib.Models.TuringMachine.Registers.Horner
public import Complexitylib.Models.TuringMachine.Registers.RegisterOps
public import Complexitylib.Models.TuringMachine.Registers.EmitSeq

/-!
# The enumerator's prologue

⚠️ Unreviewed by Bolton

Before the loop can start, three tapes have to be filled: a copy of the real input, for the pair
emitter to read; the horizon the counter is compared against; and the unary register that drives
each pass's wipe.

`TM.copyInputToWorkTM`'s own contract says nothing about the tapes it does not write, and it is
used here beside a dozen that must survive. It does not disturb them: every tape but its target
is written `blank` and moved by `TM.idleDir`, so a blank tape comes back blank — which is what
the frame below records, by induction along the run.

## Main results

- `PolyExists.blankTape_idle` — an idled blank tape is unchanged
- `PolyExists.copyInputToWorkTM_blank_frame` — the copier leaves every other blank tape blank
- `PolyExists.copyX_hoareTime` — the copy stage's contract, frame included
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {n : ℕ}

/-- **An idled blank tape is unchanged.** Writing a blank under the head of a blank tape changes
nothing, and `TM.idleDir` does not move a head that is off the marker. -/
theorem blankTape_idle :
    TM.blankTape.writeAndMove Γw.blank.toΓ (TM.idleDir TM.blankTape.read) = TM.blankTape := by
  have hread : TM.blankTape.read = Γ.blank := Tape.init_nil_move_right_read
  rw [hread]
  show (TM.blankTape.write Γ.blank).move (TM.idleDir Γ.blank) = TM.blankTape
  rw [TM.idleDir, ite_eq_right (by decide)]
  refine Tape.ext ?_ ?_
  · show (TM.blankTape.write Γ.blank).head = TM.blankTape.head
    rw [Tape.write_head]
  · show (TM.blankTape.write Γ.blank).cells = TM.blankTape.cells
    rw [Tape.write, ite_eq_right (by show ¬ ((1 : ℕ) = 0); omega)]
    funext j
    show Function.update TM.blankTape.cells TM.blankTape.head Γ.blank j = TM.blankTape.cells j
    by_cases hj : j = TM.blankTape.head
    · rw [hj, Function.update_self]
      show Γ.blank = TM.blankTape.cells 1
      exact hread.symm
    · rw [Function.update_of_ne hj]

/-- **One step of the copier leaves a blank tape blank.** -/
theorem copyStep_blank (idx : Fin n) {c c' : Cfg n (TM.copyInputToWorkTM idx).Q}
    (hstep : (TM.copyInputToWorkTM idx).step c = some c') (i : Fin n) (hi : i ≠ idx)
    (h : c.work i = TM.blankTape) : c'.work i = TM.blankTape := by
  rw [TM.step] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [← Option.some_inj.mp hstep]
    show (c.work i).writeAndMove
        (((TM.copyInputToWorkTM idx).δ c.state c.input.read (fun j => (c.work j).read)
          c.output.read).2.1 i).toΓ
        (((TM.copyInputToWorkTM idx).δ c.state c.input.read (fun j => (c.work j).read)
          c.output.read).2.2.2.2.1 i) = TM.blankTape
    have hwrite : ∀ (s : TM.CopyPhase) (iH : Γ) (wH : Fin n → Γ) (oH : Γ),
        ((TM.copyInputToWorkTM idx).δ s iH wH oH).2.1 i = Γw.blank ∧
        ((TM.copyInputToWorkTM idx).δ s iH wH oH).2.2.2.2.1 i = TM.idleDir (wH i) := by
      intro s iH wH oH
      cases s with
      | copying =>
          show (if iH = Γ.blank then TM.allIdle _ iH wH oH else _).2.1 i = _ ∧
            (if iH = Γ.blank then TM.allIdle _ iH wH oH else _).2.2.2.2.1 i = _
          by_cases hb : iH = Γ.blank
          · subst hb
            exact ⟨rfl, rfl⟩
          · erw [ite_eq_right hb]
            exact ⟨ite_eq_right hi, ite_eq_right hi⟩
      | done => exact ⟨rfl, rfl⟩
    obtain ⟨hw, hd⟩ := hwrite c.state c.input.read (fun j => (c.work j).read) c.output.read
    rw [hw, hd, h]
    exact blankTape_idle

/-- **The copier leaves every other blank tape blank**, which is the frame its own contract does
not record. -/
theorem copyInputToWorkTM_blank_frame (idx : Fin n) :
    ∀ {t : ℕ} {c c' : Cfg n (TM.copyInputToWorkTM idx).Q},
      (TM.copyInputToWorkTM idx).reachesIn t c c' →
      ∀ i, i ≠ idx → c.work i = TM.blankTape → c'.work i = TM.blankTape := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach i hi h
      cases hreach
      exact h
  | succ t ih =>
      intro c c' hreach i hi h
      cases hreach with
      | step hstep hrest => exact ih hrest i hi (copyStep_blank idx hstep i hi h)

/-- **One step of the copier leaves the real output blank**, for the same reason. -/
theorem copyStep_blank_out (idx : Fin n) {c c' : Cfg n (TM.copyInputToWorkTM idx).Q}
    (hstep : (TM.copyInputToWorkTM idx).step c = some c')
    (h : c.output = TM.blankTape) : c'.output = TM.blankTape := by
  rw [TM.step] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [← Option.some_inj.mp hstep]
    show c.output.writeAndMove
        (((TM.copyInputToWorkTM idx).δ c.state c.input.read (fun j => (c.work j).read)
          c.output.read).2.2.1).toΓ
        (((TM.copyInputToWorkTM idx).δ c.state c.input.read (fun j => (c.work j).read)
          c.output.read).2.2.2.2.2) = TM.blankTape
    have hwrite : ∀ (s : TM.CopyPhase) (iH : Γ) (wH : Fin n → Γ) (oH : Γ),
        ((TM.copyInputToWorkTM idx).δ s iH wH oH).2.2.1 = Γw.blank ∧
        ((TM.copyInputToWorkTM idx).δ s iH wH oH).2.2.2.2.2 = TM.idleDir oH := by
      intro s iH wH oH
      cases s with
      | copying =>
          show (if iH = Γ.blank then TM.allIdle _ iH wH oH else _).2.2.1 = _ ∧
            (if iH = Γ.blank then TM.allIdle _ iH wH oH else _).2.2.2.2.2 = _
          by_cases hb : iH = Γ.blank
          · subst hb
            exact ⟨rfl, rfl⟩
          · erw [ite_eq_right hb]
            exact ⟨rfl, rfl⟩
      | done => exact ⟨rfl, rfl⟩
    obtain ⟨hw, hd⟩ := hwrite c.state c.input.read (fun j => (c.work j).read) c.output.read
    rw [hw, hd, h]
    exact blankTape_idle

theorem copyInputToWorkTM_blank_frame_out (idx : Fin n) :
    ∀ {t : ℕ} {c c' : Cfg n (TM.copyInputToWorkTM idx).Q},
      (TM.copyInputToWorkTM idx).reachesIn t c c' →
      c.output = TM.blankTape → c'.output = TM.blankTape := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach h
      cases hreach
      exact h
  | succ t ih =>
      intro c c' hreach h
      cases hreach with
      | step hstep hrest => exact ih hrest (copyStep_blank_out idx hstep h)

/-- The blank tape carries the empty binary prefix. -/
theorem blankTape_hasBinaryPrefix_nil : TM.blankTape.HasBinaryPrefix [] := by
  refine ⟨rfl, nofun, fun i _ => ?_⟩
  show ((Tape.init ([] : List Γ)).move Dir3.right).cells (i + 1) = Γ.blank
  rw [Tape.move_cells, Tape.init_nil_cells_succ]

/-- **The input copy, contracted with its frame.** -/
theorem copyX_hoareTime (k : ℕ) (x : List Bool) :
    (TM.copyInputToWorkTM (xIdx k)).HoareTime
      (fun inp work out => inp = strTape x ∧ work = (fun _ => TM.blankTape) ∧
        out = TM.blankTape)
      (fun inp work out => inp.cells = (strTape x).cells ∧ inp.head = x.length + 1 ∧
        (∀ i, i ≠ xIdx k → work i = TM.blankTape) ∧
        (work (xIdx k)).HasBinaryPrefix x ∧ (work (xIdx k)).cells 0 = Γ.start ∧
        out = TM.blankTape)
      (x.length + 1) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  obtain ⟨c', t, ht, hreach, hhalt, hcells, hhead, hprefix⟩ :=
    TM.copyInputToWorkTM_started_hoareTime (xIdx k) x (strTape x) (fun _ => TM.blankTape)
      TM.blankTape ⟨rfl, blankTape_hasBinaryPrefix_nil⟩
  have hSI := TM.reachesIn_startInvariant hreach (strTape_startInvariant x)
    (fun _ => TM.blankTape_startInvariant) TM.blankTape_startInvariant
  exact ⟨c', t, ht, hreach, hhalt, hcells, hhead,
    fun i hi => copyInputToWorkTM_blank_frame (xIdx k) hreach i hi rfl,
    hprefix, (hSI.2.1 (xIdx k)).1, copyInputToWorkTM_blank_frame_out (xIdx k) hreach rfl⟩

/-- The register subroutines state their contracts with an output accumulator; with nothing
emitted that is just the blank tape. -/
theorem outAcc_nil_iff (out : Tape) : TM.OutAcc [] out ↔ out = TM.blankTape := by
  constructor
  · intro h
    refine TM.OutAcc.eq h ?_
    show TM.OutAcc [] TM.blankTape
    exact TM.outAcc_nil_init
  · intro h
    rw [h]
    exact TM.outAcc_nil_init

/-- A pinned contract with a blank output is an emit contract with nothing emitted. -/
theorem hoareTime_emit_of_pinned {m : ℕ} {tm : TM m} {inp₀ : Tape}
    {W W' : Fin m → Tape} {b : ℕ}
    (h : tm.HoareTime (fun inp work out => inp = inp₀ ∧ work = W ∧ out = TM.blankTape)
      (fun inp work out => inp = inp₀ ∧ work = W' ∧ out = TM.blankTape) b) :
    tm.HoareTime (TM.EmitPred inp₀ W []) (TM.EmitPred inp₀ W' []) b := by
  intro inp work out hpre
  obtain ⟨hi, hw, hout⟩ := hpre
  obtain ⟨c', t, ht, hreach, hhalt, hi', hw', ho'⟩ :=
    h inp work out ⟨hi, hw, (outAcc_nil_iff out).mp hout⟩
  exact ⟨c', t, ht, hreach, hhalt, hi', hw', (outAcc_nil_iff _).mpr ho'⟩

/-- **A unary register of `T` ones is the binary numeral `2 ^ T - 1`.** The two encodings agree
cell for cell, which is what lets the prologue produce the horizon without a doubling loop. -/
theorem bits_two_pow_sub_one' : ∀ T : ℕ, (2 ^ T - 1).bits = List.replicate T true := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
      have hrw : 2 ^ (T + 1) - 1 = 2 * (2 ^ T - 1) + 1 := by
        have h : 1 ≤ 2 ^ T := Nat.one_le_two_pow
        have : 2 ^ (T + 1) = 2 * 2 ^ T := by ring
        omega
      rw [hrw, Nat.bit1_bits, ih, List.replicate_succ]

theorem regTape_eq_natTape' (T : ℕ) : TM.regTape T = natTape (2 ^ T - 1) := by
  refine Tape.ext rfl (funext fun j => ?_)
  have hbits := bits_two_pow_sub_one' T
  have hlen : (2 ^ T - 1).bits.length = T := by rw [hbits, List.length_replicate]
  show TM.regCells T j = (natTape (2 ^ T - 1)).cells j
  rw [natTape, Tape.move_cells]
  by_cases hj : j = 0
  · rw [hj]
    show (if (0 : ℕ) = 0 then Γ.start else _) = _
    rw [ite_eq_left rfl, Tape.init_cells_zero]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Tape.init_cells_succ]
    show (if i + 1 = 0 then Γ.start else if i + 1 ≤ T then Γ.one else Γ.blank)
      = (((2 ^ T - 1).bits.map Γ.ofBool)[i]?).getD Γ.blank
    rw [ite_eq_right (by omega), hbits]
    by_cases hi : i < T
    · rw [ite_eq_left (by omega)]
      simp [hi, Γ.ofBool]
    · rw [ite_eq_right (by omega)]
      simp [hi]


/-- A unary register holding zero is the blank tape. -/
theorem regTape_zero' : TM.regTape 0 = TM.blankTape := by
  refine Tape.ext rfl (funext fun j => ?_)
  show TM.regCells 0 j = ((Tape.init ([] : List Γ)).move Dir3.right).cells j
  rw [Tape.move_cells]
  by_cases hj : j = 0
  · rw [hj]
    show (if (0 : ℕ) = 0 then Γ.start else _) = _
    rw [ite_eq_left rfl, Tape.init_cells_zero]
  · show (if j = 0 then Γ.start else if j ≤ 0 then Γ.one else Γ.blank) = _
    rw [ite_eq_right hj, ite_eq_right (by omega), show j = (j - 1) + 1 from by omega,
      Tape.init_nil_cells_succ]

/-- And so is a counter tape holding zero. -/
theorem natTape_zero_eq' : natTape 0 = TM.blankTape := by
  rw [← regTape_zero', regTape_eq_natTape' 0]
  norm_num


/-- **The enumerator's prologue.** Measure the input, evaluate the horizon's exponent and the
wipe height on unary registers, bump the exponent — a register of `m + 1` ones *is* the binary
numeral `2 ^ (m + 1) - 1` — and clear the scratch. -/
def prologueTM (k : ℕ) (p q : Polynomial ℕ) : TM (enumTapes k) :=
  TM.bigSeqTM
    [TM.inputLenRegTM (resIdx k),
      TM.polyEvalTM (resIdx k) (nIdx k) (y1Idx k) p,
      TM.incRegTM (nIdx k),
      TM.polyEvalTM (resIdx k) (regIdx k) (yIdx k) q,
      TM.clearRegTM (resIdx k),
      TM.clearRegTM (y1Idx k),
      TM.clearRegTM (yIdx k)]

/-- The bank the copy stage leaves: the input on its tape, everything else blank. -/
def copiedBank (k : ℕ) (x : List Bool) : Fin (enumTapes k) → Tape :=
  Function.update (fun _ => TM.blankTape) (xIdx k) (strTape x)

theorem copiedBank_parked (k : ℕ) (x : List Bool) (j : Fin (enumTapes k)) :
    TM.Parked (copiedBank k x j) := by
  rw [copiedBank]
  by_cases h : j = xIdx k
  · rw [h, Function.update_self]
    exact strTape_parked x
  · rw [Function.update_of_ne h]
    exact TM.blankTape_parked

theorem copiedBank_of_ne (k : ℕ) (x : List Bool) (j : Fin (enumTapes k)) (h : j ≠ xIdx k) :
    copiedBank k x j = TM.blankTape := by
  rw [copiedBank, Function.update_of_ne h]
/-- The cap the Horner evaluation stays under. -/
def prologueCap (p : Polynomial ℕ) (lx : ℕ) : ℕ :=
  ((TM.polyCoeffs p).sum + 1) * (lx + 1) ^ (TM.polyCoeffs p).length

theorem le_prologueCap (p : Polynomial ℕ) (lx : ℕ) : lx ≤ prologueCap p lx := by
  have hlen : 1 ≤ (TM.polyCoeffs p).length :=
    List.length_pos_iff.mpr (TM.polyCoeffs_ne_nil p)
  have h1 : lx + 1 ≤ (lx + 1) ^ (TM.polyCoeffs p).length :=
    Nat.le_self_pow (by omega) _
  have h2 : (lx + 1) ^ (TM.polyCoeffs p).length
      ≤ ((TM.polyCoeffs p).sum + 1) * (lx + 1) ^ (TM.polyCoeffs p).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold prologueCap
  omega

/-- The prologue's per-stage budget. -/
def prologueBnd (p q : Polynomial ℕ) (lx : ℕ) : ℕ :=
  max (max (max (2 * lx + 4)
      (TM.opBudget (prologueCap p lx) + 1 +
        ((p.natDegree + 1) * (TM.layerBudget (prologueCap p lx) + 1) + 1)))
    (max (2 * p.eval lx + 4)
      (TM.opBudget (prologueCap q lx) + 1 +
        ((q.natDegree + 1) * (TM.layerBudget (prologueCap q lx) + 1) + 1))))
    (max (2 * lx + 4) (max (2 * p.eval lx + 4) (2 * q.eval lx + 4)))

/-- The prologue's running time. -/
def prologueTime (p q : Polynomial ℕ) (lx : ℕ) : ℕ := 7 * (prologueBnd p q lx + 1) + 1

/-- **The prologue's contract.** From the bank the copy stage leaves it lands on the loop's
starting bank: the horizon on `PolyExists.nIdx`, the wipe height on `PolyExists.regIdx`, the
input copy where the emitter reads it, and everything else blank. -/
theorem prologueTM_hoareTime (k : ℕ) (p q : Polynomial ℕ) (x : List Bool) :
    (prologueTM k p q).HoareTime
      (fun inp work out => inp = strTape x ∧ work = copiedBank k x ∧ out = TM.blankTape)
      (fun inp work out => inp = strTape x ∧
        work = enumBank k x (2 ^ (p.eval x.length + 1) - 1) (q.eval x.length) 0 0 0 ∧
        out = TM.blankTape)
      (prologueTime p q x.length) := by
  set lx := x.length with hlx
  set m := p.eval lx with hm
  set Hq := q.eval lx with hHq
  set I : Tape := strTape x with hI
  have hIp : TM.Parked I := strTape_parked x
  have hne : ∀ (i i' : Fin (enumTapes k)), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  have hsn : resIdx k ≠ nIdx k := hne _ _ (by show 3 + k + 4 ≠ 3 + k + 3; omega)
  have hsy1 : resIdx k ≠ y1Idx k := hne _ _ (by show 3 + k + 4 ≠ 2; omega)
  have hny1 : nIdx k ≠ y1Idx k := hne _ _ (by show 3 + k + 3 ≠ 2; omega)
  have hsg : resIdx k ≠ regIdx k := hne _ _ (by show 3 + k + 4 ≠ 3 + k + 7; omega)
  have hsy : resIdx k ≠ yIdx k := hne _ _ (by show 3 + k + 4 ≠ 3 + k; omega)
  have hgy : regIdx k ≠ yIdx k := hne _ _ (by show 3 + k + 7 ≠ 3 + k; omega)
  set V0 : Fin (enumTapes k) → Tape := copiedBank k x with hV0
  set V1 := Function.update V0 (resIdx k) (TM.regTape lx) with hV1
  set V2 := Function.update (Function.update V1 (y1Idx k) (TM.regTape m)) (nIdx k)
    (TM.regTape m) with hV2
  set V3 := Function.update V2 (nIdx k) (TM.regTape (m + 1)) with hV3
  set V4 := Function.update (Function.update V3 (yIdx k) (TM.regTape Hq)) (regIdx k)
    (TM.regTape Hq) with hV4
  set V5 := Function.update V4 (resIdx k) (TM.regTape 0) with hV5
  set V6 := Function.update V5 (y1Idx k) (TM.regTape 0) with hV6
  set V7 := Function.update V6 (yIdx k) (TM.regTape 0) with hV7
  have hupd : ∀ (W : Fin (enumTapes k) → Tape) (i : Fin (enumTapes k)) (t : Tape),
      (∀ j, TM.Parked (W j)) → TM.Parked t → ∀ j, TM.Parked (Function.update W i t j) := by
    intro W i t hW ht j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact ht
    · rw [Function.update_of_ne hj]; exact hW j
  have hreg : ∀ v : ℕ, TM.Parked (TM.regTape v) := fun v => by
    rw [regTape_eq_natTape']; exact natTape_parked _
  have hV0P : ∀ j, TM.Parked (V0 j) := copiedBank_parked k x
  have hV1P : ∀ j, TM.Parked (V1 j) := hupd _ _ _ hV0P (hreg _)
  have hV2P : ∀ j, TM.Parked (V2 j) := hupd _ _ _ (hupd _ _ _ hV1P (hreg _)) (hreg _)
  have hV3P : ∀ j, TM.Parked (V3 j) := hupd _ _ _ hV2P (hreg _)
  have hV4P : ∀ j, TM.Parked (V4 j) := hupd _ _ _ (hupd _ _ _ hV3P (hreg _)) (hreg _)
  have hV5P : ∀ j, TM.Parked (V5 j) := hupd _ _ _ hV4P (hreg _)
  have hV6P : ∀ j, TM.Parked (V6 j) := hupd _ _ _ hV5P (hreg _)
  have hV7P : ∀ j, TM.Parked (V7 j) := hupd _ _ _ hV6P (hreg _)
  have hV0s : V0 (resIdx k) = TM.regTape 0 := by
    rw [hV0, copiedBank_of_ne k x _ (hne _ _ (by show 3 + k + 4 ≠ 0; omega)), regTape_zero']
  have hV1s : V1 (resIdx k) = TM.regTape lx := by rw [hV1, Function.update_self]
  have hV1n : V1 (nIdx k) = TM.regTape 0 := by
    rw [hV1, Function.update_of_ne (Ne.symm hsn), hV0,
      copiedBank_of_ne k x _ (hne _ _ (by show 3 + k + 3 ≠ 0; omega)), regTape_zero']
  have hV1y1 : V1 (y1Idx k) = TM.regTape 0 := by
    rw [hV1, Function.update_of_ne (Ne.symm hsy1), hV0,
      copiedBank_of_ne k x _ (hne _ _ (by show (2 : ℕ) ≠ 0; omega)), regTape_zero']
  have hV2n : V2 (nIdx k) = TM.regTape m := by rw [hV2, Function.update_self]
  have hV3s : V3 (resIdx k) = TM.regTape lx := by
    rw [hV3, Function.update_of_ne hsn, hV2, Function.update_of_ne hsn,
      Function.update_of_ne hsy1, hV1s]
  have hV3g : V3 (regIdx k) = TM.regTape 0 := by
    rw [hV3, Function.update_of_ne (hne _ _ (by show 3 + k + 7 ≠ 3 + k + 3; omega)), hV2,
      Function.update_of_ne (hne _ _ (by show 3 + k + 7 ≠ 3 + k + 3; omega)),
      Function.update_of_ne (hne _ _ (by show 3 + k + 7 ≠ 2; omega)), hV1,
      Function.update_of_ne (Ne.symm hsg), hV0,
      copiedBank_of_ne k x _ (hne _ _ (by show 3 + k + 7 ≠ 0; omega)), regTape_zero']
  have hV3y : V3 (yIdx k) = TM.regTape 0 := by
    rw [hV3, Function.update_of_ne (hne _ _ (by show 3 + k ≠ 3 + k + 3; omega)), hV2,
      Function.update_of_ne (hne _ _ (by show 3 + k ≠ 3 + k + 3; omega)),
      Function.update_of_ne (hne _ _ (by show 3 + k ≠ 2; omega)), hV1,
      Function.update_of_ne (Ne.symm hsy), hV0,
      copiedBank_of_ne k x _ (hne _ _ (by show 3 + k ≠ 0; omega)), regTape_zero']
  have hV4s : V4 (resIdx k) = TM.regTape lx := by
    rw [hV4, Function.update_of_ne hsg, Function.update_of_ne hsy, hV3s]
  have hV5y1 : V5 (y1Idx k) = TM.regTape m := by
    rw [hV5, Function.update_of_ne (Ne.symm hsy1), hV4,
      Function.update_of_ne (hne _ _ (by show (2 : ℕ) ≠ 3 + k + 7; omega)),
      Function.update_of_ne (hne _ _ (by show (2 : ℕ) ≠ 3 + k; omega)), hV3,
      Function.update_of_ne (hne _ _ (by show (2 : ℕ) ≠ 3 + k + 3; omega)), hV2,
      Function.update_of_ne (hne _ _ (by show (2 : ℕ) ≠ 3 + k + 3; omega)),
      Function.update_self]
  have hV6y : V6 (yIdx k) = TM.regTape Hq := by
    rw [hV6, Function.update_of_ne (hne _ _ (by show 3 + k ≠ 2; omega)), hV5,
      Function.update_of_ne (Ne.symm hsy), hV4, Function.update_of_ne hgy.symm,
      Function.update_self]
  refine (TM.bigSeqTM_hoareTime
    [TM.inputLenRegTM (resIdx k),
      TM.polyEvalTM (resIdx k) (nIdx k) (y1Idx k) p,
      TM.incRegTM (nIdx k),
      TM.polyEvalTM (resIdx k) (regIdx k) (yIdx k) q,
      TM.clearRegTM (resIdx k),
      TM.clearRegTM (y1Idx k),
      TM.clearRegTM (yIdx k)]
    I
    (fun j => if j = 0 then V0 else if j = 1 then V1 else if j = 2 then V2
      else if j = 3 then V3 else if j = 4 then V4 else if j = 5 then V5
      else if j = 6 then V6 else V7)
    (fun _ => []) (prologueBnd p q lx) hIp ?_ ?_).consequence ?_ ?_ (le_refl _)
  · intro j i
    split
    · exact hV0P i
    · split
      · exact hV1P i
      · split
        · exact hV2P i
        · split
          · exact hV3P i
          · split
            · exact hV4P i
            · split
              · exact hV5P i
              · split
                · exact hV6P i
                · exact hV7P i
  · intro j hj
    match j, hj with
    | 0, _ =>
      show (TM.inputLenRegTM (resIdx k)).HoareTime (TM.EmitPred I V0 []) _ _
      refine ((TM.inputLenRegTM_hoareTime (resIdx k) x V0 [] (fun i _ => hV0P i)
        hV0s).consequence (fun _ _ _ h => h) ?_ ?_)
      · rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, ?_, ho⟩
        rw [hw, ← hV1]
        norm_num
      · exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    | 1, _ =>
      show (TM.polyEvalTM (resIdx k) (nIdx k) (y1Idx k) p).HoareTime (TM.EmitPred I V1 []) _ _
      refine ((TM.polyEvalTM_hoareTime (resIdx k) (nIdx k) (y1Idx k) hsn hsy1 hny1 p
        (prologueCap p lx) lx 0 0 (le_prologueCap p lx) (Nat.zero_le _) (Nat.zero_le _)
        (fun j _ => TM.hornerFold_take_le lx (TM.polyCoeffs p) j)
        I V1 [] hIp hV1P hV1s hV1n hV1y1).consequence (fun _ _ _ h => h) ?_ ?_)
      · rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, ?_, ho⟩
        rw [hw, ← hV2]
        norm_num
      · exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    | 2, _ =>
      show (TM.incRegTM (nIdx k)).HoareTime (TM.EmitPred I V2 []) _ _
      refine ((TM.incRegTM_hoareTime (nIdx k) m I V2 [] hIp (fun i _ => hV2P i)
        hV2n).consequence (fun _ _ _ h => h) ?_ ?_)
      · rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, ?_, ho⟩
        rw [hw, ← hV3]
        norm_num
      · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
    | 3, _ =>
      show (TM.polyEvalTM (resIdx k) (regIdx k) (yIdx k) q).HoareTime (TM.EmitPred I V3 []) _ _
      refine ((TM.polyEvalTM_hoareTime (resIdx k) (regIdx k) (yIdx k) hsg hsy hgy q
        (prologueCap q lx) lx 0 0 (le_prologueCap q lx) (Nat.zero_le _) (Nat.zero_le _)
        (fun j _ => TM.hornerFold_take_le lx (TM.polyCoeffs q) j)
        I V3 [] hIp hV3P hV3s hV3g hV3y).consequence (fun _ _ _ h => h) ?_ ?_)
      · rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, ?_, ho⟩
        rw [hw, ← hV4]
        norm_num
      · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
    | 4, _ =>
      show (TM.clearRegTM (resIdx k)).HoareTime (TM.EmitPred I V4 []) _ _
      refine ((TM.clearRegTM_hoareTime (resIdx k) lx I V4 [] hIp (fun i _ => hV4P i)
        hV4s).consequence (fun _ _ _ h => h) ?_ ?_)
      · rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, ?_, ho⟩
        rw [hw, ← hV5]
        norm_num
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
    | 5, _ =>
      show (TM.clearRegTM (y1Idx k)).HoareTime (TM.EmitPred I V5 []) _ _
      refine ((TM.clearRegTM_hoareTime (y1Idx k) m I V5 [] hIp (fun i _ => hV5P i)
        hV5y1).consequence (fun _ _ _ h => h) ?_ ?_)
      · rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, ?_, ho⟩
        rw [hw, ← hV6]
        norm_num
      · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    | 6, _ =>
      show (TM.clearRegTM (yIdx k)).HoareTime (TM.EmitPred I V6 []) _ _
      refine ((TM.clearRegTM_hoareTime (yIdx k) Hq I V6 [] hIp (fun i _ => hV6P i)
        hV6y).consequence (fun _ _ _ h => h) ?_ ?_)
      · rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, ?_, ho⟩
        rw [hw, ← hV7]
        norm_num
      · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  · rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, hw, (outAcc_nil_iff out).mpr ho⟩
  · rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨hi, ?_, (outAcc_nil_iff out).mp ho⟩
    rw [hw]
    show V7 = enumBank k x (2 ^ (m + 1) - 1) Hq 0 0 0
    funext j
    by_cases hy : j = yIdx k
    · rw [hy, hV7, Function.update_self, regTape_zero', enumBank_y]
    · rw [hV7, Function.update_of_ne hy]
      by_cases hy1 : j = y1Idx k
      · rw [hy1, hV6, Function.update_self, regTape_zero', enumBank_y1]
      · rw [hV6, Function.update_of_ne hy1]
        by_cases hs : j = resIdx k
        · rw [hs, hV5, Function.update_self, regTape_zero',
            enumBank_blank k x (2 ^ (m + 1) - 1) Hq 0 0 0 _ (res_ne_regs k).1
              (res_ne_regs k).2.1 (res_ne_regs k).2.2
              (hne _ _ (by show 3 + k + 4 ≠ 0; omega))
              (hne _ _ (by show 3 + k + 4 ≠ 1; omega))
              (hne _ _ (by show 3 + k + 4 ≠ 3 + k + 3; omega))
              (hne _ _ (by show 3 + k + 4 ≠ 3 + k + 7; omega))]
        · rw [hV5, Function.update_of_ne hs]
          by_cases hg : j = regIdx k
          · rw [hg, hV4, Function.update_self,
              enumBank_of_ne k x (2 ^ (m + 1) - 1) Hq 0 0 0 _ (reg_ne_regs k).1
                (reg_ne_regs k).2.1 (reg_ne_regs k).2.2, enumRest,
              ite_eq_right (hne _ _ (by show 3 + k + 7 ≠ 0; omega)),
              ite_eq_right (hne _ _ (by show 3 + k + 7 ≠ 1; omega)),
              ite_eq_right (hne _ _ (by show 3 + k + 7 ≠ 3 + k + 3; omega)), ite_eq_left rfl]
          · rw [hV4, Function.update_of_ne hg, Function.update_of_ne hy]
            by_cases hn : j = nIdx k
            · rw [hn, hV3, Function.update_self, regTape_eq_natTape',
                enumBank_of_ne k x (2 ^ (m + 1) - 1) Hq 0 0 0 _ (n_ne_regs k).1
                  (n_ne_regs k).2.1 (n_ne_regs k).2.2, enumRest,
                ite_eq_right (hne _ _ (by show 3 + k + 3 ≠ 0; omega)),
                ite_eq_right (hne _ _ (by show 3 + k + 3 ≠ 1; omega)), ite_eq_left rfl]
            · rw [hV3, Function.update_of_ne hn, hV2, Function.update_of_ne hn,
                Function.update_of_ne hy1, hV1, Function.update_of_ne hs, hV0]
              by_cases hx : j = xIdx k
              · rw [hx, copiedBank, Function.update_self,
                  enumBank_x]
              · rw [copiedBank_of_ne k x j hx]
                by_cases hw' : j = wIdx k
                · rw [hw', enumBank_w]
                  rfl
                · by_cases hc : j = cIdx k
                  · rw [hc, enumBank_c]
                    exact natTape_zero_eq'.symm
                  · by_cases ha : j = aIdx k
                    · rw [ha, enumBank_a]
                      exact natTape_zero_eq'.symm
                    · by_cases hr : j = rIdx k
                      · rw [hr, enumBank_r]
                        exact natTape_zero_eq'.symm
                      · rw [enumBank_blank k x (2 ^ (m + 1) - 1) Hq 0 0 0 j hc ha hr hx hw' hn
                          hg]

end PolyExists

end Complexity

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PPLayout
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub
public import Complexitylib.Models.TuringMachine.Registers.InputLen
public import Complexitylib.Models.TuringMachine.Registers.Horner

/-!
# Assembling the counting loop's body

⚠️ Unreviewed by Bolton

The loop invariant names every tape: the counter and the two tallies carry their numbers, the
horizon and the wipe's register carry theirs, and everything else rests blank. This file records
what that bank looks like at each named index and proves the body's stages against it.

## Main results

- `NTM.bodyBank` — the bank the loop invariant pins, with its value at every named index
- `NTM.blankSlot_hoareTime` — the body's first stage: blank the verdict slot
- `NTM.publish_hoareTime` — the stage that copies the verdict into the output slot
- `NTM.simCfg_entry` — the simulation stage is entered on exactly the loop's own bank
- `NTM.afterSim`, `NTM.simTM_hoareTime` — the tape state the simulation stage leaves the body in
- `NTM.afterPark`, `NTM.parkStage_hoareTime` — the cleanup stage that follows it
- `NTM.afterPublish`, `NTM.publishStage_hoareTime` — the stage that publishes the verdict
- `NTM.afterBump`, `NTM.bumpStage_hoareTime` — the arithmetic stage
- `NTM.wipeStage_hoareTime` — the wipe, which returns the bank to the loop invariant's shape
- `NTM.afterSim_trans`, `NTM.afterPark_trans`, `NTM.afterPublish_trans`, `NTM.afterBump_trans` —
  the body's intermediate states survive a phase boundary
- `NTM.bodyTM`, `NTM.bodyTM_hoareTime`, `NTM.bodyTM_hoareTime_mid` — the loop's body, its
  contract, and that contract in the shape the loop rule asks for
- `NTM.tallyLoop_full`, `NTM.tallyLoop_full_bounded` — body and test together, running the tally
  to its horizon, with both running times written in terms of the horizon alone
- `NTM.tallyLoop_keepsWindow_bounded`, `NTM.tallyLoop_keepsWindowOn` — and the loop's space bound
  at the same layout, packaged for composition
- `NTM.prologueTM`, `NTM.prologueTM_hoareTime` — the machine's prologue and its contract
- `NTM.ppPark_hoareTime`, `NTM.ppMachine`, `NTM.ppMachine_hoareTime` — the parking step, the whole
  counting machine, and its contract
- `NTM.loopEpilogue_keepsWindowOn`, `NTM.prologueRest_keepsWindowOn`,
  `NTM.ppMachine_keepsWindow` — the parts composed in space, and the whole machine's window
- `NTM.lt_iff_succ_sub_eq_zero`, `NTM.epilogueTM` — the comparison the machine ends with
- `NTM.epiloguePreTM_hoareTime` — the epilogue's arithmetic
- `NTM.epilogueEq_hoareTime` — its comparison
- `NTM.afterEq`, `NTM.epiloguePostTM_hoareTime` — its publication
- `NTM.epilogueTM_hoareTime`, `NTM.epilogueTM_keepsWindowOn` — the three chained, in time and space
- `NTM.binaryEqTime_le_of_le`, `NTM.bodyTime_le` — the two running times are uniform over the loop
- `NTM.bodyTM_keepsWindowOn` — one pass of the body stays inside a window of its own width
- `NTM.bodyBank_eq_of` — the bridge from the wipe's result back to the loop invariant
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ}

/-- The bank the loop invariant pins at count `v` with tallies `a` and `r`. -/
def bodyBank (k N H v a r : ℕ) : Fin (bodyTapes k) → Tape :=
  tallyWork (cIdx k) (aIdx k) (rIdx k) (bodyRest k N H) (v, a, r)

theorem bodyBank_cIdx (k N H v a r : ℕ) : bodyBank k N H v a r (cIdx k) = natTape v := by
  simp only [bodyBank, tallyWork]
  simp

theorem bodyBank_aIdx (k N H v a r : ℕ) : bodyBank k N H v a r (aIdx k) = natTape a := by
  obtain ⟨hca, -⟩ := bodyIdx_distinct k
  simp only [bodyBank, tallyWork, ite_eq_right (Ne.symm hca)]
  simp

theorem bodyBank_rIdx (k N H v a r : ℕ) : bodyBank k N H v a r (rIdx k) = natTape r := by
  obtain ⟨-, hcr, har, -⟩ := bodyIdx_distinct k
  simp only [bodyBank, tallyWork, ite_eq_right (Ne.symm hcr), ite_eq_right (Ne.symm har)]
  simp

theorem bodyBank_rest (k N H v a r : ℕ) (j : Fin (bodyTapes k))
    (hc : j ≠ cIdx k) (ha : j ≠ aIdx k) (hr : j ≠ rIdx k) :
    bodyBank k N H v a r j = bodyRest k N H j := by
  simp only [bodyBank, tallyWork, ite_eq_right hc, ite_eq_right ha, ite_eq_right hr]

theorem bodyBank_parked (k N H v a r : ℕ) : ∀ j, TM.Parked (bodyBank k N H v a r j) := by
  intro j
  simp only [bodyBank, tallyWork]
  split
  · exact natTape_parked _
  · split
    · exact natTape_parked _
    · split
      · exact natTape_parked _
      · exact bodyRest_parked k N H j

theorem bodyBank_cells_zero (k N H v a r : ℕ) :
    ∀ j, (bodyBank k N H v a r j).cells 0 = Γ.start := by
  intro j
  simp only [bodyBank, tallyWork]
  split
  · exact natTape_cells_zero _
  · split
    · exact natTape_cells_zero _
    · split
      · exact natTape_cells_zero _
      · exact bodyRest_cells_zero k N H j

theorem bodyBank_startInvariant (k N H v a r : ℕ) :
    ∀ j, Tape.StartInvariant (bodyBank k N H v a r j) :=
  fun j => ⟨bodyBank_cells_zero k N H v a r j, fun i hi => (bodyBank_parked k N H v a r j).2 i hi⟩

/-- Every tape the body wipes rests blank in the loop's bank. -/
theorem bodyBank_wipeTarget (k N H v a r : ℕ) (j : Fin (bodyTapes k))
    (hj : j.val < k ∨ j = vIdx k) : bodyBank k N H v a r j = TM.blankTape := by
  have hval : j.val < k ∨ j.val = k + 7 := by
    rcases hj with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; rfl)
  have hne : ∀ i' : Fin (bodyTapes k), j.val ≠ i'.val → j ≠ i' :=
    fun i' h hh => h (congrArg Fin.val hh)
  rw [bodyBank_rest k N H v a r j
      (hne (cIdx k) (by simp only [cIdx]; omega))
      (hne (aIdx k) (by simp only [aIdx]; omega))
      (hne (rIdx k) (by simp only [rIdx]; omega)),
    bodyRest_other k N H j
      (hne (nIdx k) (by simp only [nIdx]; omega))
      (hne (regIdx k) (by simp only [regIdx]; omega))]

/-- The permanently blank register reads a blank, which is what makes it usable as the source of
a blanking write. -/
theorem bodyBank_zIdx_read (k N H v a r : ℕ) :
    (bodyBank k N H v a r (zIdx k)).read = Γ.blank := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hzc, hza, hzr, -⟩ := bodyIdx_distinct k
  have hzn : zIdx k ≠ nIdx k := by
    intro h; have := congrArg Fin.val h
    simp only [zIdx, nIdx] at this; omega
  have hzreg : zIdx k ≠ regIdx k := by
    intro h; have := congrArg Fin.val h
    simp only [zIdx, regIdx] at this; omega
  rw [bodyBank_rest k N H v a r _ hzc hza hzr, bodyRest_other k N H _ hzn hzreg]
  exact Tape.init_nil_move_right_read

/-- **The body's first stage: blank the verdict slot.** The loop returns to its start state with
the previous check's verdict still in the slot; the wipe that ends the body needs it blank, and so
does the simulation, whose real output tape must start blank. -/
theorem blankSlot_hoareTime (k N H v a r : ℕ) (I : Tape) (hI : TM.Parked I) :
    (TM.writeOutputBitTM (zIdx k)).HoareTime
      (fun inp work out => inp = I ∧ work = bodyBank k N H v a r ∧
        ∃ s : Γw, s ≠ Γw.one ∧ out = outSlot s)
      (fun inp work out => inp = I ∧ work = bodyBank k N H v a r ∧ out = outSlot Γw.blank)
      1 := by
  intro inp work out hpre
  obtain ⟨hi, hw, s, -, ho⟩ := hpre
  refine (TM.writeOutputBitTM_hoareTime_frame (zIdx k) I (bodyBank k N H v a r)
    (outSlot s) hI (bodyBank_parked k N H v a r) (outSlot_parked _)).strengthen_post
    (post' := fun inp work out => inp = I ∧ work = bodyBank k N H v a r ∧
      out = outSlot Γw.blank) ?_ inp work out ⟨hi, hw, ho⟩
  rintro inp' work' out' ⟨hi', hw', ho'⟩
  refine ⟨hi', hw', ?_⟩
  rw [ho', bodyBank_zIdx_read]
  show (outSlot s).write (TM.readBackWrite Γ.blank).toΓ = _
  exact outSlot_write s Γw.blank


/-- **The bridge back to the loop invariant.** After the body's wipe, a bank that carries the
right numbers on the named registers and rests blank elsewhere *is* the bank the loop invariant
pins at the next index. -/
theorem bodyBank_eq_of (k N H v a r : ℕ) (W : Fin (bodyTapes k) → Tape)
    (hc : W (cIdx k) = natTape v) (ha : W (aIdx k) = natTape a) (hr : W (rIdx k) = natTape r)
    (hn : W (nIdx k) = natTape N) (hreg : W (regIdx k) = TM.regTape H)
    (hrest : ∀ j, j ∉ wipeTargets k → j ≠ cIdx k → j ≠ aIdx k → j ≠ rIdx k → j ≠ nIdx k →
      j ≠ regIdx k → W j = TM.blankTape) :
    (fun j => if j ∈ wipeTargets k then TM.blankTape else W j) = bodyBank k N H v a r := by
  have hsim : ∀ j : Fin (bodyTapes k), j ∈ wipeTargets k →
      j ≠ cIdx k ∧ j ≠ aIdx k ∧ j ≠ rIdx k ∧ j ≠ nIdx k ∧ j ≠ regIdx k := by
    intro j hj
    rw [mem_wipeTargets_iff] at hj
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      · intro h
        have hval := congrArg Fin.val h
        simp only [cIdx, aIdx, rIdx, nIdx, regIdx] at hval
        rcases hj with hj | hj
        · omega
        · have := congrArg Fin.val hj
          simp only [vIdx] at this
          omega
  funext j
  by_cases hj : j ∈ wipeTargets k
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hsim j hj
    rw [ite_eq_left hj, bodyBank_rest k N H v a r j h1 h2 h3, bodyRest_other k N H j h4 h5]
  · rw [ite_eq_right hj]
    by_cases hjc : j = cIdx k
    · rw [hjc, hc, bodyBank_cIdx]
    by_cases hja : j = aIdx k
    · rw [hja, ha, bodyBank_aIdx]
    by_cases hjr : j = rIdx k
    · rw [hjr, hr, bodyBank_rIdx]
    by_cases hjn : j = nIdx k
    · have h1 : nIdx k ≠ cIdx k := by
        intro h; have := congrArg Fin.val h; simp only [nIdx, cIdx] at this; omega
      have h2 : nIdx k ≠ aIdx k := by
        intro h; have := congrArg Fin.val h; simp only [nIdx, aIdx] at this; omega
      have h3 : nIdx k ≠ rIdx k := by
        intro h; have := congrArg Fin.val h; simp only [nIdx, rIdx] at this; omega
      rw [hjn, hn, bodyBank_rest k N H v a r _ h1 h2 h3, bodyRest_nIdx]
    by_cases hjreg : j = regIdx k
    · have h1 : regIdx k ≠ cIdx k := by
        intro h; have := congrArg Fin.val h; simp only [regIdx, cIdx] at this; omega
      have h2 : regIdx k ≠ aIdx k := by
        intro h; have := congrArg Fin.val h; simp only [regIdx, aIdx] at this; omega
      have h3 : regIdx k ≠ rIdx k := by
        intro h; have := congrArg Fin.val h; simp only [regIdx, rIdx] at this; omega
      rw [hjreg, hreg, bodyBank_rest k N H v a r _ h1 h2 h3, bodyRest_regIdx]
    · rw [hrest j hj hjc hja hjr hjn hjreg,
        bodyBank_rest k N H v a r j hjc hja hjr, bodyRest_other k N H j hjn hjreg]


/-- **The stage's entry configuration is the loop's own bank.** Placing the simulation beside the
registers and redirecting its output puts exactly the tapes the loop invariant names where the
stage expects them: the machine's own tapes blank, the counter at `v`, the registers untouched,
and the verdict tape blank. -/
theorem simCfg_entry (tm : NTM k) (x : List Bool) (N H v a r : ℕ)
    (extras : Fin (0 + (k + 1) + 6) → Tape)
    (hex : ∀ j, extras j = bodyBank k N H v a r j.castSucc) :
    simCfg tm 6 extras (simEntry tm x v)
      = (⟨(simTM tm 6).qstart, (Tape.init (x.map Γ.ofBool)).move Dir3.right,
          bodyBank k N H v a r, TM.blankTape⟩ : Cfg (bodyTapes k) (simTM tm 6).Q) := by
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  refine Cfg.ext rfl rfl (funext fun j => ?_) rfl
  dsimp only
  by_cases hj : j.val < 0 + (k + 1) + 6
  · rw [show (simCfg tm 6 extras (simEntry tm x v)).work j
        = (TM.placeWorkCfg (simCore tm) 0 6 extras (simEntry tm x v)).work ⟨j.val, hj⟩ from
      TM.retargetCfg_work_lt _ _ j hj]
    by_cases hmid : j.val < 0 + (k + 1)
    · rw [show (⟨j.val, hj⟩ : Fin (0 + (k + 1) + 6))
          = TM.placeWorkIdx 0 6 (⟨j.val, by omega⟩ : Fin (k + 1)) from
        Fin.ext (by show j.val = 0 + j.val; omega), TM.placeWorkCfg_work_middle]
      show (if j.val < k then TM.blankTape else natTape v) = _
      by_cases hjk : j.val < k
      · rw [ite_eq_left hjk,
          bodyBank_rest k N H v a r j
            (hne j (cIdx k) (by simp only [cIdx]; omega))
            (hne j (aIdx k) (by simp only [aIdx]; omega))
            (hne j (rIdx k) (by simp only [rIdx]; omega)),
          bodyRest_other k N H j
            (hne j (nIdx k) (by simp only [nIdx]; omega))
            (hne j (regIdx k) (by simp only [regIdx]; omega))]
      · rw [ite_eq_right hjk, show j = cIdx k from Fin.ext (by show j.val = k; omega),
        bodyBank_cIdx]
    · rw [TM.placeWorkCfg_work_extra _ _ _ _ _ _ (fun hcon => hmid hcon.2), hex]
      congr 1
  · have hlast : j = vIdx k := Fin.ext (by
      have hlt := j.isLt
      show j.val = k + 7
      omega)
    rw [hlast, vIdx_eq_last,
      show (simCfg tm 6 extras (simEntry tm x v)).work (Fin.last (0 + (k + 1) + 6))
        = (TM.placeWorkCfg (simCore tm) 0 6 extras (simEntry tm x v)).output from
      TM.retargetCfg_work_last _ _, ← vIdx_eq_last]
    show TM.blankTape = _
    rw [bodyBank_rest k N H v a r (vIdx k)
        (hne _ (cIdx k) (by simp only [vIdx, cIdx]; omega))
        (hne _ (aIdx k) (by simp only [vIdx, aIdx]; omega))
        (hne _ (rIdx k) (by simp only [vIdx, rIdx]; omega)),
      bodyRest_other k N H (vIdx k)
        (hne _ (nIdx k) (by simp only [vIdx, nIdx]; omega))
        (hne _ (regIdx k) (by simp only [vIdx, regIdx]; omega))]


/-- Every tape of the loop's bank is parked at cell one. -/
theorem bodyBank_head (k N H v a r : ℕ) : ∀ j, (bodyBank k N H v a r j).head = 1 := by
  intro j
  simp only [bodyBank, tallyWork]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · simp only [bodyRest]
        split
        · rfl
        · split
          · rfl
          · rfl

/-- The real input tape, parked at cell one, with `x` on it. -/
def bodyInput (x : List Bool) : Tape := (Tape.init (x.map Γ.ofBool)).move Dir3.right

theorem bodyInput_startInvariant (x : List Bool) : Tape.StartInvariant (bodyInput x) := by
  refine ⟨?_, fun j hj => ?_⟩
  · show ((Tape.init (x.map Γ.ofBool)).move Dir3.right).cells 0 = Γ.start
    rw [Tape.move_cells]
    exact Tape.init_cells_zero _
  · show ((Tape.init (x.map Γ.ofBool)).move Dir3.right).cells j ≠ Γ.start
    rw [Tape.move_cells]
    exact Tape.init_ofBool_cells_ne_start x j hj

@[simp] theorem bodyInput_head (x : List Bool) : (bodyInput x).head = 1 := rfl

theorem bodyInput_parked (x : List Bool) : TM.Parked (bodyInput x) :=
  ⟨le_refl 1, fun j hj => (bodyInput_startInvariant x).2 j hj⟩

/-- **The tape state the simulation stage leaves the body in.** Nothing is pinned but the
registers: the simulated machine's tapes and the verdict tape hold whatever the run put there,
and the heads are only bounded. What survives is enough — the counter's digits, the registers,
the verdict bit, and a blank real output. -/
def afterSim (k N H v a r T : ℕ) (I : Tape) (b : Bool) : TM.TapePred (bodyTapes k) :=
  fun inp work out =>
    Tape.StartInvariant inp ∧ inp.cells = I.cells ∧ inp.head ≤ 1 + T ∧
    (∀ j, Tape.StartInvariant (work j)) ∧ (∀ j, (work j).head ≤ 1 + T) ∧
    (work (cIdx k)).cells = (natTape v).cells ∧
    (∀ j : Fin (bodyTapes k), ¬ (j.val < k) → j ≠ cIdx k → j ≠ vIdx k →
      work j = bodyBank k N H v a r j) ∧
    (∀ j : Fin (bodyTapes k), (j.val < k ∨ j = vIdx k) →
      ∀ i, 1 + T < i → (work j).cells i = Γ.blank) ∧
    decide ((work (vIdx k)).cells 1 = Γ.one) = b ∧
    out = TM.blankTape


/-- **The simulation stage's contract.** From the loop's bank with a blank output slot, the
stage halts within the horizon and leaves the body in `NTM.afterSim`, carrying the acceptance bit
of path `v`. -/
theorem simTM_hoareTime (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T v : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (N H a r : ℕ) :
    (simTM tm 6).HoareTime
      (fun inp work out => inp = bodyInput x ∧ work = bodyBank k N H v a r ∧
        out = TM.blankTape)
      (afterSim k N H v a r T (bodyInput x) (acceptsAt tm x T v))
      T := by
  intro inp work out hpre
  obtain ⟨hi, hw, ho⟩ := hpre
  have hentry := simCfg_entry tm x N H v a r (fun j => bodyBank k N H v a r j.castSucc)
    (fun _ => rfl)
  obtain ⟨c', t, hle, hcore, hreach, hhalt, hverdict⟩ :=
    simTM_run tm x hne hall T v hT hfT 6 (fun j => bodyBank k N H v a r j.castSucc)
      (fun i _ => bodyBank_startInvariant k N H v a r _)
      (fun i _ => le_of_eq (bodyBank_head k N H v a r _).symm)
      (simEntry tm x v) (simEntry_dropChoice tm x v) (simEntry_counter_hasBinaryNat tm x v)
  obtain ⟨hInvI', hInvW', hcellsI', hheadI', hheadW'⟩ :=
    simTM_frame tm 6 (fun j => bodyBank k N H v a r j.castSucc) hreach
      (by rw [hentry]; exact bodyInput_startInvariant x)
      (by rw [hentry]; exact fun j => bodyBank_startInvariant k N H v a r j)
      (by rw [hentry]; exact TM.blankTape_startInvariant)
      (by rw [hentry]; exact le_of_eq rfl)
      (by rw [hentry]; exact fun j => le_of_eq (bodyBank_head k N H v a r j))
  have hstart : (⟨(simTM tm 6).qstart, inp, work, out⟩ : Cfg (bodyTapes k) (simTM tm 6).Q)
      = simCfg tm 6 (fun j => bodyBank k N H v a r j.castSucc) (simEntry tm x v) := by
    rw [hentry, hi, hw, ho]
    rfl
  refine ⟨simCfg tm 6 (fun j => bodyBank k N H v a r j.castSucc) c', t, hle,
    by rw [hstart]; exact hreach, hhalt, ?_⟩
  refine ⟨hInvI', ?_, ?_, hInvW', ?_, ?_, ?_, ?_, ?_, simTM_output tm 6 _ c'⟩
  · rw [hcellsI', hentry]
    rfl
  · exact le_trans hheadI' (by omega)
  · exact fun j => le_trans (hheadW' j) (by omega)
  · have hciv : ((simEntry tm x v).work (Fin.last k)).StartInvariant := by
      rw [simEntry_counter]
      exact hasBinaryNat_startInvariant (Tape.init_move_right_hasBinaryNat v)
    have hcih : 1 ≤ ((simEntry tm x v).work (Fin.last k)).head := by
      rw [simEntry_counter]
      exact le_of_eq rfl
    rw [simCfg_counter_cells tm 6 (fun j => bodyBank k N H v a r j.castSucc) hcore hciv hcih
      (cIdx k) rfl, hentry]
    show (bodyBank k N H v a r (cIdx k)).cells = _
    rw [bodyBank_cIdx]
  · intro j h1 h2 h3
    have hne7 : j.val ≠ k + 7 := fun hc => h3 (Fin.ext (by rw [hc]; rfl))
    have hnek : j.val ≠ k := fun hc => h2 (Fin.ext (by rw [hc]; rfl))
    have hjlt : j.val < 0 + (k + 1) + 6 + 1 := j.isLt
    have hlt : j.val < 0 + (k + 1) + 6 := by omega
    have hmid : ¬ (j.val < 0 + (k + 1)) := by omega
    rw [simCfg_work_extra tm 6 (fun j => bodyBank k N H v a r j.castSucc) c' j hmid hlt]
    congr 1
  · intro j hj i hi
    have hhead1 : ((simCfg tm 6 (fun j => bodyBank k N H v a r j.castSucc)
        (simEntry tm x v)).work j).head = 1 := by
      rw [hentry]
      exact bodyBank_head k N H v a r j
    rw [TM.reachesIn_work_cells_far hreach j i (by rw [hhead1]; omega), hentry]
    show (bodyBank k N H v a r j).cells i = Γ.blank
    rw [bodyBank_wipeTarget k N H v a r j hj]
    show ((Tape.init ([] : List Γ)).move Dir3.right).cells i = Γ.blank
    rw [Tape.move_cells, show i = (i - 1) + 1 from by omega, Tape.init_nil_cells_succ]
  · rw [← hverdict, vIdx_eq_last]


/-- **The tape state after the body's cleanup.** Every head is parked, the counter has been
rewound and reads as `v` again, and the verdict tape is at cell one so its bit can be published.
The simulated machine's own tapes still hold whatever the run left; the wipe deals with them. -/
def afterPark (k N H v a r T : ℕ) (I : Tape) (b : Bool) : TM.TapePred (bodyTapes k) :=
  fun inp work out =>
    inp = I ∧
    (∀ j, Tape.StartInvariant (work j)) ∧ (∀ j, TM.Parked (work j)) ∧
    (∀ j, (work j).head ≤ 1 + T) ∧
    work (cIdx k) = natTape v ∧
    (work (vIdx k)).head = 1 ∧ decide ((work (vIdx k)).cells 1 = Γ.one) = b ∧
    (∀ j : Fin (bodyTapes k), ¬ (j.val < k) → j ≠ cIdx k → j ≠ vIdx k →
      work j = bodyBank k N H v a r j) ∧
    (∀ j : Fin (bodyTapes k), (j.val < k ∨ j = vIdx k) →
      ∀ i, 1 + T < i → (work j).cells i = Γ.blank) ∧
    out = TM.blankTape

/-- **The body's cleanup stage.** It asks only for start-invariance, which is all a halted
simulation guarantees, and returns the counter and the verdict tape at cell one. -/
theorem parkStage_hoareTime (k N H v a r T : ℕ) (I : Tape) (b : Bool)
    (hIhead : I.head = 1) (hcne : cIdx k ≠ vIdx k) :
    (TM.parkRewindTM [cIdx k, vIdx k]).HoareTime
      (afterSim k N H v a r T I b)
      (afterPark k N H v a r T I b)
      (1 + 1 + (2 * (max (1 + T + 2) (2 * (1 + T + 3) + 1) + 1) + 1)) := by
  intro inp work out hpre
  obtain ⟨hInvI, hcellsI, hheadI, hInvW, hheadW, hcnt, hreg, hfar, hverdict, hout⟩ := hpre
  have hnodup : ([cIdx k, vIdx k] : List (Fin (bodyTapes k))).Nodup := by
    simp [hcne]
  have hOinv : Tape.StartInvariant out := by rw [hout]; exact TM.blankTape_startInvariant
  refine ((TM.parkRewindTM_hoareTime [cIdx k, vIdx k] hnodup (1 + T) (by omega) inp work out
    hInvI hInvW hOinv hheadI (fun j _ => hheadW j)).strengthen_post ?_) inp work out
    ⟨rfl, rfl, rfl⟩
  rintro inp' work' out' ⟨hi', hw', ho'⟩
  have hw'' : ∀ j, work' j = if j ∈ [cIdx k, vIdx k] then (⟨1, (work j).cells⟩ : Tape)
      else TM.parkTape (work j) := fun j => by rw [hw']
  have hIeq : (⟨1, inp.cells⟩ : Tape) = I := Tape.ext (by rw [hIhead]) hcellsI
  have hcells : ∀ j, (work' j).cells = (work j).cells := by
    intro j
    rw [hw'' j]
    split <;> rfl
  have hInvW' : ∀ j, Tape.StartInvariant (work' j) := fun j =>
    ⟨by rw [hcells j]; exact (hInvW j).1, fun i hi => by rw [hcells j]; exact (hInvW j).2 i hi⟩
  have hpark : ∀ j, TM.Parked (work' j) := by
    intro j
    refine ⟨?_, fun i hi => (hInvW' j).2 i hi⟩
    rw [hw'' j]
    split
    · exact le_refl 1
    · exact le_max_right _ _
  refine ⟨hIeq ▸ hi', hInvW', hpark, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hw'' j]
    split
    · show (1 : ℕ) ≤ 1 + T
      omega
    · show max (work j).head 1 ≤ 1 + T
      have := hheadW j
      omega
  · rw [hw'' (cIdx k), ite_eq_left (by simp)]
    exact Tape.ext (by rw [(show (natTape v).head = 1 from rfl)]) hcnt
  · rw [hw'' (vIdx k), ite_eq_left (by simp)]
  · rw [hw'' (vIdx k), ite_eq_left (by simp)]
    exact hverdict
  · intro j h1 h2 h3
    rw [hw'' j, ite_eq_right (by simp [h2, h3]), hreg j h1 h2 h3]
    refine Tape.ext ?_ rfl
    show max (bodyBank k N H v a r j).head 1 = (bodyBank k N H v a r j).head
    rw [bodyBank_head]
    omega
  · intro j hj i hi
    rw [hcells j]
    exact hfar j hj i hi
  · rw [ho', hout]
    exact Tape.ext rfl rfl


/-- **The tape state once the verdict is published.** The slot now holds a symbol that is `1`
exactly when the path accepted, which is what `TM.ifTM` branches on. -/
def afterPublish (k N H v a r T : ℕ) (I : Tape) (b : Bool) : TM.TapePred (bodyTapes k) :=
  fun inp work out =>
    inp = I ∧
    (∀ j, Tape.StartInvariant (work j)) ∧ (∀ j, TM.Parked (work j)) ∧
    (∀ j, (work j).head ≤ 1 + T) ∧
    work (cIdx k) = natTape v ∧
    (∀ j : Fin (bodyTapes k), ¬ (j.val < k) → j ≠ cIdx k → j ≠ vIdx k →
      work j = bodyBank k N H v a r j) ∧
    (∀ j : Fin (bodyTapes k), (j.val < k ∨ j = vIdx k) →
      ∀ i, 1 + T < i → (work j).cells i = Γ.blank) ∧
    ∃ s : Γw, (s = Γw.one ↔ b = true) ∧ out = outSlot s

/-- **The body's publishing stage.** One transition copies the verdict tape's cell into the
output slot; nothing else on any tape moves. -/
theorem publishStage_hoareTime (k N H v a r T : ℕ) (I : Tape) (b : Bool) (hI : TM.Parked I) :
    (TM.writeOutputBitTM (vIdx k)).HoareTime
      (afterPark k N H v a r T I b)
      (afterPublish k N H v a r T I b)
      1 := by
  intro inp work out hpre
  obtain ⟨hi, hInvW, hpark, hheadW, hcnt, hvhead, hverdict, hreg, hfar, hout⟩ := hpre
  have hIp : TM.Parked inp := by rw [hi]; exact hI
  obtain ⟨c', t, hle, hreach, hhalt, hi', hw', ho'⟩ :=
    publish_hoareTime (vIdx k) inp work hIp hpark hvhead inp work out ⟨rfl, rfl, hout⟩
  refine ⟨c', t, hle, hreach, hhalt, ?_⟩
  refine ⟨by rw [hi']; exact hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hw']; exact hInvW j
  · intro j; rw [hw']; exact hpark j
  · intro j; rw [hw']; exact hheadW j
  · rw [hw']; exact hcnt
  · intro j h1 h2 h3; rw [hw']; exact hreg j h1 h2 h3
  · intro j hj i hi2; rw [hw']; exact hfar j hj i hi2
  · refine ⟨TM.readBackWrite ((work (vIdx k)).cells 1), ?_, ho'⟩
    rw [readBackWrite_eq_one_iff, ← hverdict]
    exact decide_eq_true_iff.symm


/-- **The tape state after the tallies are bumped.** The count has advanced, the chosen tally has
grown by one, and the verdict slot is blank again — ready for the wipe, which needs it so. -/
def afterBump (k N H v a r T : ℕ) (I : Tape) (b : Bool) : TM.TapePred (bodyTapes k) :=
  fun inp work out =>
    inp = I ∧
    (∀ j, Tape.StartInvariant (work j)) ∧ (∀ j, TM.Parked (work j)) ∧
    (∀ j, (work j).head ≤ 1 + T) ∧
    work (cIdx k) = natTape (v + 1) ∧
    work (aIdx k) = natTape (a + if b then 1 else 0) ∧
    work (rIdx k) = natTape (r + if b then 0 else 1) ∧
    (∀ j : Fin (bodyTapes k), ¬ (j.val < k) → j ≠ cIdx k → j ≠ aIdx k → j ≠ rIdx k →
      j ≠ vIdx k → work j = bodyBank k N H v a r j) ∧
    (∀ j : Fin (bodyTapes k), (j.val < k ∨ j = vIdx k) →
      ∀ i, 1 + T < i → (work j).cells i = Γ.blank) ∧
    out = outSlot Γw.blank

/-- **The body's arithmetic stage.** The verdict in the slot picks which tally grows; the count
grows too, and the slot is blanked on the way out. -/
theorem bumpStage_hoareTime (k N H v a r T : ℕ) (I : Tape) (b : Bool)
    (hI : TM.Parked I) (hIz : I.cells 0 = Γ.start) (hT : 1 ≤ T) :
    (TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k)).HoareTime
      (afterPublish k N H v a r T I b)
      (afterBump k N H v a r T I b)
      (3 * (max (1 + 1 + max (TM.binarySuccTime a) (TM.binarySuccTime r) + 5)
        (TM.binarySuccTime v) + 1) + 1) := by
  intro inp work out hpre
  obtain ⟨hi, hInvW, hpark, hheadW, hcnt, hreg, hfar, s, hb, hout⟩ := hpre
  obtain ⟨hca, hcr, har, hnc, hna, hnr, hsc, hsa, hsr, hsn, hzc, hza, hzr, -⟩ :=
    bodyIdx_distinct k
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  have hav : work (aIdx k) = natTape a := by
    rw [hreg (aIdx k) (by simp only [aIdx]; omega) (Ne.symm hca)
      (hne _ _ (by simp only [aIdx, vIdx]; omega)), bodyBank_aIdx]
  have hrv : work (rIdx k) = natTape r := by
    rw [hreg (rIdx k) (by simp only [rIdx]; omega) (Ne.symm hcr)
      (hne _ _ (by simp only [rIdx, vIdx]; omega)), bodyBank_rIdx]
  have hzread : (work (zIdx k)).read = Γ.blank := by
    rw [hreg (zIdx k) (by simp only [zIdx]; omega) hzc
      (hne _ _ (by simp only [zIdx, vIdx]; omega))]
    exact bodyBank_zIdx_read k N H v a r
  have hIp : TM.Parked inp := by rw [hi]; exact hI
  have hIz' : inp.cells 0 = Γ.start := by rw [hi]; exact hIz
  obtain ⟨c', t, hle, hreach, hhalt, hi', hw', ho'⟩ :=
    TM.tallyBumpTM_hoareTime (cIdx k) (aIdx k) (rIdx k) (zIdx k) hca hcr hzc hza hzr
      v a r b s hb inp work hIp hIz' hpark (fun j => (hInvW j).1) hcnt hav hrv hzread
      inp work out ⟨rfl, rfl, hout⟩
  refine ⟨c', t, hle, hreach, hhalt, ?_⟩
  have hwj : ∀ j : Fin (bodyTapes k), j ≠ cIdx k → j ≠ aIdx k → j ≠ rIdx k →
      c'.work j = work j := by
    intro j h1 h2 h3
    rw [hw', Function.update_of_ne h1]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Function.update_of_ne h3]
    · simp only [ite_true]
      rw [Function.update_of_ne h2]
  have hwc : c'.work (cIdx k) = natTape (v + 1) := by rw [hw', Function.update_self]
  have hwa : c'.work (aIdx k) = natTape (a + if b then 1 else 0) := by
    rw [hw', Function.update_of_ne (Ne.symm hca)]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Function.update_of_ne har, hav]
      rfl
    · simp only [ite_true]
      rw [Function.update_self]
  have hwr : c'.work (rIdx k) = natTape (r + if b then 0 else 1) := by
    rw [hw', Function.update_of_ne (Ne.symm hcr)]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [Function.update_self]
    · simp only [ite_true]
      rw [Function.update_of_ne (Ne.symm har), hrv]
      rfl
  have hInv' : ∀ j, Tape.StartInvariant (c'.work j) := by
    intro j
    by_cases h1 : j = cIdx k
    · rw [h1, hwc]; exact hasBinaryNat_startInvariant (Tape.init_move_right_hasBinaryNat _)
    by_cases h2 : j = aIdx k
    · rw [h2, hwa]; exact hasBinaryNat_startInvariant (Tape.init_move_right_hasBinaryNat _)
    by_cases h3 : j = rIdx k
    · rw [h3, hwr]; exact hasBinaryNat_startInvariant (Tape.init_move_right_hasBinaryNat _)
    · rw [hwj j h1 h2 h3]; exact hInvW j
  refine ⟨by rw [hi']; exact hi, hInv', fun j => ⟨?_, fun i hi2 => (hInv' j).2 i hi2⟩, ?_,
    hwc, hwa, hwr, ?_, ?_, by rw [ho']⟩
  · by_cases h1 : j = cIdx k
    · rw [h1, hwc]; exact le_of_eq rfl
    by_cases h2 : j = aIdx k
    · rw [h2, hwa]; exact le_of_eq rfl
    by_cases h3 : j = rIdx k
    · rw [h3, hwr]; exact le_of_eq rfl
    · rw [hwj j h1 h2 h3]; exact (hpark j).1
  · intro j
    by_cases h1 : j = cIdx k
    · rw [h1, hwc]; show (1 : ℕ) ≤ 1 + T; omega
    by_cases h2 : j = aIdx k
    · rw [h2, hwa]; show (1 : ℕ) ≤ 1 + T; omega
    by_cases h3 : j = rIdx k
    · rw [h3, hwr]; show (1 : ℕ) ≤ 1 + T; omega
    · rw [hwj j h1 h2 h3]; exact hheadW j
  · intro j h1 h2 h3 h4 h5
    rw [hwj j h2 h3 h4]
    exact hreg j h1 h2 h5
  · intro j hj i hi2
    have h1 : j ≠ cIdx k := by
      rcases hj with h | h
      · exact hne _ _ (by simp only [cIdx]; omega)
      · rw [h]; exact hne _ _ (by simp only [vIdx, cIdx]; omega)
    have h2 : j ≠ aIdx k := by
      rcases hj with h | h
      · exact hne _ _ (by simp only [aIdx]; omega)
      · rw [h]; exact hne _ _ (by simp only [vIdx, aIdx]; omega)
    have h3 : j ≠ rIdx k := by
      rcases hj with h | h
      · exact hne _ _ (by simp only [rIdx]; omega)
      · rw [h]; exact hne _ _ (by simp only [vIdx, rIdx]; omega)
    rw [hwj j h1 h2 h3]
    exact hfar j hj i hi2


/-- **The body's last stage.** Blanking the simulated machine's tapes and the verdict tape
returns the bank to exactly the shape the loop invariant names — at the next index, with the
tallies advanced. This is where the body closes. -/
theorem wipeStage_hoareTime (k N T v a r : ℕ) (I : Tape) (b : Bool)
    (hIsi : Tape.StartInvariant I) (hIp : TM.Parked I) :
    (TM.wipeRewindTM (wipeTargets k) (regIdx k)).HoareTime
      (afterBump k N (1 + T) v a r T I b)
      (fun inp work out => inp = I ∧
        work = bodyBank k N (1 + T) (v + 1) (a + if b then 1 else 0)
          (r + if b then 0 else 1) ∧
        out = outSlot Γw.blank)
      ((wipeTargets k).length * ((1 + T) + 4) + (1 + T) * 4 + 8 + 1 +
        ((wipeTargets k).length * ((1 + T) + 4) + 1)) := by
  intro inp work out hpre
  obtain ⟨hi, hInvW, hpark, hheadW, hwc, hwa, hwr, hreg, hfar, hout⟩ := hpre
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  have hregNotTarget := regIdx_not_mem_wipeTargets k
  have hregC : regIdx k ≠ cIdx k := hne _ _ (by simp only [regIdx, cIdx]; omega)
  have hregA : regIdx k ≠ aIdx k := hne _ _ (by simp only [regIdx, aIdx]; omega)
  have hregR : regIdx k ≠ rIdx k := hne _ _ (by simp only [regIdx, rIdx]; omega)
  have hregV : regIdx k ≠ vIdx k := hne _ _ (by simp only [regIdx, vIdx]; omega)
  have hnC : nIdx k ≠ cIdx k := hne _ _ (by simp only [nIdx, cIdx]; omega)
  have hnA : nIdx k ≠ aIdx k := hne _ _ (by simp only [nIdx, aIdx]; omega)
  have hnR : nIdx k ≠ rIdx k := hne _ _ (by simp only [nIdx, rIdx]; omega)
  have hnV : nIdx k ≠ vIdx k := hne _ _ (by simp only [nIdx, vIdx]; omega)
  have hwreg : work (regIdx k) = TM.regTape (1 + T) := by
    rw [hreg (regIdx k) (by simp only [regIdx]; omega) hregC hregA hregR hregV,
      bodyBank_rest k N (1 + T) v a r (regIdx k) hregC hregA hregR, bodyRest_regIdx]
  have hwn : work (nIdx k) = natTape N := by
    rw [hreg (nIdx k) (by simp only [nIdx]; omega) hnC hnA hnR hnV,
      bodyBank_rest k N (1 + T) v a r (nIdx k) hnC hnA hnR, bodyRest_nIdx]
  have hout' : out = TM.blankTape := by rw [hout, outSlot_blank_eq_blankTape]
  obtain ⟨c', t, hle, hreach, hhalt, hi', hw', ho'⟩ :=
    TM.wipeRewindTM_hoareTime (wipeTargets k) (wipeTargets_nodup k) (regIdx k) hregNotTarget
      (1 + T) inp work out (by rw [hi]; exact hIsi) (by rw [hi]; exact hIp) hout'
      (fun j _ => hInvW j)
      (fun j _ => hheadW j)
      (fun j hj i hi2 => hfar j (by rwa [mem_wipeTargets_iff] at hj) i hi2)
      hwreg (fun j hjr _ => hpark j)
      inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, hle, hreach, hhalt, by rw [hi']; exact hi, ?_, by rw [ho']; exact hout⟩
  rw [hw']
  refine bodyBank_eq_of k N (1 + T) (v + 1) (a + if b then 1 else 0) (r + if b then 0 else 1)
    work hwc hwa hwr hwn hwreg ?_
  intro j hj h1 h2 h3 h4 h5
  rw [mem_wipeTargets_iff] at hj
  have hjk : ¬ (j.val < k) := fun hc => hj (Or.inl hc)
  have hjv : j ≠ vIdx k := fun hc => hj (Or.inr hc)
  rw [hreg j hjk h1 h2 h3 hjv, bodyBank_rest k N (1 + T) v a r j h1 h2 h3,
    bodyRest_other k N (1 + T) j h4 h5]


/-- **The post-simulation state survives a phase boundary.** It is stated in terms of cells and
head *bounds* rather than exact tapes, which is what makes it stable: a transition preserves every
cell and never pushes a head outward. A predicate that pinned the tapes could not survive here,
because a halted simulation may leave a head on the marker, which the boundary then moves. -/
theorem afterSim_trans (k N H v a r T : ℕ) (I : Tape) (b : Bool)
    (inp : Tape) (work : Fin (bodyTapes k) → Tape) (out : Tape)
    (h : afterSim k N H v a r T I b inp work out) :
    afterSim k N H v a r T I b (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨hInvI, hcellsI, hheadI, hInvW, hheadW, hcnt, hreg, hfar, hverdict, hout⟩ := h
  have hcells : ∀ j, (TM.transitionTape (work j)).cells = (work j).cells :=
    fun j => TM.transitionTape_cells _ (fun i hi => (hInvW j).2 i hi)
  refine ⟨TM.startInvariant_transitionInput hInvI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [TM.transitionInput_cells]; exact hcellsI
  · exact le_trans (TM.head_transitionInput_le_max hInvI) (by omega)
  · exact fun j => TM.startInvariant_transitionTape (hInvW j)
  · intro j
    exact le_trans (TM.head_transitionTape_le_max (hInvW j)) (by have := hheadW j; omega)
  · show (TM.transitionTape (work (cIdx k))).cells = _
    rw [hcells]; exact hcnt
  · intro j h1 h2 h3
    show TM.transitionTape (work j) = _
    rw [hreg j h1 h2 h3]
    exact TM.transitionTape_eq_self (bodyBank_parked k N H v a r j).read_ne_start
  · intro j hj i hi
    show (TM.transitionTape (work j)).cells i = _
    rw [hcells]; exact hfar j hj i hi
  · show decide ((TM.transitionTape (work (vIdx k))).cells 1 = Γ.one) = b
    rw [hcells]; exact hverdict
  · rw [hout]
    exact TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start


/-- The pinned states between the body's later stages survive a phase boundary too, and for the
easy reason: every tape they name is parked, so the boundary is the identity. -/
theorem afterPark_trans (k N H v a r T : ℕ) (I : Tape) (b : Bool) (hI : TM.Parked I)
    (inp : Tape) (work : Fin (bodyTapes k) → Tape) (out : Tape)
    (h : afterPark k N H v a r T I b inp work out) :
    afterPark k N H v a r T I b (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨hi, hInvW, hpark, hheadW, hcnt, hvhead, hverdict, hreg, hfar, hout⟩ := h
  have hid : ∀ j, TM.transitionTape (work j) = work j :=
    fun j => TM.transitionTape_eq_self (hpark j).read_ne_start
  have hidI : TM.transitionInput inp = inp := by
    rw [hi]; exact TM.transitionInput_eq_self hI.read_ne_start
  have hidO : TM.transitionTape out = out := by
    rw [hout]; exact TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start
  rw [hidI, hidO, show (fun i => TM.transitionTape (work i)) = work from funext hid]
  exact ⟨hi, hInvW, hpark, hheadW, hcnt, hvhead, hverdict, hreg, hfar, hout⟩

/-- The same, once the verdict is in the slot. -/
theorem afterPublish_trans (k N H v a r T : ℕ) (I : Tape) (b : Bool) (hI : TM.Parked I)
    (inp : Tape) (work : Fin (bodyTapes k) → Tape) (out : Tape)
    (h : afterPublish k N H v a r T I b inp work out) :
    afterPublish k N H v a r T I b (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨hi, hInvW, hpark, hheadW, hcnt, hreg, hfar, s, hb, hout⟩ := h
  have hid : ∀ j, TM.transitionTape (work j) = work j :=
    fun j => TM.transitionTape_eq_self (hpark j).read_ne_start
  have hidI : TM.transitionInput inp = inp := by
    rw [hi]; exact TM.transitionInput_eq_self hI.read_ne_start
  have hidO : TM.transitionTape out = out := by
    rw [hout]; exact TM.transitionTape_eq_self (outSlot_parked s).read_ne_start
  rw [hidI, hidO, show (fun i => TM.transitionTape (work i)) = work from funext hid]
  exact ⟨hi, hInvW, hpark, hheadW, hcnt, hreg, hfar, s, hb, hout⟩

/-- The same, once the tallies have been bumped. -/
theorem afterBump_trans (k N H v a r T : ℕ) (I : Tape) (b : Bool) (hI : TM.Parked I)
    (inp : Tape) (work : Fin (bodyTapes k) → Tape) (out : Tape)
    (h : afterBump k N H v a r T I b inp work out) :
    afterBump k N H v a r T I b (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  obtain ⟨hi, hInvW, hpark, hheadW, hwc, hwa, hwr, hreg, hfar, hout⟩ := h
  have hid : ∀ j, TM.transitionTape (work j) = work j :=
    fun j => TM.transitionTape_eq_self (hpark j).read_ne_start
  have hidI : TM.transitionInput inp = inp := by
    rw [hi]; exact TM.transitionInput_eq_self hI.read_ne_start
  have hidO : TM.transitionTape out = out := by
    rw [hout]; exact TM.transitionTape_eq_self (outSlot_parked Γw.blank).read_ne_start
  rw [hidI, hidO, show (fun i => TM.transitionTape (work i)) = work from funext hid]
  exact ⟨hi, hInvW, hpark, hheadW, hwc, hwa, hwr, hreg, hfar, hout⟩


/-- **The counting loop's body.** Blank the verdict slot, simulate one path, put the heads back,
publish the verdict, bump the tallies and the count, and wipe the scratch tapes. -/
def bodyTM (tm : NTM k) : TM (bodyTapes k) :=
  TM.seqTM (TM.writeOutputBitTM (zIdx k))
    (TM.seqTM (simTM tm 6)
      (TM.seqTM (TM.parkRewindTM [cIdx k, vIdx k])
        (TM.seqTM (TM.writeOutputBitTM (vIdx k))
          (TM.seqTM (TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k))
            (TM.wipeRewindTM (wipeTargets k) (regIdx k))))))

/-- The body's running time: the six stages plus the five transitions between them. -/
def bodyTime (k T v a r : ℕ) : ℕ :=
  1 + 1 + (T + 1 +
    ((1 + 1 + (2 * (max (1 + T + 2) (2 * (1 + T + 3) + 1) + 1) + 1)) + 1 +
      (1 + 1 +
        ((3 * (max (1 + 1 + max (TM.binarySuccTime a) (TM.binarySuccTime r) + 5)
          (TM.binarySuccTime v) + 1) + 1) + 1 +
          ((wipeTargets k).length * ((1 + T) + 4) + (1 + T) * 4 + 8 + 1 +
            ((wipeTargets k).length * ((1 + T) + 4) + 1))))))

/-- **The body's contract.** One pass advances the count by one and the accepting or rejecting
tally by one, according to whether the path selected by the counter accepts. -/
theorem bodyTM_hoareTime (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T v : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (N a r : ℕ) :
    (bodyTM tm).HoareTime
      (fun inp work out => inp = bodyInput x ∧ work = bodyBank k N (1 + T) v a r ∧
        ∃ s : Γw, s ≠ Γw.one ∧ out = outSlot s)
      (fun inp work out => inp = bodyInput x ∧
        work = bodyBank k N (1 + T) (v + 1)
          (a + if acceptsAt tm x T v then 1 else 0)
          (r + if acceptsAt tm x T v then 0 else 1) ∧
        out = outSlot Γw.blank)
      (bodyTime k T v a r) := by
  set b := acceptsAt tm x T v with hb
  set I := bodyInput x with hIdef
  have hIp : TM.Parked I := bodyInput_parked x
  have hIsi : Tape.StartInvariant I := bodyInput_startInvariant x
  have hIz : I.cells 0 = Γ.start := hIsi.1
  have hcne : cIdx k ≠ vIdx k := fun h => by
    have := congrArg Fin.val h
    simp only [cIdx, vIdx] at this
    omega
  -- Stage one, with its post in the shape the simulation expects.
  have h1 : (TM.writeOutputBitTM (zIdx k)).HoareTime
      (fun inp work out => inp = I ∧ work = bodyBank k N (1 + T) v a r ∧
        ∃ s : Γw, s ≠ Γw.one ∧ out = outSlot s)
      (fun inp work out => inp = I ∧ work = bodyBank k N (1 + T) v a r ∧
        out = TM.blankTape) 1 :=
    (blankSlot_hoareTime k N (1 + T) v a r I hIp).strengthen_post
      (fun _ _ _ h => ⟨h.1, h.2.1, by rw [h.2.2, outSlot_blank_eq_blankTape]⟩)
  have htrans1 : ∀ inp work out,
      (inp = I ∧ work = bodyBank k N (1 + T) v a r ∧ out = TM.blankTape) →
      (TM.transitionInput inp = I ∧
        (fun i => TM.transitionTape (work i)) = bodyBank k N (1 + T) v a r ∧
        TM.transitionTape out = TM.blankTape) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨TM.transitionInput_eq_self hIp.read_ne_start,
      funext fun i => TM.transitionTape_eq_self (bodyBank_parked k N (1 + T) v a r i).read_ne_start,
      TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start⟩
  -- The five remaining stages, folded from the inside out.
  have h6 := wipeStage_hoareTime k N T v a r I b hIsi hIp
  have h5 := TM.seqTM_hoareTime _ _ (bumpStage_hoareTime k N (1 + T) v a r T I b hIp hIz hT)
    (afterBump_trans k N (1 + T) v a r T I b hIp) h6
  have h4 := TM.seqTM_hoareTime _ _ (publishStage_hoareTime k N (1 + T) v a r T I b hIp)
    (afterPublish_trans k N (1 + T) v a r T I b hIp) h5
  have h3 := TM.seqTM_hoareTime _ _
    (parkStage_hoareTime k N (1 + T) v a r T I b (bodyInput_head x) hcne)
    (afterPark_trans k N (1 + T) v a r T I b hIp) h4
  have h2 := TM.seqTM_hoareTime _ _ (simTM_hoareTime tm x hne hall T v hT hfT N (1 + T) a r)
    (afterSim_trans k N (1 + T) v a r T I b) h3
  exact TM.seqTM_hoareTime _ _ h1 htrans1 h2


/-- The tape state the body hands to the test: the bank at the next index, verdict slot blank. -/
def bodyMid (k N T : ℕ) (x : List Bool) (tm : NTM k) (v : ℕ) : TM.TapePred (bodyTapes k) :=
  fun inp work out => inp = bodyInput x ∧
    work = bodyBank k N (1 + T) (v + 1) (tally (acceptsAt tm x T) (v + 1))
      (tally (fun u => !acceptsAt tm x T u) (v + 1)) ∧
    out = outSlot Γw.blank

/-- **The body meets the loop rule's obligation.** Its contract is the tally step: the count
advances and exactly one of the two tallies grows. -/
theorem bodyTM_hoareTime_mid (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (N bBody : ℕ) (v : ℕ)
    (hbound : bodyTime k T v (tally (acceptsAt tm x T) v)
      (tally (fun u => !acceptsAt tm x T u) v) ≤ bBody) :
    (bodyTM tm).HoareTime
      (tallyPre (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
        (acceptsAt tm x T) v)
      (bodyMid k N T x tm v) bBody := by
  refine ((bodyTM_hoareTime tm x hne hall T v hT hfT N
    (tally (acceptsAt tm x T) v) (tally (fun u => !acceptsAt tm x T u) v)).strengthen_post
    ?_).mono_bound hbound
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨hi, ?_, ho⟩
  rw [hw]
  congr 1
  have hflip : (if !acceptsAt tm x T v then 1 else 0)
      = (if acceptsAt tm x T v then 0 else 1) := by
    cases acceptsAt tm x T v <;> simp
  show tally (fun u => !acceptsAt tm x T u) v + (if acceptsAt tm x T v then 0 else 1)
    = tally (fun u => !acceptsAt tm x T u) v + (if !acceptsAt tm x T v then 1 else 0)
  rw [hflip]


/-- **The counting loop.** Body and test together run the tally to its horizon: the counter walks
from `0` to `N`, and the two tallies end holding how many of the paths accepted and how many
did not. -/
theorem tallyLoop_full (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T N : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (hN : 1 ≤ N) (bBody bTest B : ℕ)
    (hbBody : ∀ v, v < N → bodyTime k T v (tally (acceptsAt tm x T) v)
      (tally (fun u => !acceptsAt tm x T u) v) ≤ bBody)
    (hbTest : ∀ w, w ≤ N → TM.binaryEqTime w.bits N.bits + 1 +
      (3 * (max (3 * (B + 3) + 1) (TM.resetBinaryWorkTime B 1) + 1) + 1) ≤ bTest)
    (hBw : ∀ w, w ≤ N → 1 + 1 + TM.binaryEqTime w.bits N.bits ≤ B) :
    (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).HoareTime
      (tallyPre (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
        (acceptsAt tm x T) 0)
      (tallyPost (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
        (acceptsAt tm x T) N N)
      (N * (bBody + bTest + 5)) := by
  have hne' : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  obtain ⟨-, -, -, hnc, hna, hnr, hsc, hsa, hsr, hsn, -⟩ := bodyIdx_distinct k
  have hd : TM.BinaryEqDistinct (cIdx k) (nIdx k) (resIdx k) :=
    ⟨Ne.symm hnc, Ne.symm hsc, Ne.symm hsn⟩
  refine tallyLoop_hoareTime_of_hoare (bodyTM tm)
    (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)) (cIdx k) (aIdx k) (rIdx k) (bodyInput x)
    (bodyRest k N (1 + T)) (acceptsAt tm x T) (bodyMid k N T x tm) N bBody bTest hN
    (bodyInput_parked x) (bodyRest_parked k N (1 + T)) ?_ ?_ ?_
  · intro v hv
    exact bodyTM_hoareTime_mid tm x hne hall T hT hfT N bBody v (hbBody v hv)
  · rintro v inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨bodyInput_parked x, bodyBank_parked k N (1 + T) _ _ _, outSlot_parked _, rfl, rfl⟩
  · intro v hv
    refine (tallyTestTM_hoareTime_tallyPost (cIdx k) (aIdx k) (rIdx k) (nIdx k) (resIdx k) hd
      hnc hna hnr hsc hsa hsr (bodyInput x) (bodyRest k N (1 + T)) (acceptsAt tm x T) N (v + 1)
      B 1 (bodyInput_parked x) (bodyInput_startInvariant x).1
      (bodyRest_parked k N (1 + T)) (bodyRest_cells_zero k N (1 + T))
      (fun j => le_of_eq (bodyRest_head k N (1 + T) j))
      (bodyRest_nIdx k N (1 + T)) (bodyRest_other k N (1 + T) (resIdx k) hsn
        (hne' _ _ (by simp only [resIdx, regIdx]; omega)))
      (hBw (v + 1) (by omega))).mono_bound (hbTest (v + 1) (by omega))


/-- **The comparison's running time is uniform over the loop.** Every count the loop compares is
at most the horizon, and a smaller number has no more binary digits, so one bound serves every
iteration — which is what the loop rule demands. -/
theorem binaryEqTime_le_of_le (w N : ℕ) (h : w ≤ N) :
    TM.binaryEqTime w.bits N.bits = N.bits.length + 1 := by
  have hlen : w.bits.length ≤ N.bits.length := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
    exact Nat.size_le_size h
  show max w.bits.length N.bits.length + 1 = _
  omega


/-- A tally over `[0, v)` counts at most `v` things. -/
theorem tally_le (P : ℕ → Bool) : ∀ v, tally P v ≤ v
  | 0 => le_refl 0
  | v + 1 => by
      show tally P v + (if P v then 1 else 0) ≤ v + 1
      have := tally_le P v
      split <;> omega

/-- The body's running time with every value-dependent part replaced by its bound at the
horizon. -/
def bodyTimeBound (k T N : ℕ) : ℕ :=
  1 + 1 + (T + 1 +
    ((1 + 1 + (2 * (max (1 + T + 2) (2 * (1 + T + 3) + 1) + 1) + 1)) + 1 +
      (1 + 1 +
        ((3 * (max (1 + 1 + max (2 * N.size + 2) (2 * N.size + 2) + 5)
          (2 * N.size + 2) + 1) + 1) + 1 +
          ((wipeTargets k).length * ((1 + T) + 4) + (1 + T) * 4 + 8 + 1 +
            ((wipeTargets k).length * ((1 + T) + 4) + 1))))))

/-- **The body's running time is uniform over the loop.** Only three parts of it depend on the
iteration — the three counter increments — and each is bounded by the width of the horizon, since
neither the count nor either tally ever exceeds it. -/
theorem bodyTime_le (k T N v : ℕ) (P : ℕ → Bool) (hv : v ≤ N) :
    bodyTime k T v (tally P v) (tally (fun u => !P u) v) ≤ bodyTimeBound k T N := by
  have hb : ∀ w, w ≤ N → TM.binarySuccTime w ≤ 2 * N.size + 2 := by
    intro w hw
    have h1 := TM.binarySuccTime_le w
    have h2 := Nat.size_le_size hw
    omega
  have hv' := hb v hv
  have ha := hb (tally P v) (le_trans (tally_le P v) hv)
  have hr := hb (tally (fun u => !P u) v) (le_trans (tally_le _ v) hv)
  unfold bodyTime bodyTimeBound
  gcongr


/-- The head bound the test's rewinds need: enough for the horizon's digits. -/
def testB (N : ℕ) : ℕ := N.bits.length + 3

/-- The test's running time at the horizon. -/
def testTimeBound (N : ℕ) : ℕ :=
  (N.bits.length + 1) + 1 +
    (3 * (max (3 * (testB N + 3) + 1) (TM.resetBinaryWorkTime (testB N) 1) + 1) + 1)

/-- **The counting loop with concrete bounds.** Both running times are now written in terms of
the horizon alone, which is what a polynomial space bound will need. -/
theorem tallyLoop_full_bounded (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T N : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (hN : 1 ≤ N) :
    (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).HoareTime
      (tallyPre (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
        (acceptsAt tm x T) 0)
      (tallyPost (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
        (acceptsAt tm x T) N N)
      (N * (bodyTimeBound k T N + testTimeBound N + 5)) :=
  tallyLoop_full tm x hne hall T N hT hfT hN (bodyTimeBound k T N) (testTimeBound N) (testB N)
    (fun v hv => bodyTime_le k T N v (acceptsAt tm x T) (le_of_lt hv))
    (fun w hw => by
      rw [binaryEqTime_le_of_le w N hw]
      exact le_of_eq rfl)
    (fun w hw => by
      rw [binaryEqTime_le_of_le w N hw]
      show 1 + 1 + (N.bits.length + 1) ≤ testB N
      unfold testB
      omega)


/-- **The body keeps a window.** Its running time bounds how far any head can drift during one
pass, and every tape it starts from is parked at cell one, so the whole pass stays inside a
window of that width — independent of which iteration it is. -/
theorem bodyTM_keepsWindowOn (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T v : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (N a r : ℕ) :
    (bodyTM tm).KeepsWindowOn
      (fun c => c.state = (bodyTM tm).qstart ∧
        (c.input = bodyInput x ∧ c.work = bodyBank k N (1 + T) v a r ∧
          ∃ s : Γw, s ≠ Γw.one ∧ c.output = outSlot s))
      x.length (1 + bodyTime k T v a r) :=
  TM.keepsWindowOn_of_hoareTime (bodyTM_hoareTime tm x hne hall T v hT hfT N a r)
    (fun _ work _ hpre i => by rw [hpre.2.1]; exact le_of_eq (bodyBank_head k N (1 + T) v a r i))
    (fun inp _ _ hpre => by rw [hpre.1, bodyInput_head]; omega)
    (fun _ _ out hpre => by
      obtain ⟨-, -, s, -, ho⟩ := hpre
      rw [ho]
      show (1 : ℕ) ≤ 1 + 1
      omega)


/-- **The counting loop's space bound at the concrete layout.** Every configuration the loop ever
reaches fits inside a window one iteration wide — and one iteration's width is a polynomial in
the horizon, not in the exponentially many iterations. -/
theorem tallyLoop_keepsWindow_bounded (tm : NTM k) (x : List Bool)
    (hne : tm.qstart ≠ tm.qhalt) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T N : ℕ)
    (hT : 1 ≤ T) (hfT : f x.length ≤ T) (hN : 1 ≤ N) :
    ∀ inp work out,
      tallyPre (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
        (acceptsAt tm x T) 0 inp work out →
      ∀ c, (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).reaches
        ⟨(TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart,
          inp, work, out⟩ c →
        c.WithinDecisionSpace x.length
          (1 + (bodyTimeBound k T N + testTimeBound N + 5)) := by
  have hne' : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  obtain ⟨-, -, -, hnc, hna, hnr, hsc, hsa, hsr, hsn, -⟩ := bodyIdx_distinct k
  have hd : TM.BinaryEqDistinct (cIdx k) (nIdx k) (resIdx k) :=
    ⟨Ne.symm hnc, Ne.symm hsc, Ne.symm hsn⟩
  refine tallyLoop_keepsWindow_of_hoare (bodyTM tm)
    (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)) (cIdx k) (aIdx k) (rIdx k) (bodyInput x)
    (bodyRest k N (1 + T)) (acceptsAt tm x T) (bodyMid k N T x tm) N
    (bodyTimeBound k T N) (testTimeBound N) x.length hN
    (bodyInput_parked x) (bodyRest_parked k N (1 + T))
    (by rw [bodyInput_head]; omega) (fun i => le_of_eq (bodyRest_head k N (1 + T) i)) ?_ ?_ ?_
  · intro v hv
    exact bodyTM_hoareTime_mid tm x hne hall T hT hfT N (bodyTimeBound k T N) v
      (bodyTime_le k T N v (acceptsAt tm x T) (le_of_lt hv))
  · rintro v inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨bodyInput_parked x, bodyBank_parked k N (1 + T) _ _ _, outSlot_parked _, rfl, rfl⟩
  · intro v hv
    refine (tallyTestTM_hoareTime_tallyPost (cIdx k) (aIdx k) (rIdx k) (nIdx k) (resIdx k) hd
      hnc hna hnr hsc hsa hsr (bodyInput x) (bodyRest k N (1 + T)) (acceptsAt tm x T) N (v + 1)
      (testB N) 1 (bodyInput_parked x) (bodyInput_startInvariant x).1
      (bodyRest_parked k N (1 + T)) (bodyRest_cells_zero k N (1 + T))
      (fun j => le_of_eq (bodyRest_head k N (1 + T) j))
      (bodyRest_nIdx k N (1 + T)) (bodyRest_other k N (1 + T) (resIdx k) hsn
        (hne' _ _ (by simp only [resIdx, regIdx]; omega)))
      (by
        rw [binaryEqTime_le_of_le (v + 1) N (by omega)]
        show 1 + 1 + (N.bits.length + 1) ≤ testB N
        unfold testB
        omega)).mono_bound (by
      rw [binaryEqTime_le_of_le (v + 1) N (by omega)]
      exact le_of_eq rfl)


/-- **The comparison the epilogue actually performs.** Testing `r < a` directly would need a
strict comparator; testing `(r + 1) - a = 0` needs only truncated subtraction and an equality
test against zero, both of which the subroutine library already has — and it avoids having to
complement the verdict afterwards. -/
theorem lt_iff_succ_sub_eq_zero (r a : ℕ) : r < a ↔ (r + 1) - a = 0 := by
  rw [Nat.sub_eq_zero_iff_le]
  omega

/-- **The counting machine's epilogue.** Bump the rejecting tally, subtract the accepting one
from it, clear the counter to reuse as scratch, test the difference against zero, and publish the
answer. The counter's value is spent by this point, which is what frees a register for the test's
result. -/
def epiloguePreTM (k : ℕ) : TM (bodyTapes k) :=
  TM.bigSeqTM
    [TM.binarySuccTM (rIdx k),
      TM.binaryRippleSubTM (rIdx k) (aIdx k) (resIdx k),
      TM.resetBinaryWorkTM (cIdx k)]

/-- The epilogue's tail: put the equality test's answer at cell one and publish it. -/
def epiloguePostTM (k : ℕ) : TM (bodyTapes k) :=
  TM.seqTM (TM.bigSeqTM ([cIdx k].map TM.rewindWorkTM)) (TM.writeOutputBitTM (cIdx k))

/-- **The counting machine's epilogue.** Bump the rejecting tally, subtract the accepting one
from it, clear the counter to reuse as scratch, test the difference against zero, and publish the
answer. -/
def epilogueTM (k : ℕ) : TM (bodyTapes k) :=
  TM.seqTM (epiloguePreTM k)
    (TM.seqTM (TM.binaryEqTM (resIdx k) (zIdx k) (cIdx k)) (epiloguePostTM k))

/-- The bank the epilogue's arithmetic leaves behind. -/
def epilogueBank (k N H a r : ℕ) : Fin (bodyTapes k) → Tape :=
  Function.update
    (Function.update
      (Function.update (bodyBank k N H N a r) (rIdx k) (natTape (r + 1)))
      (resIdx k) (natTape ((r + 1) - a)))
    (cIdx k) TM.blankTape


/-- **The epilogue's arithmetic, contracted.** Three pinned stages: bump the rejecting tally,
subtract the accepting one from it, and clear the counter — whose value is spent — to free a
register for the comparison that follows. -/
theorem epiloguePreTM_hoareTime (k N H a r : ℕ) (I O : Tape)
    (hI : TM.Parked I) (hO : TM.Parked O) :
    (epiloguePreTM k).HoareTime
      (fun inp work out => inp = I ∧ work = bodyBank k N H N a r ∧ out = O)
      (fun inp work out => inp = I ∧ work = epilogueBank k N H a r ∧ out = O)
      (3 * (max (max (TM.binarySuccTime r) (TM.binaryRippleSubTime (r + 1) a))
        (TM.resetBinaryWorkTime 1 N.bits.length) + 1) + 1) := by
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  obtain ⟨hca, hcr, har, -⟩ := bodyIdx_distinct k
  have hsc : resIdx k ≠ cIdx k := hne _ _ (by simp only [resIdx, cIdx]; omega)
  have hsa : resIdx k ≠ aIdx k := hne _ _ (by simp only [resIdx, aIdx]; omega)
  have hsr : resIdx k ≠ rIdx k := hne _ _ (by simp only [resIdx, rIdx]; omega)
  have hsn : resIdx k ≠ nIdx k := hne _ _ (by simp only [resIdx, nIdx]; omega)
  have hsreg : resIdx k ≠ regIdx k := hne _ _ (by simp only [resIdx, regIdx]; omega)
  set W0 := bodyBank k N H N a r with hW0
  set W1 := Function.update W0 (rIdx k) (natTape (r + 1)) with hW1
  set W2 := Function.update W1 (resIdx k) (natTape ((r + 1) - a)) with hW2
  set W3 := Function.update W2 (cIdx k) TM.blankTape with hW3
  have hW0P : ∀ j, TM.Parked (W0 j) := bodyBank_parked k N H N a r
  have hupd : ∀ (W : Fin (bodyTapes k) → Tape) (i : Fin (bodyTapes k)) (t : Tape),
      (∀ j, TM.Parked (W j)) → TM.Parked t → ∀ j, TM.Parked (Function.update W i t j) := by
    intro W i t hW ht j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact ht
    · rw [Function.update_of_ne hj]; exact hW j
  have hW1P : ∀ j, TM.Parked (W1 j) := hupd _ _ _ hW0P (natTape_parked _)
  have hW2P : ∀ j, TM.Parked (W2 j) := hupd _ _ _ hW1P (natTape_parked _)
  have hW3P : ∀ j, TM.Parked (W3 j) := hupd _ _ _ hW2P TM.blankTape_parked
  have hW1r : W1 (rIdx k) = natTape (r + 1) := by rw [hW1, Function.update_self]
  have hW1a : W1 (aIdx k) = natTape a := by
    rw [hW1, Function.update_of_ne har, hW0, bodyBank_aIdx]
  have hW1s : (W1 (resIdx k)).HasBinaryNat 0 := by
    rw [hW1, Function.update_of_ne hsr, hW0,
      bodyBank_rest k N H N a r (resIdx k) hsc hsa hsr, bodyRest_other k N H _ hsn hsreg]
    exact Tape.init_move_right_hasBinaryNat 0
  have hW2c : W2 (cIdx k) = natTape N := by
    rw [hW2, Function.update_of_ne (Ne.symm hsc), hW1, Function.update_of_ne hcr,
      hW0, bodyBank_cIdx]
  set bnd := max (max (TM.binarySuccTime r) (TM.binaryRippleSubTime (r + 1) a))
    (TM.resetBinaryWorkTime 1 N.bits.length) with hbnd
  refine (TM.bigSeqTM_hoareTime_pinned
    [TM.binarySuccTM (rIdx k), TM.binaryRippleSubTM (rIdx k) (aIdx k) (resIdx k),
      TM.resetBinaryWorkTM (cIdx k)]
    I (fun j => if j = 0 then W0 else if j = 1 then W1 else if j = 2 then W2 else W3)
    (fun _ => O) bnd hI ?_ (fun _ => hO) ?_).consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) (le_refl _)
  · intro j i
    split
    · exact hW0P i
    · split
      · exact hW1P i
      · split
        · exact hW2P i
        · exact hW3P i
  · intro j hj
    match j, hj with
    | 0, _ =>
      show (TM.binarySuccTM (rIdx k)).HoareTime _ _ _
      exact (TM.binarySuccTM_hoareTime_pinned (rIdx k) r I W0 O
        (by rw [hW0, bodyBank_rIdx]) hI.read_ne_start
        (fun i _ => (hW0P i).read_ne_start) hO.read_ne_start).mono_bound
        (le_trans (le_max_left _ _) (le_max_left _ _))
    | 1, _ =>
      show (TM.binaryRippleSubTM (rIdx k) (aIdx k) (resIdx k)).HoareTime _ _ _
      exact (TM.binaryRippleSubTM_hoareTime_pinned (rIdx k) (aIdx k) (resIdx k)
        ⟨Ne.symm har, Ne.symm hsr, Ne.symm hsa⟩ (r + 1) a I W1 O hW1r hW1a hW1s hI
        (fun i _ _ _ => hW1P i) hO).mono_bound
        (le_trans (le_max_right _ _) (le_max_left _ _))
    | 2, _ =>
      show (TM.resetBinaryWorkTM (cIdx k)).HoareTime _ _ _
      refine ((TM.resetBinaryWorkTM_hoareTime_frame (cIdx k) N.bits 1 I W2 O ?_ ?_ ?_ hI
        (fun i _ => hW2P i) hO).strengthen_post ?_).mono_bound (le_max_right _ _)
      · rw [hW2c]
        exact (Tape.init_move_right_hasBinaryNat N).2.2
      · rw [hW2c]
        exact (Tape.init_move_right_hasBinaryNat N).1
      · rw [hW2c]
        exact ⟨le_of_eq rfl, le_of_eq rfl⟩
      · rintro inp work out ⟨hi, hw, ho⟩
        exact ⟨hi, by rw [hw]; rfl, ho⟩


/-- The state between the epilogue's comparison and its publication: the answer sits on the
counter tape, which the comparison used as its result register. -/
def afterEq (k : ℕ) (b : Bool) (I : Tape) (B : ℕ) : TM.TapePred (bodyTapes k) :=
  fun inp work out => inp = I ∧ out = outSlot Γw.one ∧
    (∀ j, TM.Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) ∧
    (work (cIdx k)).head ≤ B ∧ (work (cIdx k)).cells 1 = Γ.ofBool b

/-- **The epilogue's publication.** Rewind the register holding the comparison's answer and copy
its bit into the output slot, where the surrounding obligation reads it. -/
theorem epiloguePostTM_hoareTime (k : ℕ) (b : Bool) (I : Tape) (B : ℕ) (hI : TM.Parked I) :
    (epiloguePostTM k).HoareTime
      (afterEq k b I B)
      (fun _inp _work out => out = outSlot (TM.readBackWrite (Γ.ofBool b)))
      (1 * (B + 3) + 1 + 1 + 1) := by
  intro inp work out hpre
  obtain ⟨hi, ho, hpark, hzero, hhead, hcell⟩ := hpre
  have hIp : TM.Parked inp := by rw [hi]; exact hI
  have hOp : TM.Parked out := by rw [ho]; exact outSlot_parked _
  set W' : Fin (bodyTapes k) → Tape :=
    fun j => if j = cIdx k then (⟨1, (work (cIdx k)).cells⟩ : Tape) else work j with hW'
  have hW'P : ∀ j, TM.Parked (W' j) := by
    intro j
    simp only [hW']
    split
    · exact ⟨le_refl 1, fun i hi2 => (hpark (cIdx k)).2 i hi2⟩
    · exact hpark j
  have hrew : (TM.bigSeqTM ([cIdx k].map TM.rewindWorkTM)).HoareTime
      (fun inp' work' out' => inp' = inp ∧ work' = work ∧ out' = out)
      (fun inp' work' out' => inp' = inp ∧ work' = W' ∧ out' = out)
      (1 * (B + 3) + 1) := by
    refine ((TM.rewindList_hoareTime [cIdx k] (by simp) B inp work out hIp hOp hpark
      ?_).strengthen_post ?_).mono_bound (by simp)
    · intro j hj
      rw [List.mem_singleton.mp hj]
      exact ⟨hzero (cIdx k), hhead⟩
    · rintro inp' work' out' ⟨rfl, rfl, hin, hout⟩
      refine ⟨rfl, funext fun j => ?_, rfl⟩
      by_cases hj : j = cIdx k
      · rw [hj, hin (cIdx k) (by simp), hW']
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
  have hpub : (TM.writeOutputBitTM (cIdx k)).HoareTime
      (fun inp' work' out' => inp' = inp ∧ work' = W' ∧ out' = out)
      (fun _inp _work out' => out' = outSlot (TM.readBackWrite (Γ.ofBool b))) 1 := by
    refine (TM.writeOutputBitTM_hoareTime_frame (cIdx k) inp W' out hIp hW'P hOp).strengthen_post
      ?_
    rintro inp' work' out' ⟨-, -, hout'⟩
    rw [hout', ho, show (W' (cIdx k)).read = Γ.ofBool b from by
      simp only [hW', ite_eq_left rfl]
      show (work (cIdx k)).cells 1 = _
      exact hcell]
    exact outSlot_write Γw.one (TM.readBackWrite (Γ.ofBool b))
  exact TM.seqTM_hoareTime _ _ hrew htrans hpub inp work out ⟨rfl, rfl, rfl⟩


theorem epilogueBank_cIdx (k N H a r : ℕ) : epilogueBank k N H a r (cIdx k) = TM.blankTape := by
  rw [epilogueBank, Function.update_self]

theorem epilogueBank_resIdx (k N H a r : ℕ) (hsc : resIdx k ≠ cIdx k) :
    epilogueBank k N H a r (resIdx k) = natTape ((r + 1) - a) := by
  rw [epilogueBank, Function.update_of_ne hsc, Function.update_self]

theorem epilogueBank_zIdx (k N H a r : ℕ) : epilogueBank k N H a r (zIdx k) = TM.blankTape := by
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  rw [epilogueBank,
    Function.update_of_ne (hne _ _ (by simp only [zIdx, cIdx]; omega)),
    Function.update_of_ne (hne _ _ (by simp only [zIdx, resIdx]; omega)),
    Function.update_of_ne (hne _ _ (by simp only [zIdx, rIdx]; omega)),
    bodyBank_rest k N H N a r (zIdx k)
      (hne _ _ (by simp only [zIdx, cIdx]; omega))
      (hne _ _ (by simp only [zIdx, aIdx]; omega))
      (hne _ _ (by simp only [zIdx, rIdx]; omega)),
    bodyRest_other k N H (zIdx k)
      (hne _ _ (by simp only [zIdx, nIdx]; omega))
      (hne _ _ (by simp only [zIdx, regIdx]; omega))]

theorem epilogueBank_parked (k N H a r : ℕ) : ∀ j, TM.Parked (epilogueBank k N H a r j) := by
  intro j
  simp only [epilogueBank]
  by_cases h1 : j = cIdx k
  · rw [h1, Function.update_self]; exact TM.blankTape_parked
  rw [Function.update_of_ne h1]
  by_cases h2 : j = resIdx k
  · rw [h2, Function.update_self]; exact natTape_parked _
  rw [Function.update_of_ne h2]
  by_cases h3 : j = rIdx k
  · rw [h3, Function.update_self]; exact natTape_parked _
  rw [Function.update_of_ne h3]
  exact bodyBank_parked k N H N a r j

theorem epilogueBank_cells_zero (k N H a r : ℕ) :
    ∀ j, (epilogueBank k N H a r j).cells 0 = Γ.start := by
  intro j
  simp only [epilogueBank]
  by_cases h1 : j = cIdx k
  · rw [h1, Function.update_self]; exact TM.blankTape_startInvariant.1
  rw [Function.update_of_ne h1]
  by_cases h2 : j = resIdx k
  · rw [h2, Function.update_self]; exact natTape_cells_zero _
  rw [Function.update_of_ne h2]
  by_cases h3 : j = rIdx k
  · rw [h3, Function.update_self]; exact natTape_cells_zero _
  rw [Function.update_of_ne h3]
  exact bodyBank_cells_zero k N H N a r j

/-- **The epilogue's comparison.** Testing the difference against zero decides `r < a`; the
answer lands on the counter tape, which the arithmetic stage cleared for exactly this purpose. -/
theorem epilogueEq_hoareTime (k N H a r : ℕ) (I : Tape) (hI : TM.Parked I)
    (hIsi : Tape.StartInvariant I) :
    (TM.binaryEqTM (resIdx k) (zIdx k) (cIdx k)).HoareTime
      (fun inp work out => inp = I ∧ work = epilogueBank k N H a r ∧
        out = outSlot Γw.one)
      (afterEq k (decide (r < a)) I 2)
      (TM.binaryEqTime ((r + 1) - a).bits (0 : ℕ).bits) := by
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  have hsc : resIdx k ≠ cIdx k := hne _ _ (by simp only [resIdx, cIdx]; omega)
  have hsz : resIdx k ≠ zIdx k := hne _ _ (by simp only [resIdx, zIdx]; omega)
  have hzc : zIdx k ≠ cIdx k := hne _ _ (by simp only [zIdx, cIdx]; omega)
  intro inp work out hpre
  obtain ⟨hi, hw, ho⟩ := hpre
  set W := epilogueBank k N H a r with hWdef
  have hWP : ∀ j, TM.Parked (W j) := epilogueBank_parked k N H a r
  have hWz : ∀ j, (W j).cells 0 = Γ.start := epilogueBank_cells_zero k N H a r
  have hlhs : (W (resIdx k)).HasBinaryString ((r + 1) - a).bits := by
    rw [hWdef, epilogueBank_resIdx k N H a r hsc]
    exact (Tape.init_move_right_hasBinaryNat _).2
  have hrhs : (W (zIdx k)).HasBinaryString (0 : ℕ).bits := by
    rw [hWdef, epilogueBank_zIdx k N H a r, show TM.blankTape = natTape 0 from natTape_zero.symm]
    exact (Tape.init_move_right_hasBinaryNat 0).2
  have hres : (W (cIdx k)).HasBinaryPrefix [] := by
    rw [hWdef, epilogueBank_cIdx k N H a r]
    refine ⟨rfl, nofun, fun i _ => ?_⟩
    show ((Tape.init ([] : List Γ)).move Dir3.right).cells (i + 1) = Γ.blank
    rw [Tape.move_cells, Tape.init_nil_cells_succ]
  have hIp : TM.Parked inp := by rw [hi]; exact hI
  have hOp : TM.Parked out := by rw [ho]; exact outSlot_parked _
  rw [hi, hw, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hinp', hres', hlhs', hlhsh, hrhs', hrhsh, hother', hout'⟩ :=
    TM.binaryEqTM_reachesIn_frame (resIdx k) (zIdx k) (cIdx k) ⟨hsz, hsc, hzc⟩
      ((r + 1) - a).bits (0 : ℕ).bits I W (outSlot Γw.one) hlhs hrhs hres
      (by rw [← hi]; exact hIp.read_ne_start) (fun i _ _ _ => (hWP i).read_ne_start)
      (outSlot_parked _).read_ne_start
  obtain ⟨-, hSI', -⟩ := TM.startInvariant_reachesIn _ hreach hIsi
    (fun j => ⟨hWz j, fun i hi2 => (hWP j).2 i hi2⟩)
    ⟨rfl, fun j hj => (outSlot_parked Γw.one).2 j hj⟩
  have hbits : (decide (((r + 1) - a).bits = (0 : ℕ).bits)) = decide (r < a) := by
    refine decide_eq_decide.mpr ?_
    rw [lt_iff_succ_sub_eq_zero]
    exact ⟨fun h => bits_injective h, fun h => by rw [h]⟩
  refine ⟨c', t, ht, hreach, hhalt, hinp', hout', fun j => ?_, fun j => (hSI' j).1, ?_, ?_⟩
  · refine ⟨?_, fun i hi2 => (hSI' j).2 i hi2⟩
    by_cases h1 : j = cIdx k
    · rw [h1, hres'.1]; omega
    by_cases h2 : j = resIdx k
    · rw [h2]; exact hlhsh
    by_cases h3 : j = zIdx k
    · rw [h3]; exact hrhsh
    · rw [hother' j h2 h3 h1]; exact (hWP j).1
  · rw [hres'.1]
    simp
  · rw [hres'.2.1 0 (by simp), ← hbits]
    simp


/-- The state between the epilogue's comparison and its publication survives a phase boundary:
every tape it names is parked, so the boundary is the identity. -/
theorem afterEq_trans (k : ℕ) (b : Bool) (I : Tape) (B : ℕ) (hI : TM.Parked I)
    (inp : Tape) (work : Fin (bodyTapes k) → Tape) (out : Tape)
    (h : afterEq k b I B inp work out) :
    afterEq k b I B (TM.transitionInput inp) (fun i => TM.transitionTape (work i))
      (TM.transitionTape out) := by
  obtain ⟨hi, ho, hpark, hzero, hhead, hcell⟩ := h
  have hid : ∀ j, TM.transitionTape (work j) = work j :=
    fun j => TM.transitionTape_eq_self (hpark j).read_ne_start
  have hidI : TM.transitionInput inp = inp := by
    rw [hi]; exact TM.transitionInput_eq_self hI.read_ne_start
  have hidO : TM.transitionTape out = out := by
    rw [ho]; exact TM.transitionTape_eq_self (outSlot_parked _).read_ne_start
  rw [hidI, hidO, show (fun i => TM.transitionTape (work i)) = work from funext hid]
  exact ⟨hi, ho, hpark, hzero, hhead, hcell⟩

/-- The epilogue's running time: its three stages and the two transitions between them. -/
def epilogueTime (N a r : ℕ) : ℕ :=
  (3 * (max (max (TM.binarySuccTime r) (TM.binaryRippleSubTime (r + 1) a))
    (TM.resetBinaryWorkTime 1 N.bits.length) + 1) + 1) + 1 +
    (TM.binaryEqTime ((r + 1) - a).bits (0 : ℕ).bits + 1 + (1 * (2 + 3) + 1 + 1 + 1))

/-- **The epilogue's contract.** From the bank the loop leaves — the counter at the horizon, the
two tallies holding their counts — the machine writes `1` into the verdict slot exactly when the
rejecting tally is smaller than the accepting one. -/
theorem epilogueTM_hoareTime (k N H a r : ℕ) (I : Tape) (hI : TM.Parked I)
    (hIsi : Tape.StartInvariant I) :
    (epilogueTM k).HoareTime
      (fun inp work out => inp = I ∧ work = bodyBank k N H N a r ∧ out = outSlot Γw.one)
      (fun _inp _work out => out = outSlot (TM.readBackWrite (Γ.ofBool (decide (r < a)))))
      (epilogueTime N a r) := by
  have htrans1 : ∀ inp work out,
      (inp = I ∧ work = epilogueBank k N H a r ∧ out = outSlot Γw.one) →
      (TM.transitionInput inp = I ∧
        (fun i => TM.transitionTape (work i)) = epilogueBank k N H a r ∧
        TM.transitionTape out = outSlot Γw.one) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨TM.transitionInput_eq_self hI.read_ne_start,
      funext fun i => TM.transitionTape_eq_self (epilogueBank_parked k N H a r i).read_ne_start,
      TM.transitionTape_eq_self (outSlot_parked _).read_ne_start⟩
  exact TM.seqTM_hoareTime _ _ (epiloguePreTM_hoareTime k N H a r I (outSlot Γw.one) hI
      (outSlot_parked _)) htrans1
    (TM.seqTM_hoareTime _ _ (epilogueEq_hoareTime k N H a r I hI hIsi)
      (afterEq_trans k (decide (r < a)) I 2 hI)
      (epiloguePostTM_hoareTime k (decide (r < a)) I 2 hI))


/-- **The epilogue keeps a window.** It runs for a bounded time from tapes parked at cell one, so
no head can leave a window of that width. -/
theorem epilogueTM_keepsWindowOn (k N H a r : ℕ) (x : List Bool) :
    (epilogueTM k).KeepsWindowOn
      (fun c => c.state = (epilogueTM k).qstart ∧
        (c.input = bodyInput x ∧ c.work = bodyBank k N H N a r ∧
          c.output = outSlot Γw.one))
      x.length (1 + epilogueTime N a r) :=
  TM.keepsWindowOn_of_hoareTime_pinned
    (epilogueTM_hoareTime k N H a r (bodyInput x) (bodyInput_parked x)
      (bodyInput_startInvariant x))
    (fun i => le_of_eq (bodyBank_head k N H N a r i))
    (by rw [bodyInput_head]; omega)
    (by show (1 : ℕ) ≤ 1 + 1; omega)


/-- The register-arithmetic subroutines state their contracts in the `TM.EmitPred` shape, whose
output component is an accumulator of emitted bits. With nothing emitted that is just the blank
tape, so those contracts are pinned after all. -/
theorem outAcc_nil_iff (out : Tape) : TM.OutAcc [] out ↔ out = TM.blankTape := by
  constructor
  · intro h
    refine TM.OutAcc.eq h ?_
    show TM.OutAcc [] TM.blankTape
    exact TM.outAcc_nil_init
  · intro h
    rw [h]
    exact TM.outAcc_nil_init


/-- A pinned contract with a blank output is an `TM.EmitPred` contract with nothing emitted. -/
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

/-- The machine's own input tape, in the shape the register subroutines name it. -/
theorem bodyInput_eq (x : List Bool) :
    bodyInput x = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) :=
  Tape.ext rfl (by rw [bodyInput, Tape.move_cells])

/-- **The counting machine's prologue.** Measure the input, evaluate the horizon polynomial on a
unary register, turn that register into the binary horizon with one increment, bump the wipe
height, and clear the scratch. -/
def prologueTM (k : ℕ) (p : Polynomial ℕ) : TM (bodyTapes k) :=
  TM.bigSeqTM
    [TM.inputLenRegTM (resIdx k),
      TM.polyEvalTM (resIdx k) (regIdx k) (nIdx k) p,
      TM.binarySuccTM (nIdx k),
      TM.incRegTM (regIdx k),
      TM.clearRegTM (resIdx k)]


/-- The bank the prologue's five stages leave behind. -/
def prologueBank (k T lx : ℕ) : Fin (bodyTapes k) → Tape :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update (fun _ => TM.blankTape) (resIdx k) (TM.regTape lx))
          (nIdx k) (TM.regTape T))
        (regIdx k) (TM.regTape T))
      (nIdx k) (natTape (2 ^ T)))
    (regIdx k) (TM.regTape (T + 1))

/-- **The prologue lands on the loop's starting bank.** The horizon sits on `nIdx`, the wipe
height on `regIdx`, and everything else — the counter, both tallies, the scratch registers — is
blank, which is what `NTM.bodyBank` at index zero says. -/
theorem prologueBank_eq (k T lx : ℕ) :
    Function.update (prologueBank k T lx) (resIdx k) (TM.regTape 0)
      = bodyBank k (2 ^ T) (1 + T) 0 0 0 := by
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  funext j
  by_cases hs : j = resIdx k
  · rw [hs, Function.update_self, regTape_zero,
      bodyBank_rest k (2 ^ T) (1 + T) 0 0 0 (resIdx k)
        (hne _ _ (by simp only [resIdx, cIdx]; omega))
        (hne _ _ (by simp only [resIdx, aIdx]; omega))
        (hne _ _ (by simp only [resIdx, rIdx]; omega)),
      bodyRest_other k (2 ^ T) (1 + T) (resIdx k)
        (hne _ _ (by simp only [resIdx, nIdx]; omega))
        (hne _ _ (by simp only [resIdx, regIdx]; omega))]
  rw [Function.update_of_ne hs]
  by_cases hr : j = regIdx k
  · rw [hr, prologueBank, Function.update_self,
      bodyBank_rest k (2 ^ T) (1 + T) 0 0 0 (regIdx k)
        (hne _ _ (by simp only [regIdx, cIdx]; omega))
        (hne _ _ (by simp only [regIdx, aIdx]; omega))
        (hne _ _ (by simp only [regIdx, rIdx]; omega)),
      bodyRest_regIdx]
    congr 1
    omega
  by_cases hn : j = nIdx k
  · rw [hn, prologueBank, Function.update_of_ne (hne _ _ (by simp only [nIdx, regIdx]; omega)),
      Function.update_self,
      bodyBank_rest k (2 ^ T) (1 + T) 0 0 0 (nIdx k)
        (hne _ _ (by simp only [nIdx, cIdx]; omega))
        (hne _ _ (by simp only [nIdx, aIdx]; omega))
        (hne _ _ (by simp only [nIdx, rIdx]; omega)),
      bodyRest_nIdx]
  · rw [prologueBank, Function.update_of_ne hr, Function.update_of_ne hn,
      Function.update_of_ne hr, Function.update_of_ne hn, Function.update_of_ne hs]
    show TM.blankTape = _
    by_cases hc : j = cIdx k
    · rw [hc, bodyBank_cIdx, natTape_zero]
    by_cases ha : j = aIdx k
    · rw [ha, bodyBank_aIdx, natTape_zero]
    by_cases hb : j = rIdx k
    · rw [hb, bodyBank_rIdx, natTape_zero]
    · rw [bodyBank_rest k (2 ^ T) (1 + T) 0 0 0 j hc ha hb,
        bodyRest_other k (2 ^ T) (1 + T) j hn hr]


/-- A bound covering the input length and every Horner accumulator the prologue forms. -/
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

/-- The prologue's running time. -/
def prologueTime (p : Polynomial ℕ) (lx : ℕ) : ℕ :=
  5 * (max (max (max (2 * lx + 4)
    (TM.opBudget (prologueCap p lx) + 1 +
      ((p.natDegree + 1) * (TM.layerBudget (prologueCap p lx) + 1) + 1)))
    (TM.binarySuccTime (2 ^ p.eval lx - 1)))
    (max (2 * p.eval lx + 4) (2 * lx + 4)) + 1) + 1

/-- **The prologue's contract.** From the blank bank it lands on the loop's starting bank: the
horizon on `nIdx`, the wipe height on `regIdx`, everything else blank. -/
theorem prologueTM_hoareTime (k : ℕ) (p : Polynomial ℕ) (x : List Bool) :
    (prologueTM k p).HoareTime
      (fun inp work out => inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        work = (fun _ => TM.blankTape) ∧ out = TM.blankTape)
      (fun inp work out => inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        work = bodyBank k (2 ^ p.eval x.length) (1 + p.eval x.length) 0 0 0 ∧
        out = TM.blankTape)
      (prologueTime p x.length) := by
  have hne : ∀ i i' : Fin (bodyTapes k), i.val ≠ i'.val → i ≠ i' :=
    fun i i' h hh => h (congrArg Fin.val hh)
  have hsn : resIdx k ≠ nIdx k := hne _ _ (by simp only [resIdx, nIdx]; omega)
  have hsg : resIdx k ≠ regIdx k := hne _ _ (by simp only [resIdx, regIdx]; omega)
  have hgn : regIdx k ≠ nIdx k := hne _ _ (by simp only [regIdx, nIdx]; omega)
  set I : Tape := (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) with hI
  have hIp : TM.Parked I := by rw [hI, ← bodyInput_eq]; exact bodyInput_parked x
  set lx := x.length with hlx
  set T := p.eval lx with hT
  set M := prologueCap p lx with hM
  set V0 : Fin (bodyTapes k) → Tape := fun _ => TM.blankTape with hV0
  set V1 : Fin (bodyTapes k) → Tape :=
    Function.update V0 (resIdx k) (TM.regTape lx) with hV1
  set V2 : Fin (bodyTapes k) → Tape :=
    Function.update (Function.update V1 (nIdx k) (TM.regTape T)) (regIdx k)
      (TM.regTape T) with hV2
  set V3 : Fin (bodyTapes k) → Tape :=
    Function.update V2 (nIdx k) (natTape (2 ^ T)) with hV3
  set V4 : Fin (bodyTapes k) → Tape :=
    Function.update V3 (regIdx k) (TM.regTape (T + 1)) with hV4
  have hupd : ∀ (W : Fin (bodyTapes k) → Tape) (i : Fin (bodyTapes k)) (t : Tape),
      (∀ j, TM.Parked (W j)) → TM.Parked t → ∀ j, TM.Parked (Function.update W i t j) := by
    intro W i t hW ht j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact ht
    · rw [Function.update_of_ne hj]; exact hW j
  have hreg : ∀ v : ℕ, TM.Parked (TM.regTape v) := fun v => by
    rw [regTape_eq_natTape]; exact natTape_parked _
  have hV0P : ∀ j, TM.Parked (V0 j) := fun _ => TM.blankTape_parked
  have hV1P : ∀ j, TM.Parked (V1 j) := hupd _ _ _ hV0P (hreg _)
  have hV2P : ∀ j, TM.Parked (V2 j) := hupd _ _ _ (hupd _ _ _ hV1P (hreg _)) (hreg _)
  have hV3P : ∀ j, TM.Parked (V3 j) := hupd _ _ _ hV2P (natTape_parked _)
  have hV4P : ∀ j, TM.Parked (V4 j) := hupd _ _ _ hV3P (hreg _)
  have hV1s : V1 (resIdx k) = TM.regTape lx := by rw [hV1, Function.update_self]
  have hV1g : V1 (regIdx k) = TM.regTape 0 := by
    rw [hV1, Function.update_of_ne (Ne.symm hsg), hV0, regTape_zero]
  have hV1n : V1 (nIdx k) = TM.regTape 0 := by
    rw [hV1, Function.update_of_ne (Ne.symm hsn), hV0, regTape_zero]
  have hV2n : V2 (nIdx k) = TM.regTape T := by
    rw [hV2, Function.update_of_ne hgn.symm, Function.update_self]
  have hV2g : V2 (regIdx k) = TM.regTape T := by rw [hV2, Function.update_self]
  have hV3g : V3 (regIdx k) = TM.regTape T := by
    rw [hV3, Function.update_of_ne hgn, hV2g]
  have hV4s : V4 (resIdx k) = TM.regTape lx := by
    rw [hV4, Function.update_of_ne hsg, hV3, Function.update_of_ne hsn, hV2,
      Function.update_of_ne hsg, Function.update_of_ne hsn, hV1s]
  have hpow : 2 ^ T - 1 + 1 = 2 ^ T := by
    have : 1 ≤ 2 ^ T := Nat.one_le_two_pow
    omega
  set bnd := max (max (max (2 * lx + 4)
    (TM.opBudget M + 1 + ((p.natDegree + 1) * (TM.layerBudget M + 1) + 1)))
    (TM.binarySuccTime (2 ^ T - 1)))
    (max (2 * T + 4) (2 * lx + 4)) with hbnd
  refine (TM.bigSeqTM_hoareTime
    [TM.inputLenRegTM (resIdx k), TM.polyEvalTM (resIdx k) (regIdx k) (nIdx k) p,
      TM.binarySuccTM (nIdx k), TM.incRegTM (regIdx k), TM.clearRegTM (resIdx k)]
    I
    (fun j => if j = 0 then V0 else if j = 1 then V1 else if j = 2 then V2
      else if j = 3 then V3 else if j = 4 then V4
      else Function.update V4 (resIdx k) (TM.regTape 0))
    (fun _ => []) bnd hIp ?_ ?_).consequence ?_ ?_ (le_refl _)
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
            · exact hupd _ _ _ hV4P (hreg _) i
  · intro j hj
    match j, hj with
    | 0, _ =>
      show (TM.inputLenRegTM (resIdx k)).HoareTime _ _ _
      exact (TM.inputLenRegTM_hoareTime (resIdx k) x V0 [] (fun i _ => hV0P i)
        (by rw [hV0, regTape_zero])).mono_bound
        (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
    | 1, _ =>
      show (TM.polyEvalTM (resIdx k) (regIdx k) (nIdx k) p).HoareTime _ _ _
      exact (TM.polyEvalTM_hoareTime (resIdx k) (regIdx k) (nIdx k) hsg hsn hgn p M lx 0 0
        (le_prologueCap p lx) (Nat.zero_le _) (Nat.zero_le _)
        (fun j _ => le_trans (TM.hornerFold_take_le lx (TM.polyCoeffs p) j) (le_of_eq rfl))
        I V1 [] hIp hV1P hV1s hV1g hV1n).mono_bound
        (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
    | 2, _ =>
      show (TM.binarySuccTM (nIdx k)).HoareTime _ _ _
      refine (hoareTime_emit_of_pinned
        ((TM.binarySuccTM_hoareTime_pinned (nIdx k) (2 ^ T - 1) I V2 TM.blankTape
          (by rw [hV2n, regTape_eq_natTape]) hIp.read_ne_start
          (fun i _ => (hV2P i).read_ne_start)
          TM.blankTape_parked.read_ne_start).strengthen_post ?_)).mono_bound
        (le_trans (le_max_right _ _) (le_max_left _ _))
      rintro inp work out ⟨hi, hw, ho⟩
      exact ⟨hi, by rw [hw, hpow]; rfl, ho⟩
    | 3, _ =>
      show (TM.incRegTM (regIdx k)).HoareTime _ _ _
      exact (TM.incRegTM_hoareTime (regIdx k) T I V3 [] hIp (fun i _ => hV3P i)
        hV3g).mono_bound (le_trans (le_max_left _ _) (le_max_right _ _))
    | 4, _ =>
      show (TM.clearRegTM (resIdx k)).HoareTime _ _ _
      exact (TM.clearRegTM_hoareTime (resIdx k) lx I V4 [] hIp (fun i _ => hV4P i)
        hV4s).mono_bound (le_trans (le_max_right _ _) (le_max_right _ _))
  · rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, hw, (outAcc_nil_iff out).mpr ho⟩
  · rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨hi, ?_, (outAcc_nil_iff out).mp ho⟩
    rw [hw]
    show Function.update V4 (resIdx k) (TM.regTape 0) = _
    rw [hV4, hV3, hV2, hV1, hV0]
    exact prologueBank_eq k T lx


/-- **The prologue keeps a window.** It runs for a bounded time from blank tapes parked at cell
one, so nothing travels beyond a window of that width. -/
theorem prologueTM_keepsWindowOn (k : ℕ) (p : Polynomial ℕ) (x : List Bool) :
    (prologueTM k p).KeepsWindowOn
      (fun c => c.state = (prologueTM k p).qstart ∧
        (c.input = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
          c.work = (fun _ => TM.blankTape) ∧ c.output = TM.blankTape))
      x.length (1 + prologueTime p x.length) :=
  TM.keepsWindowOn_of_hoareTime_pinned (prologueTM_hoareTime k p x)
    (fun _ => le_of_eq rfl) (by show (1 : ℕ) ≤ x.length + 1 + 1; omega)
    (by show (1 : ℕ) ≤ 1 + 1; omega)

/-- **The whole counting machine.** Park the heads off the left marker, set up the horizon and
the wipe height, run the tally to its horizon, then compare the two tallies and publish. -/
def ppMachine (k : ℕ) (tm : NTM k) (p : Polynomial ℕ) : TM (bodyTapes k) :=
  TM.seqTM TM.skipTM
    (TM.seqTM (prologueTM k p)
      (TM.seqTM (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)))
        (epilogueTM k)))


/-- **The parking step.** One transition off the initial configuration puts every head at cell
one, which is where every stage of the machine expects to be entered. -/
theorem ppPark_hoareTime (k : ℕ) (x : List Bool) :
    (TM.skipTM (n := bodyTapes k)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init ([] : List Γ)) ∧ out = Tape.init ([] : List Γ))
      (fun inp work out => inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        work = (fun _ => TM.blankTape) ∧ out = TM.blankTape)
      1 := by
  have hblank : Tape.StartInvariant (Tape.init ([] : List Γ)) := Tape.StartInvariant.init_nil
  have hinit : Tape.StartInvariant (Tape.init (x.map Γ.ofBool)) :=
    Tape.StartInvariant.init_ofBool x
  have hb : (⟨max (Tape.init ([] : List Γ)).head 1, (Tape.init ([] : List Γ)).cells⟩ : Tape)
      = TM.blankTape := by
    refine Tape.ext rfl (funext fun j => ?_)
    show (Tape.init ([] : List Γ)).cells j = _
    rw [TM.blankTape, Tape.move_cells]
  refine (TM.parkAll_hoareTime (Tape.init (x.map Γ.ofBool))
    (fun _ => Tape.init ([] : List Γ)) (Tape.init ([] : List Γ)) hinit (fun _ => hblank)
    hblank).strengthen_post ?_
  rintro inp work out ⟨hi, hw, ho⟩
  refine ⟨?_, by rw [funext hw]; exact funext fun _ => hb, by rw [ho]; exact hb⟩
  rw [hi]
  refine Tape.ext ?_ rfl
  show max (Tape.init (x.map Γ.ofBool)).head 1 = 1
  rw [Tape.init_head]
  omega


/-- The whole machine's running time. -/
def ppTime (k : ℕ) (tm : NTM k) (p : Polynomial ℕ) (x : List Bool) : ℕ :=
  1 + 1 + (prologueTime p x.length + 1 +
    ((2 ^ p.eval x.length) *
      (bodyTimeBound k (p.eval x.length) (2 ^ p.eval x.length) +
        testTimeBound (2 ^ p.eval x.length) + 5) + 1 +
      epilogueTime (2 ^ p.eval x.length)
        (tally (acceptsAt tm x (p.eval x.length)) (2 ^ p.eval x.length))
        (tally (fun u => !acceptsAt tm x (p.eval x.length) u) (2 ^ p.eval x.length))))

/-- **The counting machine's contract.** From its initial configuration it halts with the verdict
slot holding `1` exactly when the accepting paths outnumber the rejecting ones. -/
theorem ppMachine_hoareTime (k : ℕ) (tm : NTM k) (x : List Bool)
    (hne : tm.qstart ≠ tm.qhalt) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (p : Polynomial ℕ) (hT : 1 ≤ p.eval x.length) (hfT : f x.length ≤ p.eval x.length) :
    (ppMachine k tm p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init ([] : List Γ)) ∧ out = Tape.init ([] : List Γ))
      (fun _inp _work out => out = outSlot (TM.readBackWrite (Γ.ofBool
        (decide (tally (fun u => !acceptsAt tm x (p.eval x.length) u) (2 ^ p.eval x.length)
          < tally (acceptsAt tm x (p.eval x.length)) (2 ^ p.eval x.length))))))
      (ppTime k tm p x) := by
  set T := p.eval x.length with hTdef
  set N := 2 ^ T with hNdef
  set P := acceptsAt tm x T with hPdef
  have hIp : TM.Parked (bodyInput x) := bodyInput_parked x
  have hIsi : Tape.StartInvariant (bodyInput x) := bodyInput_startInvariant x
  have hIeq : bodyInput x = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) := bodyInput_eq x
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have htr : ∀ (W : Fin (bodyTapes k) → Tape) (O : Tape), (∀ j, TM.Parked (W j)) →
      TM.Parked O → ∀ inp work out, (inp = bodyInput x ∧ work = W ∧ out = O) →
        (TM.transitionInput inp = bodyInput x ∧
          (fun i => TM.transitionTape (work i)) = W ∧ TM.transitionTape out = O) := by
    rintro W O hW hO inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨TM.transitionInput_eq_self hIp.read_ne_start,
      funext fun i => TM.transitionTape_eq_self (hW i).read_ne_start,
      TM.transitionTape_eq_self hO.read_ne_start⟩
  -- The parking step, with the input tape named the way the rest of the machine names it.
  have p0 : (TM.skipTM (n := bodyTapes k)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init ([] : List Γ)) ∧ out = Tape.init ([] : List Γ))
      (fun inp work out => inp = bodyInput x ∧ work = (fun _ => TM.blankTape) ∧
        out = TM.blankTape) 1 :=
    (ppPark_hoareTime k x).strengthen_post
      (fun _ _ _ h => ⟨by rw [hIeq]; exact h.1, h.2.1, h.2.2⟩)
  -- The prologue, restated as the loop's precondition.
  have p1 : (prologueTM k p).HoareTime
      (fun inp work out => inp = bodyInput x ∧ work = (fun _ => TM.blankTape) ∧
        out = TM.blankTape)
      (tallyPre (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T)) P 0)
      (prologueTime p x.length) := by
    refine ((prologueTM_hoareTime k p x).weaken_pre ?_).strengthen_post ?_
    · rintro inp work out ⟨hi, hw, ho⟩
      exact ⟨by rw [← hIeq]; exact hi, hw, ho⟩
    · rintro inp work out ⟨hi, hw, ho⟩
      refine ⟨by rw [hIeq]; exact hi, hw, Γw.blank, by decide, ?_⟩
      rw [ho, outSlot_blank_eq_blankTape]
  -- The loop.
  have p2 := tallyLoop_full_bounded tm x hne hall T N hT hfT hN
  -- The epilogue, entered on the bank the loop leaves.
  have p3 : (epilogueTM k).HoareTime
      (tallyPost (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T)) P N N)
      (fun _inp _work out => out = outSlot (TM.readBackWrite (Γ.ofBool
        (decide (tally (fun u => !P u) N < tally P N)))))
      (epilogueTime N (tally P N) (tally (fun u => !P u) N)) := by
    refine (epilogueTM_hoareTime k N (1 + T) (tally P N) (tally (fun u => !P u) N)
      (bodyInput x) hIp hIsi).weaken_pre ?_
    rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, hw, by rw [ho, ite_eq_left rfl]⟩
  exact TM.seqTM_hoareTime _ _ p0
    (htr (fun _ => TM.blankTape) TM.blankTape (fun _ => TM.blankTape_parked)
      TM.blankTape_parked)
    (TM.seqTM_hoareTime _ _ p1
      (fun inp work out h => by
        obtain ⟨hi, hw, s, hs, ho⟩ := h
        refine ⟨?_, ?_, ?_⟩
        · rw [hi]; exact TM.transitionInput_eq_self hIp.read_ne_start
        · rw [hw]
          exact funext fun i =>
            TM.transitionTape_eq_self
              (bodyBank_parked k N (1 + T) 0 (tally P 0) (tally (fun u => !P u) 0) i).read_ne_start
        · refine ⟨s, hs, ?_⟩
          rw [ho]
          exact TM.transitionTape_eq_self (outSlot_parked s).read_ne_start)
      (TM.seqTM_hoareTime _ _ p2
        (fun inp work out h => by
          obtain ⟨hi, hw, ho⟩ := h
          refine ⟨?_, ?_, ?_⟩
          · rw [hi]; exact TM.transitionInput_eq_self hIp.read_ne_start
          · rw [hw]
            exact funext fun i =>
              TM.transitionTape_eq_self
                (bodyBank_parked k N (1 + T) N (tally P N)
                  (tally (fun u => !P u) N) i).read_ne_start
          · rw [ho]; exact TM.transitionTape_eq_self (outSlot_parked _).read_ne_start)
        p3))


/-- The counting loop's space bound, packaged as a conditional window contract so it can be
composed with the machine's other parts. -/
theorem tallyLoop_keepsWindowOn (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T N : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (hN : 1 ≤ N) :
    (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).KeepsWindowOn
      (fun c => c.state =
          (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart ∧
        tallyPre (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
          (acceptsAt tm x T) 0 c.input c.work c.output)
      x.length (1 + (bodyTimeBound k T N + testTimeBound N + 5)) := by
  intro c hc c' hreach
  obtain ⟨hstate, hpre⟩ := hc
  refine tallyLoop_keepsWindow_bounded tm x hne hall T N hT hfT hN c.input c.work c.output hpre
    c' ?_
  rwa [show (⟨(TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart,
    c.input, c.work, c.output⟩ : Cfg (bodyTapes k) _) = c from Cfg.ext hstate.symm rfl rfl rfl]


/-- The loop's starting configuration is inside any window at least one cell wide, and carries
its left markers. -/
theorem tallyPre_cfg_ok (k N H v a r : ℕ) (x : List Bool) (S : ℕ) (hS : 1 ≤ S)
    {Q : Type} (c : Cfg (bodyTapes k) Q)
    (h : c.input = bodyInput x ∧ c.work = bodyBank k N H v a r ∧
      ∃ s : Γw, s ≠ Γw.one ∧ c.output = outSlot s) :
    c.WithinDecisionSpace x.length S ∧ TM.CfgStartInvariant c := by
  obtain ⟨hi, hw, s, -, ho⟩ := h
  refine ⟨⟨⟨fun i => ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [hw, bodyBank_head]; omega
  · rw [hi, bodyInput_head]; omega
  · rw [ho]; show (1 : ℕ) ≤ S + 1; omega
  · rw [hi]; exact bodyInput_startInvariant x
  · intro i
    rw [hw]
    exact bodyBank_startInvariant k N H v a r i
  · rw [ho]
    exact ⟨rfl, fun j hj => (outSlot_parked s).2 j hj⟩


/-- **The loop and the epilogue, composed in space.** -/
theorem loopEpilogue_keepsWindowOn (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T N : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (hN : 1 ≤ N) (S : ℕ)
    (hS1 : 1 + (bodyTimeBound k T N + testTimeBound N + 5) ≤ S)
    (hS2 : 1 + epilogueTime N (tally (acceptsAt tm x T) N)
      (tally (fun u => !acceptsAt tm x T u) N) ≤ S) :
    (TM.seqTM (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)))
        (epilogueTM k)).KeepsWindowOn
      (fun c => ∃ d, (d.state =
          (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart ∧
          tallyPre (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T))
            (acceptsAt tm x T) 0 d.input d.work d.output) ∧
        c = TM.phase1Wrap _ (epilogueTM k) d)
      x.length S := by
  set P := acceptsAt tm x T with hP
  have hIp : TM.Parked (bodyInput x) := bodyInput_parked x
  have hIsi : Tape.StartInvariant (bodyInput x) := bodyInput_startInvariant x
  refine TM.seqTM_keepsWindowOn _ _ (by omega)
    (mid := tallyPost (cIdx k) (aIdx k) (rIdx k) (bodyInput x) (bodyRest k N (1 + T)) P N N) ?_
    ((tallyLoop_keepsWindowOn tm x hne hall T N hT hfT hN).mono_space hS1) ?_
    ((epilogueTM_keepsWindowOn k N (1 + T) (tally P N) (tally (fun u => !P u) N)
      x).mono_space hS2)
    ?_
  · rintro c ⟨hstate, hpre⟩
    exact ⟨hstate, tallyPre_cfg_ok k N (1 + T) 0 0 0 x S (by omega) c hpre⟩
  · rintro c ⟨hstate, hpre⟩
    obtain ⟨c', t, -, hreach, hhalt, hpost⟩ :=
      tallyLoop_full_bounded tm x hne hall T N hT hfT hN c.input c.work c.output hpre
    refine ⟨c', ?_, hhalt, hpost⟩
    rw [show (⟨(TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart,
      c.input, c.work, c.output⟩ : Cfg (bodyTapes k) _) = c from
      Cfg.ext hstate.symm rfl rfl rfl] at hreach
    exact TM.reaches_of_reachesIn hreach
  · rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hi]; exact TM.transitionInput_eq_self hIp.read_ne_start
    · rw [hw]
      exact funext fun i => TM.transitionTape_eq_self
        (bodyBank_parked k N (1 + T) N (tally P N) (tally (fun u => !P u) N) i).read_ne_start
    · rw [ho, ite_eq_left rfl]
      exact TM.transitionTape_eq_self (outSlot_parked Γw.one).read_ne_start


/-- **The prologue joined to the rest, in space.** -/
theorem prologueRest_keepsWindowOn (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (p : Polynomial ℕ) (T N : ℕ)
    (hTdef : T = p.eval x.length) (hNdef : N = 2 ^ T)
    (hT : 1 ≤ T) (hfT : f x.length ≤ T) (hN : 1 ≤ N) (S : ℕ)
    (hS0 : 1 + prologueTime p x.length ≤ S)
    (hS1 : 1 + (bodyTimeBound k T N + testTimeBound N + 5) ≤ S)
    (hS2 : 1 + epilogueTime N (tally (acceptsAt tm x T) N)
      (tally (fun u => !acceptsAt tm x T u) N) ≤ S) :
    (TM.seqTM (prologueTM k p)
        (TM.seqTM (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)))
          (epilogueTM k))).KeepsWindowOn
      (fun c => ∃ d, (d.state = (prologueTM k p).qstart ∧
          (d.input = bodyInput x ∧ d.work = (fun _ => TM.blankTape) ∧
            d.output = TM.blankTape)) ∧
        c = TM.phase1Wrap _ _ d)
      x.length S := by
  have hIp : TM.Parked (bodyInput x) := bodyInput_parked x
  have hIeq : bodyInput x = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) := bodyInput_eq x
  refine TM.seqTM_keepsWindowOn _ _ (by omega)
    (mid := fun inp work out => inp = bodyInput x ∧
      work = bodyBank k N (1 + T) 0 0 0 ∧ out = TM.blankTape) ?_
    (((prologueTM_keepsWindowOn k p x).mono
      (fun c hc => ⟨hc.1, by rw [← hIeq]; exact hc.2.1, hc.2.2.1, hc.2.2.2⟩)).mono_space hS0) ?_
    (loopEpilogue_keepsWindowOn tm x hne hall T N hT hfT hN S hS1 hS2) ?_
  · rintro c ⟨hstate, hi, hw, ho⟩
    refine ⟨hstate, ⟨⟨fun i => ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
    · rw [hw]; show (1 : ℕ) ≤ S; omega
    · rw [hi, bodyInput_head]; omega
    · rw [ho]; show (1 : ℕ) ≤ S + 1; omega
    · rw [hi]; exact bodyInput_startInvariant x
    · intro i; rw [hw]; exact TM.blankTape_startInvariant
    · rw [ho]; exact TM.blankTape_startInvariant
  · rintro c ⟨hstate, hi, hw, ho⟩
    obtain ⟨c', t, -, hreach, hhalt, hpi, hpw, hpo⟩ :=
      prologueTM_hoareTime k p x c.input c.work c.output
        ⟨by rw [hi, hIeq], hw, ho⟩
    refine ⟨c', ?_, hhalt, by rw [hpi, ← hIeq], by rw [hpw, hNdef, hTdef], hpo⟩
    rw [show (⟨(prologueTM k p).qstart, c.input, c.work, c.output⟩ :
      Cfg (bodyTapes k) _) = c from Cfg.ext hstate.symm rfl rfl rfl] at hreach
    exact TM.reaches_of_reachesIn hreach
  · rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨⟨(TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart,
      TM.transitionInput inp, fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, ?_, ?_, ?_⟩, rfl⟩
    · rw [hi]; exact TM.transitionInput_eq_self hIp.read_ne_start
    · rw [hw]
      exact funext fun i => TM.transitionTape_eq_self
        (bodyBank_parked k N (1 + T) 0 0 0 i).read_ne_start
    · refine ⟨Γw.blank, by decide, ?_⟩
      rw [ho, TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start,
        outSlot_blank_eq_blankTape]


/-- **The whole machine keeps a polynomial window.** Every configuration it reaches from its
initial one fits inside `S` cells. -/
theorem ppMachine_keepsWindow (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (p : Polynomial ℕ) (T N : ℕ)
    (hTdef : T = p.eval x.length) (hNdef : N = 2 ^ T)
    (hT : 1 ≤ T) (hfT : f x.length ≤ T) (hN : 1 ≤ N) (S : ℕ) (hS : 1 ≤ S)
    (hS0 : 1 + prologueTime p x.length ≤ S)
    (hS1 : 1 + (bodyTimeBound k T N + testTimeBound N + 5) ≤ S)
    (hS2 : 1 + epilogueTime N (tally (acceptsAt tm x T) N)
      (tally (fun u => !acceptsAt tm x T u) N) ≤ S) :
    ∀ c', (ppMachine k tm p).reaches ((ppMachine k tm p).initCfg x) c' →
      c'.WithinDecisionSpace x.length S := by
  have hIeq : bodyInput x = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) := bodyInput_eq x
  have hpark : (TM.skipTM (n := bodyTapes k)).KeepsWindowOn
      (fun c => c.state = (TM.skipTM (n := bodyTapes k)).qstart ∧
        (c.input = Tape.init (x.map Γ.ofBool) ∧
          c.work = (fun _ => Tape.init ([] : List Γ)) ∧
          c.output = Tape.init ([] : List Γ))) x.length S :=
    (TM.keepsWindowOn_of_hoareTime_pinned (h₀ := 0) (ppPark_hoareTime k x)
      (fun _ => le_of_eq rfl) (by show (0 : ℕ) ≤ x.length + 0 + 1; omega)
      (by show (0 : ℕ) ≤ 0 + 1; omega)).mono_space (by omega)
  have hcomp := TM.seqTM_keepsWindowOn (TM.skipTM (n := bodyTapes k))
    (TM.seqTM (prologueTM k p)
      (TM.seqTM (TM.loopTM (bodyTM tm) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)))
        (epilogueTM k))) hS
    (mid := fun inp work out => inp = bodyInput x ∧ work = (fun _ => TM.blankTape) ∧
      out = TM.blankTape)
    (fun c hc => ⟨hc.1, ⟨⟨fun i => by rw [hc.2.2.1]; show (0 : ℕ) ≤ S; omega,
        by rw [hc.2.1]; show (0 : ℕ) ≤ x.length + S + 1; omega⟩,
        by rw [hc.2.2.2]; show (0 : ℕ) ≤ S + 1; omega⟩,
      by rw [hc.2.1]; exact Tape.StartInvariant.init_ofBool x,
      fun i => by rw [hc.2.2.1]; exact Tape.StartInvariant.init_nil,
      by rw [hc.2.2.2]; exact Tape.StartInvariant.init_nil⟩)
    hpark
    (fun c hc => by
      obtain ⟨hstate, hi, hw, ho⟩ := hc
      obtain ⟨c', t, -, hreach, hhalt, hpi, hpw, hpo⟩ :=
        ppPark_hoareTime k x c.input c.work c.output ⟨hi, hw, ho⟩
      refine ⟨c', ?_, hhalt, by rw [hpi, ← hIeq], hpw, hpo⟩
      rw [show (⟨(TM.skipTM (n := bodyTapes k)).qstart, c.input, c.work, c.output⟩ :
        Cfg (bodyTapes k) _) = c from Cfg.ext hstate.symm rfl rfl rfl] at hreach
      exact TM.reaches_of_reachesIn hreach)
    (prologueRest_keepsWindowOn tm x hne hall p T N hTdef hNdef hT hfT hN S hS0 hS1 hS2)
    (fun inp work out h => by
      obtain ⟨hi, hw, ho⟩ := h
      refine ⟨⟨(prologueTM k p).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩, ⟨rfl, ?_, ?_, ?_⟩, rfl⟩
      · rw [hi]
        exact TM.transitionInput_eq_self (bodyInput_parked x).read_ne_start
      · rw [hw]
        exact funext fun i =>
          TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start
      · rw [ho]
        exact TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start)
  intro c' hreach
  exact hcomp ((ppMachine k tm p).initCfg x)
    ⟨⟨(TM.skipTM (n := bodyTapes k)).qstart, Tape.init (x.map Γ.ofBool),
      fun _ => Tape.init ([] : List Γ), Tape.init ([] : List Γ)⟩,
      ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ c' hreach


/-- **The horizon's width is the exponent plus one.** Every bound the machine's parts state in
terms of the horizon's number of digits is therefore a bound in terms of the exponent — which is
what makes them polynomial in the input length rather than exponential. -/
theorem size_horizon (T : ℕ) : (2 ^ T).size = T + 1 := Nat.size_pow

theorem bits_length_horizon (T : ℕ) : (2 ^ T).bits.length = T + 1 :=
  (Nat.size_eq_bits_len (2 ^ T)).trans (size_horizon T)


/-- The Horner cap, as a polynomial. The space bound the surrounding obligation asks for must be
a `Polynomial ℕ`, so each arithmetic expression the machine's parts are bounded by has to be
mirrored by a polynomial whose evaluation reproduces it. -/
noncomputable def capPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C ((TM.polyCoeffs p).sum + 1) * (Polynomial.X + 1) ^ (TM.polyCoeffs p).length

@[simp] theorem capPoly_eval (p : Polynomial ℕ) (n : ℕ) :
    (capPoly p).eval n = prologueCap p n := by
  simp only [capPoly, prologueCap, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

/-- The operation budget, as a polynomial. -/
noncomputable def opBudgetPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 32 * ((capPoly p + Polynomial.C 2) ^ 3)

@[simp] theorem opBudgetPoly_eval (p : Polynomial ℕ) (n : ℕ) :
    (opBudgetPoly p).eval n = TM.opBudget (prologueCap p n) := by
  simp only [opBudgetPoly, TM.opBudget, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, capPoly_eval]
  ring

/-- The layer budget, as a polynomial. -/
noncomputable def layerBudgetPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 4 * opBudgetPoly p + Polynomial.C 3

@[simp] theorem layerBudgetPoly_eval (p : Polynomial ℕ) (n : ℕ) :
    (layerBudgetPoly p).eval n = TM.layerBudget (prologueCap p n) := by
  simp only [layerBudgetPoly, TM.layerBudget, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, opBudgetPoly_eval]

/-- The predecessor of the horizon has exactly `T` digits, all of them ones. -/
theorem size_horizon_pred (T : ℕ) : (2 ^ T - 1).size = T := by
  rw [← Nat.size_eq_bits_len (2 ^ T - 1), bits_two_pow_sub_one, List.length_replicate]

theorem binarySuccTime_horizon_pred (T : ℕ) :
    TM.binarySuccTime (2 ^ T - 1) ≤ 2 * T + 2 := by
  have h := TM.binarySuccTime_le (2 ^ T - 1)
  rw [size_horizon_pred] at h
  exact h

/-- The prologue's running time, as a polynomial. Only a bound is possible — the running time
involves `max`, which no polynomial reproduces — so the maxima are replaced by sums. -/
noncomputable def prologueTimePoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 5 *
    ((Polynomial.C 2 * Polynomial.X + Polynomial.C 4) +
      (opBudgetPoly p + Polynomial.C 1 +
        (Polynomial.C (p.natDegree + 1) * (layerBudgetPoly p + Polynomial.C 1) +
          Polynomial.C 1)) +
      (Polynomial.C 2 * p + Polynomial.C 2) +
      ((Polynomial.C 2 * p + Polynomial.C 4) +
        (Polynomial.C 2 * Polynomial.X + Polynomial.C 4)) + Polynomial.C 1) + Polynomial.C 1

theorem prologueTime_le (p : Polynomial ℕ) (n : ℕ) :
    prologueTime p n ≤ (prologueTimePoly p).eval n := by
  have hsucc := binarySuccTime_horizon_pred (p.eval n)
  have hev : (prologueTimePoly p).eval n
      = 5 * ((2 * n + 4) +
        (TM.opBudget (prologueCap p n) + 1 +
          ((p.natDegree + 1) * (TM.layerBudget (prologueCap p n) + 1) + 1)) +
        (2 * p.eval n + 2) + ((2 * p.eval n + 4) + (2 * n + 4)) + 1) + 1 := by
    simp only [prologueTimePoly, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, opBudgetPoly_eval, layerBudgetPoly_eval]
  rw [hev, prologueTime]
  have hmax : ∀ a b : ℕ, max a b ≤ a + b := fun a b => by omega
  have h1 := hmax (2 * n + 4)
    (TM.opBudget (prologueCap p n) + 1 +
      ((p.natDegree + 1) * (TM.layerBudget (prologueCap p n) + 1) + 1))
  have h2 := hmax (max (2 * n + 4)
      (TM.opBudget (prologueCap p n) + 1 +
        ((p.natDegree + 1) * (TM.layerBudget (prologueCap p n) + 1) + 1)))
    (TM.binarySuccTime (2 ^ p.eval n - 1))
  have h3 := hmax (max (max (2 * n + 4)
      (TM.opBudget (prologueCap p n) + 1 +
        ((p.natDegree + 1) * (TM.layerBudget (prologueCap p n) + 1) + 1)))
      (TM.binarySuccTime (2 ^ p.eval n - 1)))
    (max (2 * p.eval n + 4) (2 * n + 4))
  have h4 := hmax (2 * p.eval n + 4) (2 * n + 4)
  omega


/-- **A tally has no more digits than its horizon.** Every time bound the epilogue states in
terms of the tallies' widths is therefore a bound in terms of the exponent. -/
theorem tally_size_le (P : ℕ → Bool) (N : ℕ) : (tally P N).size ≤ N.size :=
  Nat.size_le_size (tally_le P N)

theorem tally_size_horizon_le (P : ℕ → Bool) (T : ℕ) :
    (tally P (2 ^ T)).size ≤ T + 1 := by
  have h := tally_size_le P (2 ^ T)
  rw [size_horizon] at h
  exact h

/-- One more than a tally still has no more than one extra digit. -/
theorem tally_succ_size_horizon_le (P : ℕ → Bool) (T : ℕ) :
    (tally P (2 ^ T) + 1).size ≤ T + 2 := by
  have h1 : tally P (2 ^ T) + 1 ≤ 2 ^ (T + 1) := by
    have := tally_le P (2 ^ T)
    have h2 : 2 ^ (T + 1) = 2 * 2 ^ T := by ring
    have h3 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
    omega
  have h := Nat.size_le_size h1
  rw [size_horizon] at h
  omega


/-- **The loop's window is linear in the exponent.** Its width is stated through the digit counts
of the horizon and of the two tallies; each of those is `T + O(1)`, so the width is too — even
though the horizon itself is `2 ^ T`. -/
theorem loopWidth_le (k T : ℕ) :
    1 + (bodyTimeBound k T (2 ^ T) + testTimeBound (2 ^ T) + 5)
      ≤ 2 * ((wipeTargets k).length * (T + 5)) + (40 * T + 300) := by
  unfold bodyTimeBound testTimeBound testB
  rw [size_horizon, bits_length_horizon]
  simp only [TM.resetBinaryWorkTime, TM.clearWorkTimeBound]
  have hL : (wipeTargets k).length * (1 + T + 4) = (wipeTargets k).length * (T + 5) := by
    congr 1
    omega
  rw [hL]
  omega


/-- **The epilogue's window is linear in the exponent too.** Its cost is stated through the digit
counts of the two tallies and of their difference, all of which are `T + O(1)`. -/
theorem epilogueWidth_le (T : ℕ) (P : ℕ → Bool) :
    1 + epilogueTime (2 ^ T) (tally P (2 ^ T)) (tally (fun u => !P u) (2 ^ T))
      ≤ 40 * T + 200 := by
  set a := tally P (2 ^ T) with ha'
  set r := tally (fun u => !P u) (2 ^ T) with hr'
  have ha : a.size ≤ T + 1 := tally_size_horizon_le P T
  have hr : r.size ≤ T + 1 := tally_size_horizon_le _ T
  have hr1 : (r + 1).size ≤ T + 2 := tally_succ_size_horizon_le _ T
  have hsucc : TM.binarySuccTime r ≤ 2 * r.size + 2 := TM.binarySuccTime_le r
  have hsub : TM.binaryRippleSubTime (r + 1) a ≤ 3 * ((r + 1).size + a.size) + 10 :=
    TM.binaryRippleSubTime_le _ _
  have hdiff : ((r + 1) - a).size ≤ T + 2 :=
    le_trans (Nat.size_le_size (by omega)) hr1
  have hbitsz : ((r + 1) - a).bits.length ≤ T + 2 := by
    rw [Nat.size_eq_bits_len ((r + 1) - a)]
    exact hdiff
  have hzero : (0 : ℕ).bits.length = 0 := by simp
  have heq : TM.binaryEqTime ((r + 1) - a).bits (0 : ℕ).bits ≤ T + 3 := by
    show max ((r + 1 - a).bits.length) ((0 : ℕ).bits.length) + 1 ≤ T + 3
    rw [hzero]
    omega
  unfold epilogueTime
  simp only [TM.resetBinaryWorkTime, TM.clearWorkTimeBound, bits_length_horizon]
  omega


/-- **The machine's space bound, as a polynomial.** The sum of the three parts' widths: the
prologue's, the loop's, and the epilogue's. -/
noncomputable def ppSpacePoly (k : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  prologueTimePoly p +
    (Polynomial.C (2 * (wipeTargets k).length) * (p + Polynomial.C 5) +
      Polynomial.C 40 * p + Polynomial.C 300) +
    (Polynomial.C 40 * p + Polynomial.C 200)

theorem ppSpacePoly_eval (k : ℕ) (p : Polynomial ℕ) (n : ℕ) :
    (ppSpacePoly k p).eval n
      = (prologueTimePoly p).eval n +
        (2 * (wipeTargets k).length * (p.eval n + 5) + 40 * p.eval n + 300) +
        (40 * p.eval n + 200) := by
  simp only [ppSpacePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

theorem prologue_le_ppSpacePoly (k : ℕ) (p : Polynomial ℕ) (n : ℕ) :
    1 + prologueTime p n ≤ (ppSpacePoly k p).eval n := by
  have h := prologueTime_le p n
  rw [ppSpacePoly_eval]
  omega

theorem loop_le_ppSpacePoly (k : ℕ) (p : Polynomial ℕ) (n : ℕ) :
    1 + (bodyTimeBound k (p.eval n) (2 ^ p.eval n) +
      testTimeBound (2 ^ p.eval n) + 5) ≤ (ppSpacePoly k p).eval n := by
  have h := loopWidth_le k (p.eval n)
  have hmul : 2 * (wipeTargets k).length * (p.eval n + 5)
      = 2 * ((wipeTargets k).length * (p.eval n + 5)) := by ring
  rw [ppSpacePoly_eval, hmul]
  omega

theorem epilogue_le_ppSpacePoly (k : ℕ) (p : Polynomial ℕ) (n : ℕ) (P : ℕ → Bool) :
    1 + epilogueTime (2 ^ p.eval n) (tally P (2 ^ p.eval n))
      (tally (fun u => !P u) (2 ^ p.eval n)) ≤ (ppSpacePoly k p).eval n := by
  have h := epilogueWidth_le (p.eval n) P
  rw [ppSpacePoly_eval]
  omega


/-- The comparison the surrounding obligation names: after `2 ^ p |x|` tally steps, does the
accepting component exceed the rejecting one? -/
def ppCond (tm : NTM k) (p : Polynomial ℕ) (x : List Bool) : Prop :=
  ((tallyStep fun v => acceptsAt tm x (p.eval x.length) v)^[2 ^ p.eval x.length] (0, 0, 0)).2.2 <
    ((tallyStep fun v => acceptsAt tm x (p.eval x.length) v)^[2 ^ p.eval x.length] (0, 0, 0)).2.1

/-- **The counting machine decides the `PP` comparison.** It runs at the horizon `p.eval |x| + 1`
— one more than the specification names, so that the horizon is never zero, which the simulation
needs — and `NTM.cmp_horizon_iff'` says the comparison is the same either way. -/
theorem ppMachine_decides (k : ℕ) (tm : NTM k) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (p : Polynomial ℕ) (hle : ∀ n, f n ≤ p.eval n) (hne : tm.qstart ≠ tm.qhalt)
    (x : List Bool) :
    ∃ c', (ppMachine k tm (p + 1)).reaches ((ppMachine k tm (p + 1)).initCfg x) c' ∧
      (ppMachine k tm (p + 1)).halted c' ∧
      (ppCond tm p x → c'.output.cells 1 = Γ.one) ∧
      (¬ ppCond tm p x → c'.output.cells 1 = Γ.zero) := by
  set T := (p + 1).eval x.length with hT'
  have hTval : T = p.eval x.length + 1 := by
    rw [hT']
    simp
  have hT : 1 ≤ T := by omega
  have hfT : f x.length ≤ T := by
    have := hle x.length
    omega
  obtain ⟨c', t, -, hreach, hhalt, hout⟩ :=
    ppMachine_hoareTime k tm x hne hall (p + 1) hT hfT
      (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init ([] : List Γ))
      (Tape.init ([] : List Γ)) ⟨rfl, rfl, rfl⟩
  have hiff : (tally (fun u => !acceptsAt tm x T u) (2 ^ T) <
      tally (fun u => acceptsAt tm x T u) (2 ^ T)) ↔ ppCond tm p x := by
    rw [ppCond, tallyStep_iterate, tally_cmp_iff, tally_cmp_iff]
    exact cmp_horizon_iff' tm hall x T (p.eval x.length) hfT (hle x.length)
  refine ⟨c', TM.reaches_of_reachesIn hreach, hhalt, ?_, ?_⟩
  · intro hcond
    rw [hout, outSlot_cells_one, decide_eq_true_iff.mpr (hiff.mpr hcond)]
    rfl
  · intro hcond
    rw [hout, outSlot_cells_one,
      show decide (tally (fun u => !acceptsAt tm x T u) (2 ^ T) <
        tally (fun u => acceptsAt tm x T u) (2 ^ T)) = false from by
        simp only [decide_eq_false_iff_not]
        exact fun hc => hcond (hiff.mp hc)]
    rfl


/-- **The counting machine runs in polynomial space.** Every configuration it reaches fits inside
`NTM.ppSpacePoly` cells — a polynomial in the input length, even though the machine's own running
time is exponential. -/
theorem ppMachine_space (k : ℕ) (tm : NTM k) {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f)
    (p : Polynomial ℕ) (hle : ∀ n, f n ≤ p.eval n) (hne : tm.qstart ≠ tm.qhalt)
    (x : List Bool) (c' : Cfg (bodyTapes k) (ppMachine k tm (p + 1)).Q)
    (hreach : (ppMachine k tm (p + 1)).reaches ((ppMachine k tm (p + 1)).initCfg x) c') :
    c'.WithinDecisionSpace x.length ((ppSpacePoly k (p + 1)).eval x.length) := by
  set T := (p + 1).eval x.length with hT'
  have hTval : T = p.eval x.length + 1 := by
    rw [hT']
    simp
  have hT : 1 ≤ T := by omega
  have hfT : f x.length ≤ T := by
    have := hle x.length
    omega
  have hN : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  have hS0 := prologue_le_ppSpacePoly k (p + 1) x.length
  have hS1 := loop_le_ppSpacePoly k (p + 1) x.length
  have hS2 := epilogue_le_ppSpacePoly k (p + 1) x.length (acceptsAt tm x T)
  exact ppMachine_keepsWindow tm x hne hall (p + 1) T (2 ^ T) rfl rfl hT hfT hN
    ((ppSpacePoly k (p + 1)).eval x.length) (by omega) hS0 hS1 hS2 c' hreach


/-- **Two is the smallest numeral whose low digit is zero.** A blank register incremented twice
therefore reads `0`, which is how the trivial machine below produces a `0` to publish — the
alphabet offers no other way to name one. -/
theorem natTape_two_read : (natTape 2).read = Γ.zero := by
  show ((Tape.init ((Nat.bits 2).map Γ.ofBool)).move Dir3.right).cells 1 = Γ.zero
  rw [Tape.move_cells, show Nat.bits 2 = [false, true] from by decide]
  show (Tape.init (([false, true] : List Bool).map Γ.ofBool)).cells (0 + 1) = Γ.zero
  rw [Tape.init_ofBool_cells_lt [false, true] 0 (by simp)]
  rfl

/-- **The trivial machine**: it writes `0` and halts. This is what serves for a source machine
that starts halted, where no path can accept and the comparison is always false. -/
def zeroTM (k : ℕ) : TM (bodyTapes k) :=
  TM.seqTM TM.skipTM
    (TM.bigSeqTM [TM.binarySuccTM (cIdx k), TM.binarySuccTM (cIdx k),
      TM.writeOutputBitTM (cIdx k)])

/-- The trivial machine's running time. -/
def zeroTime : ℕ :=
  1 + 1 + (3 * (max (max (TM.binarySuccTime 0) (TM.binarySuccTime 1)) 1 + 1) + 1)

/-- **The trivial machine's contract.** It halts with `0` in the verdict slot. -/
theorem zeroTM_hoareTime (k : ℕ) (x : List Bool) :
    (zeroTM k).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init ([] : List Γ)) ∧ out = Tape.init ([] : List Γ))
      (fun _inp _work out => out = outSlot Γw.zero)
      zeroTime := by
  set I : Tape := (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) with hI
  have hIp : TM.Parked I := by rw [hI, ← bodyInput_eq]; exact bodyInput_parked x
  set V0 : Fin (bodyTapes k) → Tape := fun _ => TM.blankTape with hV0
  set V1 : Fin (bodyTapes k) → Tape := Function.update V0 (cIdx k) (natTape 1) with hV1
  set V2 : Fin (bodyTapes k) → Tape := Function.update V1 (cIdx k) (natTape 2) with hV2
  have hupd : ∀ (W : Fin (bodyTapes k) → Tape) (i : Fin (bodyTapes k)) (t : Tape),
      (∀ j, TM.Parked (W j)) → TM.Parked t → ∀ j, TM.Parked (Function.update W i t j) := by
    intro W i t hW ht j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact ht
    · rw [Function.update_of_ne hj]; exact hW j
  have hV0P : ∀ j, TM.Parked (V0 j) := fun _ => TM.blankTape_parked
  have hV1P : ∀ j, TM.Parked (V1 j) := hupd _ _ _ hV0P (natTape_parked _)
  have hV2P : ∀ j, TM.Parked (V2 j) := hupd _ _ _ hV1P (natTape_parked _)
  set b := max (max (TM.binarySuccTime 0) (TM.binarySuccTime 1)) 1 with hb
  have hrest : (TM.bigSeqTM [TM.binarySuccTM (cIdx k), TM.binarySuccTM (cIdx k),
      TM.writeOutputBitTM (cIdx k)]).HoareTime
      (fun inp work out => inp = I ∧ work = V0 ∧ out = TM.blankTape)
      (fun inp work out => inp = I ∧ work = V2 ∧ out = outSlot Γw.zero)
      (3 * (b + 1) + 1) := by
    refine (TM.bigSeqTM_hoareTime_pinned _ I
      (fun j => if j = 0 then V0 else if j = 1 then V1 else V2)
      (fun j => if j ≤ 2 then TM.blankTape else outSlot Γw.zero) b hIp ?_ ?_ ?_).consequence
      (fun _ _ _ h => h) (fun _ _ _ h => h) (le_refl _)
    · intro j i
      split
      · exact hV0P i
      · split
        · exact hV1P i
        · exact hV2P i
    · intro j
      split
      · exact TM.blankTape_parked
      · exact outSlot_parked _
    · intro j hj
      match j, hj with
      | 0, _ =>
        show (TM.binarySuccTM (cIdx k)).HoareTime _ _ _
        exact (TM.binarySuccTM_hoareTime_pinned (cIdx k) 0 I V0 TM.blankTape
          (by rw [hV0, natTape_zero]) hIp.read_ne_start (fun i _ => (hV0P i).read_ne_start)
          TM.blankTape_parked.read_ne_start).mono_bound
          (le_trans (le_max_left _ _) (le_max_left _ _))
      | 1, _ =>
        show (TM.binarySuccTM (cIdx k)).HoareTime _ _ _
        exact (TM.binarySuccTM_hoareTime_pinned (cIdx k) 1 I V1 TM.blankTape
          (by rw [hV1, Function.update_self]) hIp.read_ne_start
          (fun i _ => (hV1P i).read_ne_start)
          TM.blankTape_parked.read_ne_start).mono_bound
          (le_trans (le_max_right _ _) (le_max_left _ _))
      | 2, _ =>
        show (TM.writeOutputBitTM (cIdx k)).HoareTime _ _ _
        refine ((TM.writeOutputBitTM_hoareTime_frame (cIdx k) I V2 TM.blankTape hIp hV2P
          TM.blankTape_parked).strengthen_post ?_).mono_bound (le_max_right _ _)
        rintro inp work out ⟨hi, hw, ho⟩
        refine ⟨hi, hw, ?_⟩
        rw [ho, show V2 (cIdx k) = natTape 2 from by rw [hV2, Function.update_self],
          natTape_two_read, ← outSlot_blank_eq_blankTape]
        exact outSlot_write Γw.blank Γw.zero
  have hpark : (TM.skipTM (n := bodyTapes k)).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init ([] : List Γ)) ∧ out = Tape.init ([] : List Γ))
      (fun inp work out => inp = I ∧ work = V0 ∧ out = TM.blankTape) 1 :=
    ppPark_hoareTime k x
  have htrans : ∀ inp work out, (inp = I ∧ work = V0 ∧ out = TM.blankTape) →
      (TM.transitionInput inp = I ∧ (fun i => TM.transitionTape (work i)) = V0 ∧
        TM.transitionTape out = TM.blankTape) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨TM.transitionInput_eq_self hIp.read_ne_start,
      funext fun i => TM.transitionTape_eq_self (hV0P i).read_ne_start,
      TM.transitionTape_eq_self TM.blankTape_parked.read_ne_start⟩
  exact (TM.seqTM_hoareTime _ _ hpark htrans hrest).strengthen_post (fun _ _ _ h => h.2.2)

/-- The trivial machine's space bound, as a polynomial: a constant. -/
noncomputable def zeroSpacePoly : Polynomial ℕ := Polynomial.C zeroTime

@[simp] theorem zeroSpacePoly_eval (n : ℕ) : zeroSpacePoly.eval n = zeroTime := by
  simp [zeroSpacePoly]

/-- **The trivial machine keeps a constant window.** Its running time is constant, so the heads
cannot travel far enough to leave one. -/
theorem zeroTM_space (k : ℕ) (x : List Bool) (c' : Cfg (bodyTapes k) (zeroTM k).Q)
    (hreach : (zeroTM k).reaches ((zeroTM k).initCfg x) c') :
    c'.WithinDecisionSpace x.length (zeroSpacePoly.eval x.length) := by
  have h := TM.keepsWindowOn_of_hoareTime_pinned (h₀ := 0) (inputLength := x.length)
    (zeroTM_hoareTime k x) (fun _ => le_of_eq rfl)
    (by show (0 : ℕ) ≤ x.length + 0 + 1; omega) (by show (0 : ℕ) ≤ 0 + 1; omega)
  have hw := h ((zeroTM k).initCfg x) ⟨rfl, rfl, rfl, rfl⟩ c' hreach
  rw [zeroSpacePoly_eval]
  exact (by simpa using hw : c'.WithinDecisionSpace x.length (0 + zeroTime))

/-- **The trivial machine publishes `0`.** -/
theorem zeroTM_decides (k : ℕ) (x : List Bool) :
    ∃ c', (zeroTM k).reaches ((zeroTM k).initCfg x) c' ∧ (zeroTM k).halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  obtain ⟨c', t, -, hreach, hhalt, hout⟩ :=
    zeroTM_hoareTime k x (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init ([] : List Γ))
      (Tape.init ([] : List Γ)) ⟨rfl, rfl, rfl⟩
  exact ⟨c', TM.reaches_of_reachesIn hreach, hhalt, by rw [hout, outSlot_cells_one]; rfl⟩

/-- **A source that starts halted fails the comparison.** No path accepts, so the accepting tally
is zero and cannot exceed the rejecting one — which is why the trivial machine, publishing `0`
unconditionally, decides this case. -/
theorem not_ppCond_of_qstart_eq_qhalt (k : ℕ) (tm : NTM k) (heq : tm.qstart = tm.qhalt)
    (p : Polynomial ℕ) (x : List Bool) : ¬ ppCond tm p x := by
  rw [ppCond, tallyStep_iterate]
  show ¬ (tally (fun v => !acceptsAt tm x (p.eval x.length) v) (2 ^ p.eval x.length) <
    tally (fun v => acceptsAt tm x (p.eval x.length) v) (2 ^ p.eval x.length))
  rw [tally_eq_acceptCount, acceptCount_eq_zero_of_qstart_eq_qhalt heq]
  omega


end NTM

end Complexity

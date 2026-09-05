/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PPParts
public import Complexitylib.Models.TuringMachine.Placement
public import Complexitylib.Models.TuringMachine.Lift
public import Complexitylib.Models.TuringMachine.Subroutines.WipeRewind

/-!
# The counting loop's simulation stage

⚠️ Unreviewed by Bolton

The loop body runs one path of the source machine and reads off whether it accepts. Three
wrappers turn that simulation into something a composed machine can use as a stage:

* `TM.startedTM` moves the start state past the compulsory `▷`-step, because no stage of a
  composed machine can be entered with a head at cell zero;
* `TM.placeWorkTM 0 m` sets the simulation's tapes beside the loop's own registers, with an
  *exact* frame — the registers come back untouched;
* `TM.retargetOutput` sends the verdict to a work tape instead of the real output tape, which
  has to stay blank for the wipe that follows.

None of the three costs a step, and none of them disturbs the others' tapes, so a run of the
simulation transports to a run of the stage of exactly the same length.

## Main results

- `NTM.simTM` — the simulation as a stage of the counting machine
- `NTM.simTM_reachesIn` — a run of the simulation is a run of the stage
- `NTM.simTM_verdict_tape` — the verdict lands on the stage's last work tape
- `NTM.simTM_run` — the stage run to a halt, with the acceptance bit of path `v`
- `NTM.simEntry`, `NTM.simEntry_dropChoice` — the configuration the stage is entered at
- `NTM.simTM_frame` — the invariants and head bounds the stage leaves behind
- `NTM.simCfg_work_middle`, `NTM.simCfg_work_extra`, `NTM.simCfg_counter_cells` — where each of
  the stage's tapes comes from
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ}

/-- The path simulator, entered after its sentinel step. -/
def simCore (tm : NTM k) : TM (k + 1) :=
  TM.startedTM (choiceTM (delayNTM tm))

/-- **The simulation as a stage of the counting machine.** Its tapes are the source machine's
`k` work tapes and the choice tape — which is the loop's counter — followed by `m` registers of
the loop's own and, last, the tape the verdict is written to. -/
def simTM (tm : NTM k) (m : ℕ) : TM (0 + (k + 1) + m + 1) :=
  (TM.placeWorkTM 0 m (simCore tm)).retargetOutput

/-- The stage's entry configuration: the simulation's own configuration, placed beside the
loop's registers, with the real output tape blank. -/
def simCfg (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    (c : Cfg (k + 1) (simCore tm).Q) : Cfg (0 + (k + 1) + m + 1) (simTM tm m).Q :=
  (TM.placeWorkTM 0 m (simCore tm)).retargetCfg
    (TM.placeWorkCfg (simCore tm) 0 m extras c)

/-- **A run of the simulation is a run of the stage**, of exactly the same length. The loop's
registers need only carry their left marker and be parked; they are returned untouched. -/
theorem simTM_reachesIn (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    (hinv : ∀ i, ¬ TM.placeWorkInMiddle 0 (k + 1) i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ TM.placeWorkInMiddle 0 (k + 1) i → 1 ≤ (extras i).head)
    {t : ℕ} {c c' : Cfg (k + 1) (simCore tm).Q}
    (h : (simCore tm).reachesIn t c c') :
    (simTM tm m).reachesIn t (simCfg tm m extras c) (simCfg tm m extras c') :=
  TM.retargetOutput_reachesIn_retargetCfg_frame _
    (TM.placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant (simCore tm) 0 m extras h
      hinv hhead)

/-- The verdict lands on the stage's last work tape — the one `TM.retargetOutput` redirects the
simulation's output to. -/
theorem simTM_verdict_tape (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    (c : Cfg (k + 1) (simCore tm).Q) :
    (simCfg tm m extras c).work (Fin.last (0 + (k + 1) + m)) = c.output :=
  TM.retargetCfg_work_last _ _

/-- The stage leaves the real output tape blank and parked, which is what the wipe that follows
the simulation requires. -/
theorem simTM_output (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    (c : Cfg (k + 1) (simCore tm).Q) :
    (simCfg tm m extras c).output = (Tape.init ([] : List Γ)).move Dir3.right := rfl

/-- The stage's start state is the simulation's, so a run of the stage from `simCfg` is a run
from the stage machine's own start state. -/
theorem simTM_qstart (tm : NTM k) (m : ℕ) : (simTM tm m).qstart = (simCore tm).qstart := rfl


/-- **The simulation stage, run to a halt with its verdict.** From an entry configuration whose
counter carries `v` and whose simulated tapes are the delayed machine's post-sentinel ones, the
stage halts within the horizon, leaves the loop's registers exactly as it found them, and writes
the acceptance bit of path `v` onto its last work tape. -/
theorem simTM_run (tm : NTM k) (x : List Bool) (hne : tm.qstart ≠ tm.qhalt)
    {f : ℕ → ℕ} (hall : tm.AllPathsHaltIn f) (T v : ℕ) (hT : 1 ≤ T) (hfT : f x.length ≤ T)
    (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    (hinv : ∀ i, ¬ TM.placeWorkInMiddle 0 (k + 1) i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬ TM.placeWorkInMiddle 0 (k + 1) i → 1 ≤ (extras i).head)
    (c : Cfg (k + 1) (simCore tm).Q)
    (hdrop : dropChoice c
      = (delayNTM tm).trace 1 (fun _ => false) ((delayNTM tm).initCfg x))
    (hv : (c.work (Fin.last k)).HasBinaryNat v) :
    ∃ (c' : Cfg (k + 1) (simCore tm).Q) (t : ℕ), t ≤ T ∧
      (simCore tm).reachesIn t c c' ∧
      (simTM tm m).reachesIn t (simCfg tm m extras c) (simCfg tm m extras c') ∧
      (simTM tm m).halted (simCfg tm m extras c') ∧
      decide (((simCfg tm m extras c').work
        (Fin.last (0 + (k + 1) + m))).cells 1 = Γ.one) = acceptsAt tm x T v := by
  obtain ⟨c', t, hle, hreach, hhalt, hverdict⟩ :=
    choiceTM_delay_haltsIn tm x hne hall T v hT hfT c hdrop hv
  refine ⟨c', t, hle, TM.reachesIn_startedTM _ hreach,
    simTM_reachesIn tm m extras hinv hhead (TM.reachesIn_startedTM _ hreach), hhalt, ?_⟩
  rw [simTM_verdict_tape tm m extras c']
  exact hverdict


/-- **The simulation's entry configuration.** The delayed machine's post-sentinel state: every
head at cell one, the machine's own tapes blank, and the counter carrying `v`. -/
def simEntry (tm : NTM k) (x : List Bool) (v : ℕ) : Cfg (k + 1) (simCore tm).Q where
  state := (simCore tm).qstart
  input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
  work := fun i => if i.val < k then TM.blankTape else natTape v
  output := TM.blankTape

theorem simEntry_counter (tm : NTM k) (x : List Bool) (v : ℕ) :
    (simEntry tm x v).work (Fin.last k) = natTape v := by
  show (if (Fin.last k).val < k then TM.blankTape else natTape v) = _
  rw [ite_eq_right (by simp)]

theorem simEntry_counter_hasBinaryNat (tm : NTM k) (x : List Bool) (v : ℕ) :
    ((simEntry tm x v).work (Fin.last k)).HasBinaryNat v := by
  rw [simEntry_counter]
  simpa [natTape] using Tape.init_move_right_hasBinaryNat v

/-- The resumed simulation's start state is the delayed machine's extra state: the sentinel step
reads `▷` on the choice tape, and the delayed machine's first transition ignores its choice bit,
so nothing branches there. -/
theorem simCore_qstart (tm : NTM k) : (simCore tm).qstart = Sum.inl () := rfl

/-- **The entry configuration is the delayed machine's post-sentinel one.** This is the hypothesis
`NTM.choiceTM_delay_haltsIn` asks for: the simulation is entered exactly where the compulsory
`▷`-step would have left the machine. -/
theorem simEntry_dropChoice (tm : NTM k) (x : List Bool) (v : ℕ) :
    dropChoice (simEntry tm x v)
      = (delayNTM tm).trace 1 (fun _ => false) ((delayNTM tm).initCfg x) := by
  rw [trace_one_of_heads_zero (delayNTM tm) false ((delayNTM tm).initCfg x)
    (by show (Sum.inl () : Unit ⊕ tm.Q) ≠ Sum.inr tm.qhalt; nofun)
    rfl (fun _ => rfl) rfl (Tape.init_cells_zero _) (fun _ => Tape.init_cells_zero _)
    (Tape.init_cells_zero _)]
  refine Cfg.ext rfl rfl ?_ rfl
  · funext i
    show (if (i.castSucc : Fin (k + 1)).val < k then TM.blankTape else natTape v)
      = ((Tape.init ([] : List Γ))).move Dir3.right
    rw [show (i.castSucc : Fin (k + 1)).val = (i : ℕ) from rfl, ite_eq_left i.isLt]
    rfl


/-- **What the stage leaves behind.** Every tape still carries its marker only at cell zero; no
head has travelled further than the run was long; the input tape's contents are untouched, since
a machine never writes to it. These are the facts the cleanup stage needs, and they hold for any
stage, so they are read off the generic run lemmas. -/
theorem simTM_frame (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    {t : ℕ} {c c' : Cfg (k + 1) (simCore tm).Q}
    (hrun : (simTM tm m).reachesIn t (simCfg tm m extras c) (simCfg tm m extras c'))
    (hInvI : Tape.StartInvariant (simCfg tm m extras c).input)
    (hInvW : ∀ j, Tape.StartInvariant ((simCfg tm m extras c).work j))
    (hInvO : Tape.StartInvariant (simCfg tm m extras c).output)
    (hHeadI : (simCfg tm m extras c).input.head ≤ 1)
    (hHeadW : ∀ j, ((simCfg tm m extras c).work j).head ≤ 1) :
    Tape.StartInvariant (simCfg tm m extras c').input ∧
    (∀ j, Tape.StartInvariant ((simCfg tm m extras c').work j)) ∧
    (simCfg tm m extras c').input.cells = (simCfg tm m extras c).input.cells ∧
    (simCfg tm m extras c').input.head ≤ 1 + t ∧
    (∀ j, ((simCfg tm m extras c').work j).head ≤ 1 + t) := by
  obtain ⟨hI, hW, -⟩ := TM.startInvariant_reachesIn (simTM tm m) hrun hInvI hInvW hInvO
  obtain ⟨hbI, -, hbW⟩ := TM.head_le_start_add_of_reachesIn (simTM tm m) hrun
  refine ⟨hI, hW, TM.reachesIn_input_cells (simTM tm m) hrun, ?_, fun j => ?_⟩
  · omega
  · have := hbW j
    have := hHeadW j
    omega


/-- The stage's tapes at the simulation's own indices are the simulation's. -/
theorem simCfg_work_middle (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    (c : Cfg (k + 1) (simCore tm).Q) (i : Fin (k + 1))
    (j : Fin (0 + (k + 1) + m + 1)) (hj : j.val = i.val) :
    (simCfg tm m extras c).work j = c.work i := by
  have hlt : j.val < 0 + (k + 1) + m := by
    have := i.isLt
    omega
  rw [show (simCfg tm m extras c).work j
      = (TM.placeWorkCfg (simCore tm) 0 m extras c).work ⟨j.val, hlt⟩ from
    TM.retargetCfg_work_lt _ _ j hlt]
  rw [show (⟨j.val, hlt⟩ : Fin (0 + (k + 1) + m)) = TM.placeWorkIdx 0 m i from
    Fin.ext (by show j.val = 0 + i.val; omega), TM.placeWorkCfg_work_middle]

/-- The stage's tapes at the register indices are the registers, untouched. -/
theorem simCfg_work_extra (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    (c : Cfg (k + 1) (simCore tm).Q) (j : Fin (0 + (k + 1) + m + 1))
    (hmid : ¬ (j.val < 0 + (k + 1))) (hlt : j.val < 0 + (k + 1) + m) :
    (simCfg tm m extras c).work j = extras ⟨j.val, hlt⟩ := by
  rw [show (simCfg tm m extras c).work j
      = (TM.placeWorkCfg (simCore tm) 0 m extras c).work ⟨j.val, hlt⟩ from
    TM.retargetCfg_work_lt _ _ j hlt]
  exact TM.placeWorkCfg_work_extra _ _ _ _ _ _ (fun hcon => hmid hcon.2)

/-- **The simulation leaves the counter's digits alone.** `choiceTM` writes every choice bit back
unchanged and only advances the head, so after the cleanup rewinds it the counter reads as `v`
again. -/
theorem simCfg_counter_cells (tm : NTM k) (m : ℕ) (extras : Fin (0 + (k + 1) + m) → Tape)
    {t : ℕ} {c c' : Cfg (k + 1) (simCore tm).Q}
    (hreach : (simCore tm).reachesIn t c c')
    (hinv : (c.work (Fin.last k)).StartInvariant)
    (hhead : 1 ≤ (c.work (Fin.last k)).head)
    (j : Fin (0 + (k + 1) + m + 1)) (hj : j.val = k) :
    ((simCfg tm m extras c').work j).cells = ((simCfg tm m extras c).work j).cells := by
  rw [simCfg_work_middle tm m extras c' (Fin.last k) j (by simpa using hj),
    simCfg_work_middle tm m extras c (Fin.last k) j (by simpa using hj)]
  exact (choiceTM_choiceCells (delayNTM tm) hinv hhead c'
    (TM.reaches_of_reachesIn (TM.reachesIn_of_startedTM _ hreach))).1

end NTM

end Complexity

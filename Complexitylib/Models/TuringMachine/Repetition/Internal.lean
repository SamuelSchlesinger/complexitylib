/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Defs
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.Models.TuringMachine.Trace

/-!
# Correctness internals for fixed-time repetition

This file proves the local simulation and fixed-rewind invariants used by the
public correctness theorems for `NTM.repeatAtTime`.
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- Project one active repetition bank back to a source-machine configuration.
The source state is carried in the repetition control and is therefore supplied
separately. -/
def repeatProjectCfg (tm : NTM n) (j : Fin k) (q : tm.Q)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) : Cfg n tm.Q where
  state := q
  input := C.input
  work := fun i => C.work (repeatWorkIdx j i)
  output := C.work (repeatOutputIdx j)

/-- Apply one source transition without a halting check. Repetition uses this
operation exactly in non-halted `.run` states. -/
def repeatSourceStep (tm : NTM n) (b : Bool) (c : Cfg n tm.Q) : Cfg n tm.Q :=
  let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
    tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
  { state := q'
    input := c.input.move inputDir
    work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
    output := c.output.writeAndMove outputWrite outputDir }

/-- On a non-halted configuration, a one-slot trace is the raw source step. -/
theorem trace_one_eq_repeatSourceStep (tm : NTM n) (b : Bool) (c : Cfg n tm.Q)
    (h : c.state ≠ tm.qhalt) :
    tm.trace 1 (fun _ => b) c = repeatSourceStep tm b c := by
  simp [NTM.trace, h, repeatSourceStep]

/-- An active repetition bank simulates `c`. Before source halting its complete
projection agrees with `c`; after halting only the state and tape cells are
required to agree, because fixed-slot padding may bounce a head off cell zero. -/
def RepeatSimulates (tm : NTM n) (j : Fin k) (q : tm.Q)
    (c : Cfg n tm.Q) (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) : Prop :=
  q = c.state ∧
    C.input.cells = c.input.cells ∧
    (∀ i, (C.work (repeatWorkIdx j i)).cells = (c.work i).cells) ∧
    (C.work (repeatOutputIdx j)).cells = c.output.cells ∧
    (c.state ≠ tm.qhalt → repeatProjectCfg tm j q C = c)

/-- Exact projection implies the simulation relation. -/
theorem RepeatSimulates.of_project_eq (tm : NTM n) (j : Fin k) (q : tm.Q)
    (c : Cfg n tm.Q) (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (h : repeatProjectCfg tm j q C = c) : RepeatSimulates tm j q c C := by
  subst c
  exact ⟨rfl, rfl, fun _ => rfl, rfl, fun _ => rfl⟩

/-- On a transition direction already satisfying the model's left-end rule,
the repetition machine's defensive direction guard is inert. -/
theorem repeatSafeDir_eq (head : Γ) (dir : Dir3)
    (h : head = Γ.start → dir = Dir3.right) : repeatSafeDir head dir = dir := by
  by_cases hs : head = Γ.start
  · simp [repeatSafeDir, hs, h hs]
  · simp [repeatSafeDir, hs]

/-- Positioning an off-start tape writes its current symbol back and moves its
head one cell left. -/
theorem repeatPositionTape_eq (t : Tape) (hread : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ
        (repeatSafeDir t.read (TM.moveLeftDir t.read)) = t.move Dir3.left := by
  have hwrite : t.write (TM.readBackWrite t.read).toΓ = t := by
    rw [Tape.write]
    split
    · rfl
    · refine Tape.ext rfl ?_
      rw [TM.toΓ_readBackWrite_of_ne_start hread, Tape.read,
        Function.update_eq_self]
  rw [show repeatSafeDir t.read (TM.moveLeftDir t.read) = Dir3.left by
      simp [repeatSafeDir, TM.moveLeftDir, hread]]
  change (t.write (TM.readBackWrite t.read).toΓ).move Dir3.left = _
  rw [hwrite]

/-- A parked initialized input returns to its initial head position under the
positioning action. -/
theorem repeatPositionInput_init (x : List Bool) :
    let t := (Tape.init (x.map Γ.ofBool)).move Dir3.right
    t.writeAndMove (TM.readBackWrite t.read).toΓ
        (repeatSafeDir t.read (TM.moveLeftDir t.read)) = Tape.init (x.map Γ.ofBool) := by
  dsimp only
  rw [repeatPositionTape_eq _ (Tape.init_ofBool_move_right_read_ne_start x)]
  rfl

/-- A parked blank work tape returns to its initial head position under the
positioning action. -/
theorem repeatPositionBlank_init :
    let t := (Tape.init []).move Dir3.right
    t.writeAndMove (TM.readBackWrite t.read).toΓ
        (repeatSafeDir t.read (TM.moveLeftDir t.read)) = Tape.init [] := by
  dsimp only
  rw [repeatPositionTape_eq]
  · rfl
  · simp [Tape.read, Tape.move, Tape.init]

/-! ### Fixed-time rewind of one tape -/

/-- The one-tape component of a repetition rewind transition. -/
def repeatFixedRewindTapeStep (s : Tape × Bool) : Tape × Bool :=
  (s.1.writeAndMove (TM.readBackWrite s.1.read)
      (repeatSafeDir s.1.read (repeatRewindDir s.2 s.1.read)),
    repeatRewindDone s.2 s.1.read)

/-- Iterate the one-tape rewind component in the cons-first order of `NTM.trace`. -/
def repeatFixedRewindTapeIter : ℕ → Tape × Bool → Tape × Bool
  | 0, s => s
  | m + 1, s => repeatFixedRewindTapeIter m (repeatFixedRewindTapeStep s)

/-- Under the unique-left-marker invariant, a tape reads `▷` exactly at cell zero. -/
theorem repeatStartInvariant_read_eq_start_iff (t : Tape) (h : t.StartInvariant) :
    t.read = Γ.start ↔ t.head = 0 := by
  constructor
  · intro hr
    by_contra hh
    exact h.2 t.head (by omega) (by simpa [Tape.read] using hr)
  · intro hh
    simp [Tape.read, hh, h.1]

private theorem repeatFixedRewindTapeStep_zero (t : Tape) (h : t.StartInvariant)
    (hh : t.head = 0) :
    repeatFixedRewindTapeStep (t, false) = (t.move Dir3.right, true) := by
  have hr : t.read = Γ.start := (repeatStartInvariant_read_eq_start_iff t h).2 hh
  simp [repeatFixedRewindTapeStep, repeatSafeDir, repeatRewindDone, hr,
    Tape.writeAndMove, Tape.write, hh]

private theorem repeatFixedRewindTapeStep_false_pos (t : Tape)
    (h : t.StartInvariant) (hh : 0 < t.head) :
    repeatFixedRewindTapeStep (t, false) = (t.move Dir3.left, false) := by
  have hr : t.read ≠ Γ.start := by
    intro hrs
    have := (repeatStartInvariant_read_eq_start_iff t h).1 hrs
    omega
  simp only [repeatFixedRewindTapeStep, repeatSafeDir, repeatRewindDir,
    repeatRewindDone, hr, ↓reduceIte, decide_false, Bool.or_false,
    Bool.false_eq_true]
  rw [TM.writeAndMove_readBack t hr]

private theorem repeatFixedRewindTapeStep_true_head_one (t : Tape)
    (h : t.StartInvariant) (hh : t.head = 1) :
    repeatFixedRewindTapeStep (t, true) = (t, true) := by
  have hr : t.read ≠ Γ.start := h.read_ne_start (by omega)
  simp only [repeatFixedRewindTapeStep, repeatSafeDir, repeatRewindDir,
    repeatRewindDone, hr, ↓reduceIte, decide_false, Bool.true_or]
  rw [TM.writeAndMove_readBack t hr]
  rfl

private theorem repeatFixedRewindTapeIter_true_head_one (m : ℕ) (t : Tape)
    (h : t.StartInvariant) (hh : t.head = 1) :
    repeatFixedRewindTapeIter m (t, true) = (t, true) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [repeatFixedRewindTapeIter,
      repeatFixedRewindTapeStep_true_head_one t h hh, ih]

/-- `T + 1` fixed rewind steps park any invariant tape whose head is at most
`T` at cell one, set its completion flag, and preserve all cells. -/
theorem repeatFixedRewindTapeIter_bound (T : ℕ) (t : Tape)
    (h : t.StartInvariant) (hh : t.head ≤ T) :
    let s := repeatFixedRewindTapeIter (T + 1) (t, false)
    s.2 = true ∧ s.1.head = 1 ∧ s.1.cells = t.cells := by
  induction T generalizing t with
  | zero =>
    have ht0 : t.head = 0 := by omega
    rw [show 0 + 1 = 1 by omega, repeatFixedRewindTapeIter,
      repeatFixedRewindTapeStep_zero t h ht0]
    simp [repeatFixedRewindTapeIter, Tape.move, ht0]
  | succ T ih =>
    rw [show T.succ + 1 = (T + 1) + 1 by omega, repeatFixedRewindTapeIter]
    by_cases ht0 : t.head = 0
    · rw [repeatFixedRewindTapeStep_zero t h ht0,
        repeatFixedRewindTapeIter_true_head_one (T + 1) (t.move Dir3.right)
          (h.move Dir3.right) (by simp [Tape.move, ht0])]
      simp [Tape.move, ht0]
    · have htpos : 0 < t.head := by omega
      rw [repeatFixedRewindTapeStep_false_pos t h htpos]
      have hbound : (t.move Dir3.left).head ≤ T := by
        simp only [Tape.move]
        omega
      have hresult := ih (t.move Dir3.left) (h.move Dir3.left) hbound
      simpa only [Tape.move_cells] using hresult

/-- Configuration after the first setup transition: all tapes are parked at
cell one and the control is ready to choose the first repetition. -/
def repeatParkedCfg (tm : NTM n) (k T : ℕ) (x : List Bool) :
    Cfg (k * (n + 1)) (RepeatQ tm k T) where
  state := .begin
  input := (Tape.init (x.map Γ.ofBool)).move .right
  work := fun _ => (Tape.init []).move .right
  output := (Tape.init []).move .right

/-- The first setup transition parks every tape at cell one. -/
theorem repeatAtTime_trace_setup (tm : NTM n) (k T : ℕ) (x : List Bool)
    (choice : Fin 1 → Bool) :
    (repeatAtTime tm k T).trace 1 choice ((repeatAtTime tm k T).initCfg x) =
      repeatParkedCfg tm k T x := by
  rfl

/-- With at least one repetition and one simulated step, the second setup
transition positions trial zero exactly at the source initial configuration. -/
theorem repeatAtTime_begin_simulates (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (hT : 0 < T) (choice : Fin 1 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    let t : Fin T := ⟨0, hT⟩
    let votes : Fin k → Bool := fun _ => false
    let C := (repeatAtTime tm k T).trace 1 choice (repeatParkedCfg tm k T x)
    C.state = RepeatQ.run j t tm.qstart votes ∧
      RepeatSimulates tm j tm.qstart (tm.initCfg x) C := by
  dsimp only
  constructor
  · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg, hk, hT]
  · apply RepeatSimulates.of_project_eq
    apply (Cfg.mk.injEq ..).mpr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
        hk, hT]
      have hread := Tape.init_ofBool_move_right_read_ne_start x
      rw [show repeatSafeDir ((Tape.init (x.map Γ.ofBool)).move .right).read
          (TM.moveLeftDir ((Tape.init (x.map Γ.ofBool)).move .right).read) = .left by
        simp [repeatSafeDir, TM.moveLeftDir, hread]]
      rfl
    · funext i
      simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
        repeatPositionBankDirs, repeatWorkIdx, hk, hT]
      simpa [Tape.read, Tape.move, Tape.init, TM.readBackWrite, Γw.toΓ] using
        repeatPositionBlank_init
    · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
        repeatPositionBankDirs, repeatOutputIdx, hk, hT]
      simpa [Tape.read, Tape.move, Tape.init, TM.readBackWrite, Γw.toΓ] using
        repeatPositionBlank_init

/-- With positive repetition count and simulation time, the second setup
transition gives trial zero the exact source initial configuration. This
stronger projection fact also covers `tm.qstart = tm.qhalt`. -/
theorem repeatAtTime_begin_project (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (hT : 0 < T) (choice : Fin 1 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    let C := (repeatAtTime tm k T).trace 1 choice (repeatParkedCfg tm k T x)
    repeatProjectCfg tm j tm.qstart C = tm.initCfg x := by
  dsimp only
  apply (Cfg.mk.injEq ..).mpr
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
      hk, hT]
    have hread := Tape.init_ofBool_move_right_read_ne_start x
    rw [show repeatSafeDir ((Tape.init (x.map Γ.ofBool)).move .right).read
        (TM.moveLeftDir ((Tape.init (x.map Γ.ofBool)).move .right).read) = .left by
      simp [repeatSafeDir, TM.moveLeftDir, hread]]
    rfl
  · funext i
    simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
      repeatPositionBankDirs, repeatWorkIdx, hk, hT]
    simpa [Tape.read, Tape.move, Tape.init, TM.readBackWrite, Γw.toΓ] using
      repeatPositionBlank_init
  · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
      repeatPositionBankDirs, repeatOutputIdx, hk, hT]
    simpa [Tape.read, Tape.move, Tape.init, TM.readBackWrite, Γw.toΓ] using
      repeatPositionBlank_init

/-- The complete two-transition setup establishes the source initial
configuration in trial zero. -/
theorem repeatAtTime_trace_setup_simulates (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (hT : 0 < T) (choices : Fin 2 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    let t : Fin T := ⟨0, hT⟩
    let votes : Fin k → Bool := fun _ => false
    let C := (repeatAtTime tm k T).trace 2 choices ((repeatAtTime tm k T).initCfg x)
    C.state = RepeatQ.run j t tm.qstart votes ∧
      RepeatSimulates tm j tm.qstart (tm.initCfg x) C := by
  rw [(repeatAtTime tm k T).trace_two]
  rw [repeatAtTime_trace_setup]
  exact repeatAtTime_begin_simulates tm x hk hT
    (fun _ => choices ⟨1, by omega⟩)

/-- The complete positive-time setup gives trial zero the exact source initial
configuration. -/
theorem repeatAtTime_trace_setup_project (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (hT : 0 < T) (choices : Fin 2 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    let C := (repeatAtTime tm k T).trace 2 choices ((repeatAtTime tm k T).initCfg x)
    repeatProjectCfg tm j tm.qstart C = tm.initCfg x := by
  rw [(repeatAtTime tm k T).trace_two]
  rw [repeatAtTime_trace_setup]
  exact repeatAtTime_begin_project tm x hk hT
    (fun _ => choices ⟨1, by omega⟩)

/-- One non-halted repetition `.run` transition commutes exactly with one raw
source transition through the active-bank projection. -/
theorem repeatAtTime_run_project (tm : NTM n)
    (j : Fin k) (t : Fin T) (q : tm.Q) (votes : Fin k → Bool)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (b : Bool)
    (hstate : C.state = RepeatQ.run j t q votes) (hq : q ≠ tm.qhalt) :
    let c := repeatProjectCfg tm j q C
    let c' := repeatSourceStep tm b c
    let C' := (repeatAtTime tm k T).trace 1 (fun _ => b) C
    C'.state = repeatAfterRunState tm j t c'.state votes ∧
      repeatProjectCfg tm j c'.state C' = c' := by
  let r := tm.δ b q C.input.read (repeatWorkReads (fun i => (C.work i).read) j)
    (C.work (repeatOutputIdx j)).read
  rcases hr : r with ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩
  have hδ : tm.δ b q C.input.read (fun i => (C.work (repeatWorkIdx j i)).read)
      (C.work (repeatOutputIdx j)).read =
        (q', workWrites, outputWrite, inputDir, workDirs, outputDir) := by
    exact hr
  have hright := tm.δ_right_of_start b q C.input.read
    (repeatWorkReads (fun i => (C.work i).read) j)
    (C.work (repeatOutputIdx j)).read
  rw [show tm.δ b q C.input.read (repeatWorkReads (fun i => (C.work i).read) j)
      (C.work (repeatOutputIdx j)).read = r from rfl, hr] at hright
  dsimp only at hright
  have hright' :
      (C.input.read = Γ.start → inputDir = Dir3.right) ∧
      (∀ i : Fin n, (C.work (repeatWorkIdx j i)).read = Γ.start →
        workDirs i = Dir3.right) ∧
      ((C.work (repeatOutputIdx j)).read = Γ.start → outputDir = Dir3.right) := by
    simpa [repeatWorkReads] using hright
  dsimp only
  constructor
  · simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition, r, hr, hδ,
      repeatProjectCfg, repeatSourceStep]
  · apply (Cfg.mk.injEq ..).mpr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition, r, hr, hδ,
        repeatProjectCfg, repeatSafeDir_eq _ _ hright'.1]
    · funext i
      simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition, r, hr, hδ,
        repeatProjectCfg, repeatSafeDir_eq _ _ (hright'.2.1 i)]
    · simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition, r, hr, hδ,
        repeatProjectCfg, repeatSafeDir_eq _ _ hright'.2.2]

/-- One non-halted repetition `.run` transition projects to the source
machine's one-step trace, including the source's own halting semantics. -/
theorem repeatAtTime_run_project_trace (tm : NTM n)
    (j : Fin k) (t : Fin T) (q : tm.Q) (votes : Fin k → Bool)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (b : Bool)
    (hstate : C.state = RepeatQ.run j t q votes) (hq : q ≠ tm.qhalt) :
    let c := repeatProjectCfg tm j q C
    let c' := tm.trace 1 (fun _ => b) c
    let C' := (repeatAtTime tm k T).trace 1 (fun _ => b) C
    C'.state = repeatAfterRunState tm j t c'.state votes ∧
      repeatProjectCfg tm j c'.state C' = c' := by
  simpa only [trace_one_eq_repeatSourceStep tm b (repeatProjectCfg tm j q C) hq] using
    repeatAtTime_run_project tm j t q votes C b hstate hq

/-- A `.run` slot after the source has halted advances the fixed counter while
preserving the source state and every projected tape cell. Thus the
halt-aware simulation relation survives padding slots. -/
theorem repeatAtTime_run_padding_simulates (tm : NTM n)
    (j : Fin k) (t : Fin T) (q : tm.Q) (votes : Fin k → Bool)
    (c : Cfg n tm.Q) (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (b : Bool)
    (hstate : C.state = RepeatQ.run j t q votes)
    (hq : q = tm.qhalt) (hsim : RepeatSimulates tm j q c C)
    (hinv : ∀ i, (C.work i).StartInvariant) :
    let C' := (repeatAtTime tm k T).trace 1 (fun _ => b) C
    C'.state = repeatAfterRunState tm j t q votes ∧
      RepeatSimulates tm j q c C' := by
  dsimp only
  constructor
  · simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition]
  · refine ⟨hsim.1, ?_, ?_, ?_, ?_⟩
    · simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition,
        repeatPaddingDirs, Tape.move_cells]
      exact hsim.2.1
    · intro i
      simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition,
        repeatPaddingDirs, Tape.move_cells]
      calc
        _ = (C.work (repeatWorkIdx j i)).cells := by
          have hpres := TM.tape_readBackWrite_preserves
            (C.work (repeatWorkIdx j i)) Dir3.stay (by
              by_cases hzero : (C.work (repeatWorkIdx j i)).head = 0
              · exact Or.inl hzero
              · exact Or.inr ((hinv _).read_ne_start (by omega)))
          simpa only [TM.readBackWrite, Γw.toΓ, Tape.move_cells] using hpres
        _ = (c.work i).cells := hsim.2.2.1 i
    · simp [NTM.trace, repeatAtTime, hstate, hq, repeatGuardTransition,
        repeatPaddingDirs, Tape.move_cells]
      calc
        _ = (C.work (repeatOutputIdx j)).cells := by
          have hpres := TM.tape_readBackWrite_preserves
            (C.work (repeatOutputIdx j)) Dir3.stay (by
              by_cases hzero : (C.work (repeatOutputIdx j)).head = 0
              · exact Or.inl hzero
              · exact Or.inr ((hinv _).read_ne_start (by omega)))
          simpa only [TM.readBackWrite, Γw.toΓ, Tape.move_cells] using hpres
        _ = c.output.cells := hsim.2.2.2.1
    · intro hc
      exact (hc (hsim.1 ▸ hq)).elim

/-! ### A complete fixed-width simulation run -/

/-- Every proper prefix of a fixed-width simulation run remains in `.run`,
tracks the corresponding source prefix, and preserves all start invariants. -/
theorem repeatAtTime_trace_run_prefix (tm : NTM n) (hT : 0 < T)
    (j : Fin k) (votes : Fin k → Bool) (g : ℕ → Bool)
    (c₀ : Cfg n tm.Q) (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = RepeatQ.run j ⟨0, hT⟩ c₀.state votes)
    (hsim : RepeatSimulates tm j c₀.state c₀ C₀)
    (hinp : C₀.input.StartInvariant)
    (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (m : ℕ) (hm : m < T) :
    let c := tm.trace m (fun i => g i.val) c₀
    let C := (repeatAtTime tm k T).trace m (fun i => g i.val) C₀
    C.state = RepeatQ.run j ⟨m, hm⟩ c.state votes ∧
      RepeatSimulates tm j c.state c C ∧
      C.input.StartInvariant ∧ (∀ i, (C.work i).StartInvariant) ∧
      C.output.StartInvariant := by
  induction m with
  | zero =>
      exact And.intro hstate
        (And.intro hsim (And.intro hinp (And.intro hwork hout)))
  | succ m ih =>
      have hm' : m < T := by omega
      let c := tm.trace m (fun i => g i.val) c₀
      let C := (repeatAtTime tm k T).trace m (fun i => g i.val) C₀
      have hprefix :
          C.state = RepeatQ.run j ⟨m, hm'⟩ c.state votes ∧
            RepeatSimulates tm j c.state c C ∧
            C.input.StartInvariant ∧ (∀ i, (C.work i).StartInvariant) ∧
            C.output.StartInvariant := by
        simpa only [c, C] using ih hm'
      let c' := tm.trace 1 (fun _ => g m) c
      let C' := (repeatAtTime tm k T).trace 1 (fun _ => g m) C
      have hc_split : tm.trace (m + 1) (fun i => g i.val) c₀ = c' := by
        simpa [c, c'] using tm.trace_snoc m (fun i => g i.val) c₀
      have hC_split :
          (repeatAtTime tm k T).trace (m + 1) (fun i => g i.val) C₀ = C' := by
        simpa [C, C'] using
          (repeatAtTime tm k T).trace_snoc m (fun i => g i.val) C₀
      have hinv' := (repeatAtTime tm k T).trace_startInvariant 1
        (fun _ => g m) C hprefix.2.2.1 hprefix.2.2.2.1 hprefix.2.2.2.2
      by_cases hhalt : c.state = tm.qhalt
      · have hstep := repeatAtTime_run_padding_simulates tm j ⟨m, hm'⟩
          c.state votes c C (g m) hprefix.1 hhalt hprefix.2.1
          hprefix.2.2.2.1
        have hc' : c' = c := by
          exact tm.trace_halted 1 (fun _ => g m) hhalt
        simp only
        rw [hC_split, hc_split, hc']
        refine ⟨?_, hstep.2, hinv'.1, hinv'.2.1, hinv'.2.2⟩
        rw [hstep.1]
        simp [repeatAfterRunState, hm]
        rfl
      · have hproj := hprefix.2.1.2.2.2.2 hhalt
        have hstep := repeatAtTime_run_project_trace tm j ⟨m, hm'⟩
          c.state votes C (g m) hprefix.1 hhalt
        rw [hproj] at hstep
        simp only
        rw [hC_split, hc_split]
        refine ⟨?_, RepeatSimulates.of_project_eq tm j _ _ _ hstep.2,
          hinv'.1, hinv'.2.1, hinv'.2.2⟩
        rw [hstep.1]
        simp [repeatAfterRunState, hm, c']
        rfl

/-- Exactly `T` simulation slots advance trial `j` from its initial `.run`
state to rewind counter zero. The active bank agrees with the source `T`-step
trace even when the source halts early, and all tape start invariants persist. -/
theorem repeatAtTime_trace_run (tm : NTM n) (hT : 0 < T)
    (j : Fin k) (votes : Fin k → Bool) (choices : Fin T → Bool)
    (c₀ : Cfg n tm.Q) (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = RepeatQ.run j ⟨0, hT⟩ c₀.state votes)
    (hsim : RepeatSimulates tm j c₀.state c₀ C₀)
    (hinp : C₀.input.StartInvariant)
    (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) :
    let c := tm.trace T choices c₀
    let C := (repeatAtTime tm k T).trace T choices C₀
    C.state = RepeatQ.rewind j ⟨0, by omega⟩ c.state votes false (fun _ => false) ∧
      RepeatSimulates tm j c.state c C ∧
      C.input.StartInvariant ∧ (∀ i, (C.work i).StartInvariant) ∧
      C.output.StartInvariant := by
  let g : ℕ → Bool := fun a => if ha : a < T then choices ⟨a, ha⟩ else false
  have hg : (fun i : Fin T => g i.val) = choices := by
    funext i
    simp [g, i.isLt]
  rw [← hg]
  let m := T - 1
  have hm : m < T := by omega
  let c := tm.trace m (fun i => g i.val) c₀
  let C := (repeatAtTime tm k T).trace m (fun i => g i.val) C₀
  have hprefix := repeatAtTime_trace_run_prefix tm hT j votes g c₀ C₀ hstate hsim
    hinp hwork hout m hm
  let c' := tm.trace 1 (fun _ => g m) c
  let C' := (repeatAtTime tm k T).trace 1 (fun _ => g m) C
  have hc_split : tm.trace T (fun i => g i.val) c₀ = c' := by
    rw [show T = m + 1 by omega]
    simpa [c, c'] using tm.trace_snoc m (fun i => g i.val) c₀
  have hC_split :
      (repeatAtTime tm k T).trace T (fun i => g i.val) C₀ = C' := by
    calc
      _ = (repeatAtTime tm k T).trace (m + 1) (fun i => g i.val) C₀ := by
        simpa using (repeatAtTime tm k T).trace_cast
          (show T = m + 1 by omega) (fun i => g i.val) C₀
      _ = C' := by
        simpa [C, C'] using
          (repeatAtTime tm k T).trace_snoc m (fun i => g i.val) C₀
  have hlast : ¬m + 1 < T := by omega
  have hinv' := (repeatAtTime tm k T).trace_startInvariant 1
    (fun _ => g m) C hprefix.2.2.1 hprefix.2.2.2.1 hprefix.2.2.2.2
  by_cases hhalt : c.state = tm.qhalt
  · have hstep := repeatAtTime_run_padding_simulates tm j ⟨m, hm⟩
      c.state votes c C (g m) hprefix.1 hhalt hprefix.2.1
      hprefix.2.2.2.1
    have hc' : c' = c := tm.trace_halted 1 (fun _ => g m) hhalt
    simp only
    rw [hC_split, hc_split, hc']
    refine ⟨?_, hstep.2, hinv'.1, hinv'.2.1, hinv'.2.2⟩
    rw [hstep.1]
    simp [repeatAfterRunState, hlast]
    rfl
  · have hproj := hprefix.2.1.2.2.2.2 hhalt
    have hstep := repeatAtTime_run_project_trace tm j ⟨m, hm⟩
      c.state votes C (g m) hprefix.1 hhalt
    rw [hproj] at hstep
    simp only
    rw [hC_split, hc_split]
    refine ⟨?_, RepeatSimulates.of_project_eq tm j _ _ _ hstep.2,
      hinv'.1, hinv'.2.1, hinv'.2.2⟩
    rw [hstep.1]
    simp [repeatAfterRunState, hlast]
    rfl

end NTM

end Complexity

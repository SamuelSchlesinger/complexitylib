/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Universality
public import Complexitylib.Models.TuringMachine.OutputSemantics
public import Complexitylib.Models.TuringMachine.UTM.Universal
import Complexitylib.Models.TuringMachine.Combinators.Internal.Window
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal

/-!
# The universal machine satisfies the generic universality interface -- internals

The concrete `utmTM` is connected to `TM.IsEfficientlyUniversal` through three
exact simulations, each proved in both directions:

1. a `k`-work-tape machine is simulated by a single-work-tape machine under the
   identity compiler (`singleTapeSim`, or `pad0` when `k = 0`);
2. a single-work-tape machine is simulated step for step by the interpreted
   description `descOfTM`;
3. the interpreted description of `α` is simulated by `utmTM` under the
   compiler `pair α`.

Each stage supplies two facts to one generic engine
(`simulates_and_simulatesInTime_of_forward`): a forward simulation of halting
runs that preserves the exact output, and unbounded simulator runs on every
program where the source diverges. Determinism then reflects halting and
output: a simulator run that halts at time `T` admits no run longer than `T`.

The divergence facts are the new content. For the single-tape stage they come
from the macro-step correspondence `corr_trace_macroPos`, which holds on
non-halting runs; for the universal machine they come from `loop_iteration`,
which simulates one source step from an arbitrary configuration and takes at
least one step.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {simulatorTapes sourceTapes : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Generic engine
-- ════════════════════════════════════════════════════════════════════════

/-- A machine that never halts on `program` has a run of every length. -/
theorem exists_reachesIn_of_not_halts {source : TM sourceTapes} {program : List Bool}
    (hdiv : ¬ source.Halts program) :
    ∀ n, ∃ c, source.reachesIn n (source.initCfg program) c := by
  intro n
  induction n with
  | zero => exact ⟨_, .zero⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    cases hs : source.step c with
    | none => exact absurd ⟨c, reaches_of_reachesIn hc, step_eq_none_iff_halted.mp hs⟩ hdiv
    | some c' => exact ⟨c', reachesIn_snoc hc hs⟩

/-- Two tapes that agree through the first blank of the second one have the
same exact outputs. -/
theorem hasOutput_iff_of_agree_through_blank {tape reference : Tape} {m : ℕ}
    (hblank : reference.cells (m + 1) = Γ.blank)
    (hnonblank : ∀ j, j < m → reference.cells (j + 1) ≠ Γ.blank)
    (hagree : ∀ j, j ≤ m → tape.cells (j + 1) = reference.cells (j + 1))
    (output : List Bool) :
    tape.HasOutput output ↔ reference.HasOutput output := by
  have hlength : ∀ {candidate : Tape},
      (∀ j, j ≤ m → candidate.cells (j + 1) = reference.cells (j + 1)) →
      candidate.HasOutput output → output.length = m := by
    intro candidate hcandidate ⟨hbits, hend⟩
    rcases Nat.lt_trichotomy output.length m with hlt | heq | hgt
    · exact absurd ((hcandidate _ hlt.le).symm.trans hend) (hnonblank _ hlt)
    · exact heq
    · have hbit := hbits m hgt
      rw [hcandidate m le_rfl, hblank] at hbit
      exact absurd hbit.symm (Γ.ofBool_ne_blank _)
  constructor
  · intro htape
    have hm := hlength hagree htape
    obtain ⟨hbits, -⟩ := htape
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [← hagree i (by omega)]
      exact hbits i hi
    · rw [hm]
      exact hblank
  · intro hreference
    have hm := hlength (fun _ _ => rfl) hreference
    obtain ⟨hbits, -⟩ := hreference
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hagree i (by omega)]
      exact hbits i hi
    · rw [hm, hagree m le_rfl]
      exact hblank

/-- **Simulation from forward runs and divergence.** A compiler and a monotone
clock yield an exact semantic simulation and a timed simulation when

* every halting source run is reproduced within the clock by a halting
  simulator run with the same exact outputs, and
* on every program where the source diverges, the simulator has runs of
  unbounded length.

Reflection of halting and of outputs is by determinism: a simulator run that
halts at time `T` admits no longer run, and halted endpoints are unique. -/
theorem simulates_and_simulatesInTime_of_forward {simulator : TM simulatorTapes}
    {source : TM sourceTapes} (compile : List Bool → List Bool) (clock : TimeOverhead)
    (hmono : ∀ program, Monotone (clock program))
    (hforward : ∀ program time (c : Cfg sourceTapes source.Q),
      source.reachesIn time (source.initCfg program) c → source.halted c →
      ∃ (d : Cfg simulatorTapes simulator.Q) (steps : ℕ), steps ≤ clock program time ∧
        simulator.reachesIn steps (simulator.initCfg (compile program)) d ∧
        simulator.halted d ∧ ∀ output, d.output.HasOutput output ↔ c.output.HasOutput output)
    (hdiverge : ∀ program, ¬ source.Halts program → ∀ n,
      ∃ (steps : ℕ) (d : Cfg simulatorTapes simulator.Q), n ≤ steps ∧
        simulator.reachesIn steps (simulator.initCfg (compile program)) d) :
    simulator.Simulates source compile ∧ simulator.SimulatesInTime source compile clock := by
  have hreflect : ∀ program, simulator.Halts (compile program) → source.Halts program := by
    rintro program ⟨dHalt, hreach, hhalt⟩
    by_contra hnot
    obtain ⟨T, hT⟩ := simulator.reaches_to_reachesIn hreach
    obtain ⟨steps, d, hsteps, hd⟩ := hdiverge program hnot (T + 1)
    have := simulator.reachesIn_le_halt hd hT hhalt
    omega
  refine ⟨⟨fun program => ⟨hreflect program, ?_⟩, fun program output => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨c, hreach, hhalt⟩
    obtain ⟨time, htime⟩ := source.reaches_to_reachesIn hreach
    obtain ⟨d, steps, -, hd, hdHalt, -⟩ := hforward program time c htime hhalt
    exact ⟨d, reaches_of_reachesIn hd, hdHalt⟩
  · rintro ⟨dHalt, hreach, hhalt, hout⟩
    obtain ⟨c, hcReach, hcHalt⟩ := hreflect program ⟨dHalt, hreach, hhalt⟩
    obtain ⟨time, htime⟩ := source.reaches_to_reachesIn hcReach
    obtain ⟨d, steps, -, hd, hdHalt, hiff⟩ := hforward program time c htime hcHalt
    obtain ⟨T, hT⟩ := simulator.reaches_to_reachesIn hreach
    obtain rfl : d = dHalt := reachesIn_halted_unique hd hT hdHalt hhalt
    exact ⟨c, hcReach, hcHalt, (hiff output).mp hout⟩
  · rintro ⟨c, hreach, hhalt, hout⟩
    obtain ⟨time, htime⟩ := source.reaches_to_reachesIn hreach
    obtain ⟨d, steps, -, hd, hdHalt, hiff⟩ := hforward program time c htime hhalt
    exact ⟨d, reaches_of_reachesIn hd, hdHalt, (hiff output).mpr hout⟩
  · rintro program budget ⟨c, time, htime, hreach, hhalt⟩
    obtain ⟨d, steps, hsteps, hd, hdHalt, -⟩ := hforward program time c hreach hhalt
    exact ⟨d, steps, hsteps.trans (hmono program htime), hd, hdHalt⟩
  · rintro program output budget ⟨c, time, htime, hreach, hhalt, hout⟩
    obtain ⟨d, steps, hsteps, hd, hdHalt, hiff⟩ := hforward program time c hreach hhalt
    exact ⟨d, steps, hsteps.trans (hmono program htime), hd, hdHalt, (hiff output).mpr hout⟩

end TM

-- ════════════════════════════════════════════════════════════════════════
-- Deterministic NTM traces as DTM runs
-- ════════════════════════════════════════════════════════════════════════

namespace NTM

variable {n : ℕ}

/-- A non-halted trace configuration of a deterministic NTM is reached by
`toTM` in exactly the trace length. -/
theorem Deterministic.toTM_reachesIn_trace_of_ne_halt {N : NTM n}
    (hdet : N.Deterministic) :
    ∀ (T : ℕ) (choices : Fin T → Bool) (c : Cfg n N.Q),
      (N.trace T choices c).state ≠ N.qhalt → N.toTM.reachesIn T c (N.trace T choices c)
  | 0, _, _, _ => .zero
  | T + 1, choices, c, hne => by
    have hc : c.state ≠ N.qhalt := fun hc =>
      hne (by rw [N.trace_halted (T + 1) choices hc]; exact hc)
    have hsplit : N.trace (T + 1) choices c =
        N.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
          ((N.toTM.step c).get (by simp [TM.step, toTM, hc])) := by
      simp [NTM.trace, hc, toTM, TM.step, hdet.δ_eq]
    rw [hsplit] at hne ⊢
    exact .step (Option.some_get _).symm
      (toTM_reachesIn_trace_of_ne_halt hdet T _ _ hne)

end NTM

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Stage 1: multi-tape → single-tape
-- ════════════════════════════════════════════════════════════════════════

/-- The single-tape stage's clock: the quadratic overhead of
`NTM.singleTapeSimTime` at a fixed source budget. -/
def singleTapeClock (k : ℕ) : TimeOverhead :=
  fun program time => 16 * (k + 1) * (time + program.length + 1) ^ 2

theorem singleTapeClock_mono (k : ℕ) (program : List Bool) :
    Monotone (singleTapeClock k program) := by
  intro first second hle
  unfold singleTapeClock
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- A DTM that never halts on `program` has a never-halting NTM embedding. -/
private theorem toNTM_trace_ne_halt_of_not_halts {k : ℕ} {M : TM k} {program : List Bool}
    (hdiv : ¬ M.Halts program) (T : ℕ) (choices : Fin T → Bool) :
    (M.toNTM.trace T choices (M.toNTM.initCfg program)).state ≠ M.toNTM.qhalt :=
  fun hhalt => hdiv ⟨_, M.toNTM_trace_reaches (M.initCfg program) T choices, hhalt⟩

/-- The multi-tape to single-tape stage for `k ≥ 1`, through `singleTapeSim`. -/
private theorem singleTapeSim_simulates {k : ℕ} (hk : 1 ≤ k) (M : TM k) :
    (NTM.singleTapeSim M.toNTM).toTM.Simulates M id ∧
      (NTM.singleTapeSim M.toNTM).toTM.SimulatesInTime M id (singleTapeClock k) := by
  have hdet : (NTM.singleTapeSim M.toNTM).Deterministic :=
    NTM.singleTapeSim_deterministic M.toNTM_deterministic
  refine simulates_and_simulatesInTime_of_forward id (singleTapeClock k)
    (singleTapeClock_mono k) ?_ ?_
  · intro program time c hreach hhalt
    let ch : ℕ → Bool := fun _ => false
    have htrace : M.toNTM.trace time
        (fun i => NTM.SingleTape.inducedChoices k ch i.val) (M.toNTM.initCfg program) = c :=
      M.toNTM_trace_of_reachesIn hreach hhalt le_rfl _
    obtain ⟨m, hm, hsimHalt, hcells⟩ :=
      NTM.SingleTape.halts_rev_output_cells M.toNTM hk ch program time
        (by rw [htrace]; exact hhalt)
    obtain ⟨steps, hsteps, hrun⟩ := hdet.toTM_reachesIn_trace m (fun i => ch i.val)
      ((NTM.singleTapeSim M.toNTM).initCfg program)
    refine ⟨_, steps, ?_, hrun, hsimHalt, fun output => ?_⟩
    · exact le_trans hsteps (le_trans hm
        (NTM.SingleTape.mul_macroBound_succ_le k time program.length))
    · rw [htrace] at hcells
      exact Tape.hasOutput_congr hcells output
  · intro program hdiv n
    let ch : ℕ → Bool := fun _ => false
    have hcorr := NTM.SingleTape.corr_trace_macroPos M.toNTM hk ch program n
      (fun s _ => toNTM_trace_ne_halt_of_not_halts hdiv s _)
    have hne : ((NTM.singleTapeSim M.toNTM).trace (NTM.SingleTape.macroPos k n)
        (fun i => ch i.val) ((NTM.singleTapeSim M.toNTM).initCfg program)).state
          ≠ (NTM.singleTapeSim M.toNTM).qhalt := by
      rw [hcorr.state]
      simp [NTM.singleTapeSim, NTM.SingleTape.SimQ.run, NTM.SingleTape.SimQ.halt]
    refine ⟨NTM.SingleTape.macroPos k n, _, ?_,
      hdet.toTM_reachesIn_trace_of_ne_halt _ _ _ hne⟩
    clear hcorr hne
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      show n + 1 ≤ NTM.SingleTape.macroPos k n + NTM.SingleTape.macroLen k n
      have : 1 ≤ NTM.SingleTape.macroLen k n := by
        unfold NTM.SingleTape.macroLen
        omega
      omega

/-- The multi-tape to single-tape stage for `k = 0`, through `pad0`. -/
private theorem pad0_simulates (M : TM 0) :
    (NTM.pad0 M.toNTM).toTM.Simulates M id ∧
      (NTM.pad0 M.toNTM).toTM.SimulatesInTime M id (singleTapeClock 0) := by
  have hdet : (NTM.pad0 M.toNTM).Deterministic :=
    NTM.pad0_deterministic M.toNTM_deterministic
  refine simulates_and_simulatesInTime_of_forward id (singleTapeClock 0)
    (singleTapeClock_mono 0) ?_ ?_
  · intro program time c hreach hhalt
    let ch : Fin time → Bool := fun _ => false
    have htrace : M.toNTM.trace time ch (M.toNTM.initCfg program) = c :=
      M.toNTM_trace_of_reachesIn hreach hhalt le_rfl _
    obtain ⟨hstate, -, houtput⟩ := NTM.pad0_trace_init M.toNTM program time ch
    rw [htrace] at hstate houtput
    obtain ⟨steps, hsteps, hrun⟩ := hdet.toTM_reachesIn_trace time ch
      ((NTM.pad0 M.toNTM).initCfg program)
    refine ⟨_, steps, ?_, hrun, hstate.trans hhalt, fun output => by rw [houtput]⟩
    unfold singleTapeClock
    calc steps ≤ time + program.length + 1 := by omega
      _ ≤ (time + program.length + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      _ ≤ 16 * (0 + 1) * (time + program.length + 1) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by norm_num)
  · intro program hdiv n
    let ch : Fin n → Bool := fun _ => false
    have hne : ((NTM.pad0 M.toNTM).trace n ch ((NTM.pad0 M.toNTM).initCfg program)).state
        ≠ (NTM.pad0 M.toNTM).qhalt := by
      rw [(NTM.pad0_trace_init M.toNTM program n ch).1]
      exact toNTM_trace_ne_halt_of_not_halts hdiv n ch
    exact ⟨n, _, le_rfl, hdet.toTM_reachesIn_trace_of_ne_halt _ _ _ hne⟩

/-- **Stage 1.** Every `k`-work-tape machine is simulated exactly by a
single-work-tape machine under the identity compiler, with quadratic
overhead. -/
theorem exists_singleTape_simulates_internal {k : ℕ} (M : TM k) :
    ∃ M₁ : TM 1, M₁.Simulates M id ∧ M₁.SimulatesInTime M id (singleTapeClock k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨_, pad0_simulates M⟩
  · exact ⟨_, singleTapeSim_simulates hk M⟩

-- ════════════════════════════════════════════════════════════════════════
-- Stage 2: single-tape machine → interpreted description
-- ════════════════════════════════════════════════════════════════════════

/-- **Stage 2.** The interpreted description of a single-work-tape machine
simulates it step for step. -/
theorem descOfTM_simulates_internal (M : TM 1) :
    M.descOfTM.toTM.Simulates M id ∧
      M.descOfTM.toTM.SimulatesInTime M id (fun _ time => time) := by
  refine simulates_and_simulatesInTime_of_forward id (fun _ time => time)
    (fun _ => monotone_id) ?_ ?_
  · intro program time c hreach hhalt
    refine ⟨M.descCfg c, time, le_rfl, ?_, (M.descOfTM_halted c).mpr hhalt,
      fun _ => Iff.rfl⟩
    rw [← M.descOfTM_initCfg]
    exact M.descOfTM_reachesIn hreach
  · intro program hdiv n
    obtain ⟨c, hc⟩ := exists_reachesIn_of_not_halts hdiv n
    refine ⟨n, M.descCfg c, le_rfl, ?_⟩
    rw [← M.descOfTM_initCfg]
    exact M.descOfTM_reachesIn hc

namespace UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- Stage 3: interpreted description → universal machine
-- ════════════════════════════════════════════════════════════════════════

/-- Embed a loop configuration into `utmTM`: phase two of the outer sequence,
phase one of the inner loop/extract sequence. -/
def loopCfg (c : Cfg 6 (loopTM bodyTM haltTestTM).Q) : Cfg 6 utmTM.Q :=
  phase2Wrap initTM (seqTM (loopTM bodyTM haltTestTM) extractTM)
    (phase1Wrap (loopTM bodyTM haltTestTM) extractTM c)

/-- Loop runs lift to `utmTM` runs. -/
theorem utmTM_reachesIn_loopCfg {t : ℕ} {c c' : Cfg 6 (loopTM bodyTM haltTestTM).Q}
    (h : (loopTM bodyTM haltTestTM).reachesIn t c c') :
    utmTM.reachesIn t (loopCfg c) (loopCfg c') :=
  seqTM_reachesIn_phase2Wrap initTM _ (seqTM_reachesIn_phase1Wrap _ extractTM h)

/-- After initialization, `utmTM` reaches the loop's start state with the
standing invariant at the interpreted machine's initial configuration. -/
theorem utmTM_reachesIn_loop_start (α x : List Bool) :
    ∃ (t : ℕ) (inp : Tape) (work : Fin 6 → Tape) (out : Tape),
      SimInv α ((decodeDesc α).toTM.initCfg x) inp work out ∧
      out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧ out.head = 1 ∧
      utmTM.reachesIn t (utmTM.initCfg (pair α x))
        (loopCfg ⟨(loopTM bodyTM haltTestTM).qstart, inp, work, out⟩) := by
  obtain ⟨c₁, t₁, -, hrun, hhalt, hpost⟩ :=
    initTM_hoareTime α x (Tape.init ((pair α x).map Γ.ofBool)) (fun _ => Tape.init [])
      (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  obtain ⟨hinv, hout0, houtns, houth⟩ := utm_init_trans α x c₁.input c₁.work c₁.output hpost
  refine ⟨t₁ + 1, _, _, _, hinv, hout0, houtns, houth, ?_⟩
  exact reachesIn_snoc
    (seqTM_reachesIn_phase1Wrap initTM (seqTM (loopTM bodyTM haltTestTM) extractTM) hrun)
    (seqTM_transition_step initTM (seqTM (loopTM bodyTM haltTestTM) extractTM) hhalt)

/-- On a divergent interpreted run, `utmTM` has runs of every length: each loop
iteration simulates one more source step and takes at least one step. -/
theorem utmTM_diverges (α x : List Bool) (hterm : TerminatedRegion α)
    (hdiv : ¬ (decodeDesc α).toTM.Halts x) (n : ℕ) :
    ∃ (steps : ℕ) (d : Cfg 6 utmTM.Q), n ≤ steps ∧
      utmTM.reachesIn steps (utmTM.initCfg (pair α x)) d := by
  obtain ⟨t₀, inp, work₀, out₀, hinv₀, hout0₀, houtns₀, houth₀, hrun₀⟩ :=
    utmTM_reachesIn_loop_start α x
  have hnotHalted : ∀ {m : ℕ} {c : Cfg 1 (decodeDesc α).toTM.Q},
      (decodeDesc α).toTM.reachesIn m ((decodeDesc α).toTM.initCfg x) c →
        ¬ (decodeDesc α).toTM.halted c :=
    fun hm hc => hdiv ⟨_, reaches_of_reachesIn hm, hc⟩
  have key : ∀ rounds : ℕ, ∃ (steps : ℕ) (mc : Cfg 1 (decodeDesc α).toTM.Q)
      (work : Fin 6 → Tape) (out : Tape),
      rounds ≤ steps ∧
      (decodeDesc α).toTM.reachesIn rounds ((decodeDesc α).toTM.initCfg x) mc ∧
      SimInv α mc inp work out ∧ out.cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧ out.head = 1 ∧
      utmTM.reachesIn steps (utmTM.initCfg (pair α x))
        (loopCfg ⟨(loopTM bodyTM haltTestTM).qstart, inp, work, out⟩) := by
    intro rounds
    induction rounds with
    | zero =>
      exact ⟨t₀, _, work₀, out₀, Nat.zero_le _, .zero, hinv₀, hout0₀, houtns₀, houth₀, hrun₀⟩
    | succ rounds ih =>
      obtain ⟨steps, mc, work, out, hsteps, hmc, hinv, hout0, houtns, houth, hrun⟩ := ih
      obtain ⟨mc₂, work', out', t, -, hpos, hstep, hinv', hout0', houtns', houth', hbranch⟩ :=
        loop_iteration α hterm mc inp work out hinv hout0 houtns houth
      have hsome : (decodeDesc α).toTM.step mc = some mc₂ := by
        rcases hstep with h | ⟨hnone, -⟩
        · exact h
        · exact absurd (step_eq_none_iff_halted.mp hnone) (hnotHalted hmc)
      have hmc₂ := reachesIn_snoc hmc hsome
      rcases hbranch with ⟨hq, -, -⟩ | ⟨-, hloop⟩
      · exact absurd hq (hnotHalted hmc₂)
      · exact ⟨steps + t, mc₂, work', out', by omega, hmc₂, hinv', hout0', houtns', houth',
          reachesIn_trans _ hrun (utmTM_reachesIn_loopCfg hloop)⟩
  obtain ⟨steps, _, _, _, hsteps, _, _, _, _, _, hrun⟩ := key n
  exact ⟨steps, _, hsteps, hrun⟩

theorem utmTime_mono (α : List Bool) (n : ℕ) : Monotone fun T => utmTime α T n := by
  intro first second hle
  have hmul : (first + 1) * utmStepTime α ≤ (second + 1) * utmStepTime α :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [utmTime]
  omega

/-- **Stage 3.** For a canonical description `α`, `utmTM` simulates the
interpreted machine exactly under the compiler `pair α`, within `utmTime`. -/
theorem utmTM_simulates_decodeDesc_internal (α : List Bool) (hterm : TerminatedRegion α) :
    utmTM.Simulates (decodeDesc α).toTM (pair α) ∧
      utmTM.SimulatesInTime (decodeDesc α).toTM (pair α)
        (fun program time => utmTime α time program.length) := by
  refine simulates_and_simulatesInTime_of_forward (pair α)
    (fun program time => utmTime α time program.length)
    (fun program => utmTime_mono α program.length) ?_ (fun program hdiv n =>
      utmTM_diverges α program hterm hdiv n)
  intro program time c hreach hhalt
  obtain ⟨c', steps, hsteps, hrun, hhalt', m, -, hblank, hnonblank, hagree⟩ :=
    utmTM_hoareTime α program hterm time c hreach hhalt
      (Tape.init ((pair α program).map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
      ⟨rfl, fun _ => rfl, rfl⟩
  refine ⟨c', steps, ?_, hrun, hhalt',
    hasOutput_iff_of_agree_through_blank hblank hnonblank hagree⟩
  rw [pair_length] at hsteps
  simp only [utmTime]
  omega

-- ════════════════════════════════════════════════════════════════════════
-- Assembly
-- ════════════════════════════════════════════════════════════════════════

/-- The composed clock: single-tape overhead followed by universal simulation
of the extracted description `α`. -/
def utmClock (α : List Bool) (k : ℕ) : TimeOverhead :=
  fun program time => utmTime α (singleTapeClock k program time) program.length

/-- **`utmTM` simulates every machine through a fixed description.** For every
`k`-work-tape machine there is a description `α` such that `utmTM` simulates it
exactly under the uniform compiler `pair α`, within `utmClock α k`. -/
theorem utmTM_simulates_pair_internal {k : ℕ} (M : TM k) :
    ∃ α : List Bool, utmTM.Simulates M (pair α) ∧
      utmTM.SimulatesInTime M (pair α) (utmClock α k) := by
  obtain ⟨M₁, hsim₁, htime₁⟩ := exists_singleTape_simulates_internal M
  obtain ⟨hsimDesc, htimeDesc⟩ := descOfTM_simulates_internal M₁
  have hwf := M₁.descOfTM_wf
  have hterm : TerminatedRegion (encodeDesc M₁.descOfTM) :=
    terminatedRegion_encodeDesc_plain hwf (descOfTM_entries_ne_nil M₁)
  obtain ⟨hsimUtm, htimeUtm⟩ := utmTM_simulates_decodeDesc_internal _ hterm
  rw [decodeDesc_encodeDesc hwf] at hsimUtm htimeUtm
  exact ⟨encodeDesc M₁.descOfTM, hsimUtm.comp (hsimDesc.comp hsim₁),
    htimeUtm.comp (htimeDesc.comp htime₁)⟩

/-- The compiler `pair α` is computable; indeed it is polynomial-time. -/
theorem pair_isComputable (α : List Bool) : IsComputable (pair α) := by
  have hfp : (fun z : List Bool => pair ((fun _ : List Bool => α) z) (id z)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP α) id_mem_FP
  obtain ⟨_, tapes, machine, time, hcomputes, -⟩ := hfp
  exact ⟨tapes, machine, time, hcomputes⟩

/-- `pair α` adds exactly `2|α| + 2` bits. -/
theorem pair_additiveProgramOverhead (α : List Bool) :
    HasAdditiveProgramOverhead (pair α) (2 * α.length + 2) := by
  intro program
  rw [pair_length]
  omega

/-- The composed clock is polynomial in program length plus source time. -/
theorem utmClock_polynomial (α : List Bool) (k : ℕ) :
    PolynomialTimeOverhead (utmClock α k) := by
  refine ⟨8 * α.length + 4 * (groupPairs α).length + 47 + utmStepTime α +
    16 * (k + 1) * (utmStepTime α + 2), 2, fun program time => ?_⟩
  have hX : 1 ≤ (program.length + time + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hlen : program.length ≤ (program.length + time + 1) ^ 2 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have hexpand : utmClock α k program time =
      (8 * α.length + 4 * (groupPairs α).length + 43 + utmStepTime α) +
        4 * program.length +
        16 * (k + 1) * (utmStepTime α + 2) * (program.length + time + 1) ^ 2 := by
    simp only [utmClock, utmTime, singleTapeClock]
    ring
  have hconst : 8 * α.length + 4 * (groupPairs α).length + 43 + utmStepTime α ≤
      (8 * α.length + 4 * (groupPairs α).length + 43 + utmStepTime α) *
        (program.length + time + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ hX
  have hlen4 : 4 * program.length ≤ 4 * (program.length + time + 1) ^ 2 :=
    Nat.mul_le_mul_left 4 hlen
  rw [hexpand]
  calc _ ≤ (8 * α.length + 4 * (groupPairs α).length + 43 + utmStepTime α) *
          (program.length + time + 1) ^ 2 + 4 * (program.length + time + 1) ^ 2 +
        16 * (k + 1) * (utmStepTime α + 2) * (program.length + time + 1) ^ 2 := by
        omega
    _ = _ := by ring

/-- **The concrete universal machine is polynomially efficiently universal.** -/
theorem utmTM_isEfficientlyUniversal_internal : utmTM.IsEfficientlyUniversal := by
  intro k M
  obtain ⟨α, hsim, htime⟩ := utmTM_simulates_pair_internal M
  exact ⟨pair α, 2 * α.length + 2, utmClock α k, pair_isComputable α, hsim,
    pair_additiveProgramOverhead α, htime, utmClock_polynomial α k⟩

end UTMBody

end TM

end Complexity

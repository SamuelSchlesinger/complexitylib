/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.SingleTape

/-!
# Deterministic NTMs → DTMs

An NTM whose two transition functions coincide is *deterministic*: its trace is
independent of the choice sequence and coincides with the run of the DTM
`NTM.toTM` obtained by keeping the `false` transition function. This lets the
multi-tape → single-tape NTM simulation (`NTM.singleTapeSim`) be reused for
deterministic machines:

* `NTM.Deterministic`, `NTM.toTM` — the predicate and the conversion.
* `NTM.toTM_decidesInTime` — a deterministic NTM decider yields a `toTM`
  decider in the same time bound. `NTM.DecidesInTime` encodes rejection only
  as ¬acceptance (output cell 1 ≠ `1`), while `TM.DecidesInTime` demands the
  cell be exactly `0`, so the conversion also needs the output discipline
  `NTM.RejectsWithZero` (which every machine arising from a DTM satisfies).
* `TM.toNTM_deterministic`, `NTM.pad0_deterministic`,
  `NTM.singleTapeSim_deterministic` — the embedding, the padding, and the
  single-tape simulator all preserve determinism (the simulator consults its
  choice bit only to feed it to `N.δ`).
* `TM.exists_singleTape_decidesInTime` — the headline: every language decidable by a
  `k`-work-tape DTM in time `T` is decidable by a single-work-tape DTM within
  `singleTapeSimTime k T = fun n => 16 * (k + 1) * (T n + n + 1) ^ 2`.
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n : ℕ}

/-- An NTM is *deterministic* when its two transition functions coincide. The
    `∀ b` form (rather than `δ true = δ false`) rewrites uniformly under any
    choice bit. -/
def Deterministic (N : NTM n) : Prop := ∀ b, N.δ b = N.δ false

/-- Unfolded form of `Deterministic`, usable as a rewrite rule. -/
theorem Deterministic.δ_eq {N : NTM n} (hdet : N.Deterministic) :
    ∀ b, N.δ b = N.δ false := hdet

/-- Convert an NTM back to a DTM by keeping the `false` transition function.
    For a `Deterministic` machine this is a semantics-preserving inverse of
    `TM.toNTM`. -/
def toTM (N : NTM n) : TM n where
  Q := N.Q
  qstart := N.qstart
  qhalt := N.qhalt
  δ := N.δ false
  δ_right_of_start := N.δ_right_of_start false

/-- One non-halted trace step of a deterministic NTM is exactly one `toTM`
    step (mirror of `TM.toNTM_trace_step`). -/
private theorem Deterministic.trace_step {N : NTM n} (hdet : N.Deterministic)
    {c : Cfg n N.Q} (T : ℕ) (choices : Fin (T + 1) → Bool)
    (hne : c.state ≠ N.qhalt) :
    N.trace (T + 1) choices c =
    N.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
      ((N.toTM.step c).get (by simp [TM.step, toTM, hne])) := by
  simp [NTM.trace, hne, toTM, TM.step, hdet.δ_eq]

/-- For a deterministic NTM, the trace is independent of the choice sequence
    (mirror of `TM.toNTM_trace_choice_irrel`). -/
theorem Deterministic.trace_congr_choices {N : NTM n} (hdet : N.Deterministic)
    (T : ℕ) (c : Cfg n N.Q) (ch₁ ch₂ : Fin T → Bool) :
    N.trace T ch₁ c = N.trace T ch₂ c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    simp only [NTM.trace, hdet.δ_eq]
    split
    · rfl
    · exact ih _ _ _

/-- **Step-exact correspondence.** The `toTM` run reaches the deterministic
    NTM's trace configuration within the trace length. -/
theorem Deterministic.toTM_reachesIn_trace {N : NTM n} (hdet : N.Deterministic)
    (T : ℕ) (choices : Fin T → Bool) (c : Cfg n N.Q) :
    ∃ t ≤ T, N.toTM.reachesIn t c (N.trace T choices c) := by
  induction T generalizing c with
  | zero => exact ⟨0, le_refl 0, .zero⟩
  | succ T ih =>
    by_cases hc : c.state = N.qhalt
    · rw [N.trace_halted (T + 1) choices hc]
      exact ⟨0, Nat.zero_le _, .zero⟩
    · rw [hdet.trace_step T choices hc]
      obtain ⟨t, hle, hreach⟩ := ih (fun i => choices ⟨i.val + 1, by omega⟩) _
      exact ⟨t + 1, by omega, .step (Option.some_get _).symm hreach⟩

/-- On every rejected input, every length-`T(|x|)` computation path ends with
    `0` at output cell 1. `NTM.DecidesInTime` encodes rejection only as
    ¬acceptance (cell ≠ `1`, e.g. possibly blank), but `TM.DecidesInTime`
    demands the cell be exactly `0`; this is the missing output discipline,
    satisfied by every machine arising from a DTM decider. -/
def RejectsWithZero (N : NTM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x ∉ L, ∀ choices : Fin (T x.length) → Bool,
    (N.trace (T x.length) choices (N.initCfg x)).output.cells 1 = Γ.zero

/-- **Deterministic NTM decider → DTM decider, same time bound.** The `toTM`
    run is step-exact with the (choice-irrelevant) trace; acceptance transfers
    from the deciding hypothesis and rejection output from `RejectsWithZero`. -/
theorem toTM_decidesInTime {N : NTM n} (hdet : N.Deterministic) {L : Language}
    {T : ℕ → ℕ} (h : N.DecidesInTime L T) (hrej : N.RejectsWithZero L T) :
    N.toTM.DecidesInTime L T := by
  intro x
  obtain ⟨t, hle, hreach⟩ :=
    hdet.toTM_reachesIn_trace (T x.length) (fun _ => false) (N.initCfg x)
  refine ⟨_, t, hle, hreach, h.1 x _, fun hx => ?_, fun hx => hrej x hx _⟩
  obtain ⟨ch, _, hout⟩ := (h.2 x).mp hx
  rw [hdet.trace_congr_choices (T x.length) (N.initCfg x) _ ch]
  exact hout

end NTM

/-- A DTM's NTM embedding is deterministic: both transition functions are
    `tm.δ`. -/
theorem TM.toNTM_deterministic {n : ℕ} (M : TM n) : M.toNTM.Deterministic :=
  fun _ => rfl

/-- A DTM decider's NTM embedding rejects with output `0`: its trace freezes at
    the DTM's halting configuration, whose rejection cell is `0`. -/
theorem TM.toNTM_rejectsWithZero {n : ℕ} {M : TM n} {L : Language} {T : ℕ → ℕ}
    (h : M.DecidesInTime L T) : M.toNTM.RejectsWithZero L T := by
  intro x hx choices
  obtain ⟨c', t, hle, hreach, hhalt, _, hno⟩ := h x
  show (M.toNTM.trace (T x.length) choices (M.initCfg x)).output.cells 1 = Γ.zero
  rw [M.toNTM_trace_of_reachesIn hreach hhalt hle choices]
  exact hno hx

namespace NTM

/-- Padding a 0-work-tape machine with a dummy work tape preserves determinism:
    `pad0`'s transition threads the choice bit only into `N.δ`. -/
theorem pad0_deterministic {N : NTM 0} (hdet : N.Deterministic) :
    (pad0 N).Deterministic := by
  intro b
  funext q si sw so
  show (pad0 N).δ b q si sw so = (pad0 N).δ false q si sw so
  simp only [pad0, hdet.δ_eq]

/-- Padding preserves the zero-on-rejection output discipline (the padded
    machine's output tape tracks the original's verbatim). -/
theorem pad0_rejectsWithZero {N : NTM 0} {L : Language} {T : ℕ → ℕ}
    (hrej : N.RejectsWithZero L T) : (pad0 N).RejectsWithZero L T := by
  intro x hx choices
  rw [(pad0_trace_init N x (T x.length) choices).2.2]
  exact hrej x hx choices

/-- The single-tape simulator of a deterministic machine is deterministic: the
    simulator's transition consults the choice bit only at the GATHER sentinel
    step, where it feeds it to `N.δ`. -/
theorem singleTapeSim_deterministic {k : ℕ} {N : NTM k} (hdet : N.Deterministic) :
    (singleTapeSim N).Deterministic := by
  intro b
  funext state iH wH oH
  show SingleTape.simDelta N b state iH wH oH
    = SingleTape.simDelta N false state iH wH oH
  rcases state with q | d | d | d | d | d | ⟨⟩
  · rfl
  · show SingleTape.gatherStep N b d iH (wH 0) oH
      = SingleTape.gatherStep N false d iH (wH 0) oH
    obtain ⟨q, acc, iSym, oSym, pos, rf, pending⟩ := d
    simp only [SingleTape.gatherStep, hdet.δ_eq]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end NTM

namespace NTM.SingleTape

/-- Writing back the read symbol (the halt step's output action) preserves
    cell 1 outright, provided the cell does not hold `▷`. Strengthens
    `accept_bit_preserved` from the accept bit to the exact cell value. -/
private theorem writeAndMove_readBack_cell1 (t : Tape) (d : Dir3)
    (hns : t.cells 1 ≠ Γ.start) :
    (t.writeAndMove ((TM.readBackWrite t.read : Γw) : Γ) d).cells 1 = t.cells 1 := by
  have hcells : (t.writeAndMove ((TM.readBackWrite t.read : Γw) : Γ) d).cells
      = (t.write ((TM.readBackWrite t.read : Γw) : Γ)).cells := by
    cases d <;> rfl
  rw [hcells, Tape.write]
  by_cases hh0 : t.head = 0
  · simp [hh0]
  · rw [ite_eq_right hh0]
    simp only [Function.update_apply]
    by_cases h1 : (1 : ℕ) = t.head
    · rw [ite_eq_left h1, Tape.read, ← h1]
      cases hg : t.cells 1
      · rfl
      · rfl
      · rfl
      · exact absurd hg hns
    · rw [ite_eq_right h1]

/-- Halt-step correspondence, cells version: when `N` has halted, the
    simulator's one halt step lands with output cell 1 exactly equal to `N`'s
    (via `Corr.outputEq`; strengthens `halted_of_corr`'s accept-bit `↔`). -/
private theorem haltCorr_cell1 {k : ℕ} (N : NTM k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hh : c.state = N.qhalt) :
    ((singleTapeSim N).trace 1 (fun _ => false) c1).output.cells 1
      = c.output.cells 1 := by
  have hst : c1.state = SimQ.run N.qhalt := by rw [hcorr.state, hh]
  have hout : ((singleTapeSim N).trace 1 (fun _ => false) c1).output
      = c1.output.writeAndMove ((TM.readBackWrite c1.output.read : Γw) : Γ)
          (TM.idleDir c1.output.read) := by
    simp only [NTM.trace, singleTapeSim, simDelta, hst, SimQ.run, SimQ.halt,
      reduceCtorEq, ↓reduceIte]
  rw [hout, writeAndMove_readBack_cell1 _ _
    (hcorr.outputEq ▸ hcorr.outputWf 1 le_rfl), hcorr.outputEq]

/-- Reverse halting, cells version (mirrors `halted_singleTapeSim_of_trace_qhalt`, strengthening the
    accept-bit `↔` to equality of output cell 1 via `Corr.outputEq`): if the
    `N`-run induced by an arbitrary simulator stream halts within `Tn` steps,
    the simulator halts within the budget with the same output cell 1. -/
private theorem halts_rev_cell1 {k : ℕ} (N : NTM k) (hk : 1 ≤ k) (ch : ℕ → Bool)
    (x : List Bool) (Tn : ℕ)
    (hhalt : (N.trace Tn (fun i => inducedChoices k ch i.val) (N.initCfg x)).state
      = N.qhalt) :
    ∃ m ≤ Tn * macroBound k Tn + 1,
      (singleTapeSim N).halted
        ((singleTapeSim N).trace m (fun i => ch i.val) ((singleTapeSim N).initCfg x)) ∧
      ((singleTapeSim N).trace m (fun i => ch i.val)
          ((singleTapeSim N).initCfg x)).output.cells 1
        = (N.trace Tn (fun i => inducedChoices k ch i.val)
            (N.initCfg x)).output.cells 1 := by
  classical
  -- the first time `N`'s induced run halts
  have hex : ∃ t, (N.trace t (fun i => inducedChoices k ch i.val) (N.initCfg x)).state
      = N.qhalt := ⟨Tn, hhalt⟩
  have ht0le : Nat.find hex ≤ Tn := Nat.find_min' hex hhalt
  have hth := Nat.find_spec hex
  have hrun : ∀ s, s < Nat.find hex →
      (N.trace s (fun i => inducedChoices k ch i.val) (N.initCfg x)).state ≠ N.qhalt :=
    fun s hs => Nat.find_min hex hs
  have hcorr := corr_trace_macroPos N hk ch x (Nat.find hex) hrun
  -- one halt step lands the simulator in `SimQ.halt`, output cell preserved
  have hhalted := (halted_of_corr N hcorr hth).1
  have hcell := haltCorr_cell1 N hcorr hth
  have hstep : (singleTapeSim N).trace 1 (fun j : Fin 1 => ch (macroPos k (Nat.find hex) + j.val))
      ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
        ((singleTapeSim N).initCfg x))
      = (singleTapeSim N).trace 1 (fun _ => false)
          ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
            ((singleTapeSim N).initCfg x)) := by
    refine (trace_congr_choices N 1 (fun _ => false)
      (fun j => ch (macroPos k (Nat.find hex) + j)) _ ?_).symm
    intro i hi hgather _
    obtain rfl : i = 0 := by omega
    obtain ⟨d, hd⟩ := hgather
    have hd' : ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
        ((singleTapeSim N).initCfg x)).state = SimQ.gather d := hd
    rw [hcorr.state] at hd'
    exact absurd hd'.symm (by simp [SimQ.run, SimQ.gather, reduceCtorEq])
  have hsplit : (singleTapeSim N).trace (macroPos k (Nat.find hex) + 1) (fun i => ch i.val)
      ((singleTapeSim N).initCfg x)
      = (singleTapeSim N).trace 1 (fun _ => false)
          ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
            ((singleTapeSim N).initCfg x)) := by
    rw [(singleTapeSim N).trace_add_fun (macroPos k (Nat.find hex)) 1 ch]
    exact hstep
  -- `N` is frozen between `Nat.find hex` and `Tn`
  have hfreeze : N.trace Tn (fun i => inducedChoices k ch i.val) (N.initCfg x)
      = N.trace (Nat.find hex) (fun i => inducedChoices k ch i.val) (N.initCfg x) :=
    N.trace_mono ht0le (fun i => rfl) hth
  refine ⟨macroPos k (Nat.find hex) + 1, ?_, ?_, ?_⟩
  · have h1 := macroPos_le_mul_macroBound k (Nat.find hex)
    have h2 : Nat.find hex * macroBound k (Nat.find hex) ≤ Tn * macroBound k Tn :=
      Nat.mul_le_mul ht0le (macroBound_mono ht0le)
    omega
  · rw [hsplit]; exact hhalted
  · rw [hsplit, hfreeze]; exact hcell

end NTM.SingleTape

namespace NTM

/-- The single-tape simulator inherits the zero-on-rejection output discipline:
    the simulator's output tape tracks `N`'s exactly (`Corr.outputEq`). -/
theorem singleTapeSim_rejectsWithZero {k : ℕ} {N : NTM k} (hk : 1 ≤ k)
    {L : Language} {T : ℕ → ℕ} (hN : N.AllPathsHaltIn T)
    (hrej : N.RejectsWithZero L T) :
    (singleTapeSim N).RejectsWithZero L (singleTapeSimTime k T) := by
  intro x hx choices
  set ch : ℕ → Bool := fun j =>
    if h : j < singleTapeSimTime k T x.length then choices ⟨j, h⟩ else false with hch
  have hhaltN : (N.trace (T x.length)
      (fun i => SingleTape.inducedChoices k ch i.val) (N.initCfg x)).state = N.qhalt :=
    hN x _
  obtain ⟨m, hm, hhalted, hcell⟩ :=
    SingleTape.halts_rev_cell1 N hk ch x (T x.length) hhaltN
  have hle : m ≤ singleTapeSimTime k T x.length :=
    le_trans hm (SingleTape.mul_macroBound_succ_le k (T x.length) x.length)
  have hagree : ∀ i : Fin m, choices ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = ch i.val := by
    intro i
    simp only [hch]
    rw [dite_eq_left (lt_of_lt_of_le i.isLt hle)]
  rw [(singleTapeSim N).trace_mono hle hagree hhalted, hcell]
  exact hrej x hx _

end NTM

/-- The original bound fits under the simulation overhead bound. -/
private theorem le_singleTapeSimTime (k : ℕ) (T : ℕ → ℕ) (m : ℕ) :
    T m ≤ NTM.singleTapeSimTime k T m := by
  show T m ≤ 16 * (k + 1) * (T m + m + 1) ^ 2
  calc T m ≤ T m + m + 1 := by omega
    _ ≤ (T m + m + 1) ^ 2 := Nat.le_self_pow (by omega) _
    _ ≤ 16 * (k + 1) * (T m + m + 1) ^ 2 :=
        Nat.le_mul_of_pos_left _ (by positivity)

/-- **Single-tape reduction for DTMs.** Every language decidable by a
    `k`-work-tape DTM in time `T` is decidable by a single-work-tape DTM within
    the quadratic overhead bound
    `singleTapeSimTime k T = fun n => 16 * (k + 1) * (T n + n + 1) ^ 2`.
    Chain: embed (`toNTM`), simulate (`singleTapeSim`, or `pad0` for `k = 0`),
    convert back (`toTM`) via determinism. -/
theorem TM.exists_singleTape_decidesInTime {k : ℕ} (M : TM k) {L : Language} {T : ℕ → ℕ}
    (h : M.DecidesInTime L T) :
    ∃ M₁ : TM 1, M₁.DecidesInTime L (NTM.singleTapeSimTime k T) := by
  have hN : M.toNTM.DecidesInTime L T := M.toNTM_decidesInTime h
  have hdet : M.toNTM.Deterministic := M.toNTM_deterministic
  have hrej : M.toNTM.RejectsWithZero L T := TM.toNTM_rejectsWithZero h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨(NTM.pad0 M.toNTM).toTM,
      TM.DecidesInTime.mono (le_singleTapeSimTime 0 T)
        (NTM.toTM_decidesInTime (NTM.pad0_deterministic hdet)
          (NTM.pad0_decidesInTime hN) (NTM.pad0_rejectsWithZero hrej))⟩
  · exact ⟨(NTM.singleTapeSim M.toNTM).toTM,
      NTM.toTM_decidesInTime (NTM.singleTapeSim_deterministic hdet)
        (NTM.singleTapeSim_decidesInTime M.toNTM hk hN)
        (NTM.singleTapeSim_rejectsWithZero hk hN.1 hrej)⟩

end Complexity

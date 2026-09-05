/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Frame
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Rewind

/-!
# Parked tape banks for fixed-time repetition

This internal module tracks exact preservation of every physical work tape not
owned by the active repetition. Such tapes, and the real wrapper output tape,
are parked off the left-end marker and remain unchanged under guarded idle
transitions.

The invariant is established by setup, preserved through a complete positive-
time run and its fixed rewind, and transferred across a nonfinal finish to the
next active bank.

## Main definitions and results

- `NTM.RepeatOtherParked` — all inactive work tapes and real output are parked
- `NTM.RepeatOtherParked.parked` — setup establishes the invariant
- `NTM.RepeatOtherParked.trace_run` — a complete positive-time run preserves it
- `NTM.RepeatOtherParked.trace_rewind` — the fixed rewind preserves it
- `NTM.RepeatOtherParked.finish` — a nonfinal finish transfers it to the next bank
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- Every physical work tape outside bank `j`, together with the real output
tape, is parked off the start marker and satisfies the start invariant. -/
def RepeatOtherParked (j : Fin k)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) : Prop :=
  (∀ i, (repeatTapeCoord i).1 ≠ j → RepeatParked (C.work i)) ∧
    RepeatParked C.output

/-- A guarded idle write-and-move preserves a parked tape exactly. -/
theorem RepeatParked.writeAndMove_idle {t : Tape} (h : RepeatParked t) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ
      (repeatSafeDir t.read (TM.idleDir t.read)) = t := by
  have hread : t.read ≠ Γ.start := h.1.read_ne_start h.2
  rw [repeatSafeDir_eq _ _ TM.idleDir_right_of_start]
  exact TM.tape_writeAndMove_stable t h.2 h.1.2

/-- The canonical parked blank tape satisfies `RepeatParked`. -/
theorem repeatParked_parkedBlank : RepeatParked parkedBlank := by
  refine ⟨?_, ?_⟩
  · exact Tape.StartInvariant.init_nil.move .right
  · rfl

/-- The canonical parked source input satisfies `RepeatParked`. -/
theorem repeatParked_parkedInput (x : List Bool) : RepeatParked (parkedInput x) := by
  refine ⟨?_, ?_⟩
  · exact (Tape.StartInvariant.init_ofBool x).move .right
  · rfl

/-- The configuration after the first setup transition has every bank other
than any designated active bank, and the real output, parked. -/
theorem RepeatOtherParked.parked (tm : NTM n) (k T : ℕ) (x : List Bool) (j : Fin k) :
    RepeatOtherParked j (repeatParkedCfg tm k T x) := by
  refine ⟨?_, repeatParked_parkedBlank⟩
  intro i _
  exact repeatParked_parkedBlank

/-- The second setup transition activates bank zero and leaves every other
bank and the real output parked. -/
theorem RepeatOtherParked.begin (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (choice : Fin 1 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    RepeatOtherParked j
      ((repeatAtTime tm k T).trace 1 choice (repeatParkedCfg tm k T x)) := by
  dsimp only
  constructor
  · intro i hi
    have hp := repeatParked_parkedBlank
    have hstable := hp.writeAndMove_idle
    simp [trace, repeatAtTime, repeatParkedCfg, repeatGuardTransition,
      repeatPositionBankDirs, hk, hi]
    change RepeatParked (parkedBlank.writeAndMove
      (TM.readBackWrite parkedBlank.read).toΓ
      (repeatSafeDir parkedBlank.read (TM.idleDir parkedBlank.read)))
    rw [hstable]
    exact hp
  · have hp := repeatParked_parkedBlank
    have hstable := hp.writeAndMove_idle
    simp [trace, repeatAtTime, repeatParkedCfg, repeatGuardTransition, hk]
    change RepeatParked (parkedBlank.writeAndMove
      (TM.readBackWrite parkedBlank.read).toΓ
      (repeatSafeDir parkedBlank.read (TM.idleDir parkedBlank.read)))
    rw [hstable]
    exact hp

/-- One simulation slot preserves all parked tapes outside the active bank and
the real output tape. -/
theorem RepeatOtherParked.run (tm : NTM n)
    {C : Cfg (k * (n + 1)) (RepeatQ tm k T)} {j : Fin k} {t : Fin T}
    {q : tm.Q} {votes : Fin k → Bool} (hparked : RepeatOtherParked j C)
    (hstate : C.state = .run j t q votes) (choice : Fin 1 → Bool) :
    RepeatOtherParked j ((repeatAtTime tm k T).trace 1 choice C) := by
  constructor
  · intro i hi
    have hp := hparked.1 i hi
    have hstable := hp.writeAndMove_idle
    have heq : ((repeatAtTime tm k T).trace 1 choice C).work i = C.work i := by
      cases C with
      | mk state input work output =>
        simp only at hstate hstable ⊢
        subst state
        by_cases hq : q = tm.qhalt
        · simpa [trace, repeatAtTime, repeatGuardTransition, hq,
            repeatPaddingDirs] using hstable
        · simpa [trace, repeatAtTime, repeatGuardTransition, hq,
            repeatBankWrites, repeatBankDirs, hi] using hstable
    rw [heq]
    exact hp
  · have hp := hparked.2
    have hstable := hp.writeAndMove_idle
    have heq : ((repeatAtTime tm k T).trace 1 choice C).output = C.output := by
      cases C with
      | mk state input work output =>
        simp only at hstate hstable ⊢
        subst state
        by_cases hq : q = tm.qhalt
        · simpa [trace, repeatAtTime, repeatGuardTransition, hq,
            repeatPaddingDirs] using hstable
        · simpa [trace, repeatAtTime, repeatGuardTransition, hq] using hstable
    rw [heq]
    exact hp

/-- Every prefix of a positive-time run preserves all parked tapes outside the
active bank. -/
theorem RepeatOtherParked.trace_run_prefix (tm : NTM n) (hT : 0 < T)
    (j : Fin k) (votes : Fin k → Bool) (choices : Fin T → Bool)
    (c₀ : Cfg n tm.Q) (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = .run j ⟨0, hT⟩ c₀.state votes)
    (hsim : RepeatSimulates tm j c₀.state c₀ C₀)
    (hinp : C₀.input.StartInvariant) (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (hparked : RepeatOtherParked j C₀)
    (m : ℕ) (hm : m ≤ T) :
    RepeatOtherParked j
      ((repeatAtTime tm k T).trace m (fun i => choices ⟨i.val, by omega⟩) C₀) := by
  induction m with
  | zero => simpa [trace] using hparked
  | succ m ih =>
    have hm' : m < T := by omega
    let C := (repeatAtTime tm k T).trace m
      (fun i => choices ⟨i.val, by omega⟩) C₀
    let g : ℕ → Bool := fun a => if ha : a < T then choices ⟨a, ha⟩ else false
    have hg : (fun i : Fin m => g i.val) =
        fun i => choices ⟨i.val, by omega⟩ := by
      funext i
      simp [g, show i.val < T by omega]
    have hprefix := repeatAtTime_trace_run_prefix tm hT j votes g
      c₀ C₀ hstate hsim hinp hwork hout m hm'
    have hCstate : C.state = .run j ⟨m, hm'⟩
        (tm.trace m (fun i => choices ⟨i.val, by omega⟩) c₀).state votes := by
      rw [hg] at hprefix
      simpa [C] using hprefix.1
    erw [(repeatAtTime tm k T).trace_add m 1]
    apply RepeatOtherParked.run tm
    · exact ih (by omega)
    · exact hCstate

/-- A complete positive-time simulation run preserves all parked tapes outside
the active bank and the real output tape. -/
theorem RepeatOtherParked.trace_run (tm : NTM n) (hT : 0 < T)
    (j : Fin k) (votes : Fin k → Bool) (choices : Fin T → Bool)
    (c₀ : Cfg n tm.Q) (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = .run j ⟨0, hT⟩ c₀.state votes)
    (hsim : RepeatSimulates tm j c₀.state c₀ C₀)
    (hinp : C₀.input.StartInvariant) (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (hparked : RepeatOtherParked j C₀) :
    RepeatOtherParked j ((repeatAtTime tm k T).trace T choices C₀) := by
  exact RepeatOtherParked.trace_run_prefix tm hT j votes choices c₀ C₀
    hstate hsim hinp hwork hout hparked T (by omega)

/-- The complete fixed rewind preserves every inactive parked tape and the real
output tape. -/
theorem RepeatOtherParked.trace_rewind (tm : NTM n)
    (j : Fin k) (q : tm.Q) (votes : Fin k → Bool)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C.state = .rewind j ⟨0, by omega⟩ q votes false (fun _ => false))
    (hinv : C.input.StartInvariant)
    (hactiveInv : ∀ i, (C.work (repeatTapeIdx j i)).StartInvariant)
    (hinputHead : C.input.head ≤ T)
    (hactiveHead : ∀ i, (C.work (repeatTapeIdx j i)).head ≤ T)
    (hparked : RepeatOtherParked j C) (choices : Fin (T + 1) → Bool) :
    RepeatOtherParked j ((repeatAtTime tm k T).trace (T + 1) choices C) := by
  have hrewind := repeatAtTime_trace_rewind_bound tm j q votes C hstate hinv
    hactiveInv hinputHead hactiveHead hparked.1 hparked.2 choices
  dsimp only at hrewind
  exact ⟨fun i hi => by rw [hrewind.2.2.2.2.1 i hi]; exact hparked.1 i hi,
    by rw [hrewind.2.2.2.2.2]; exact hparked.2⟩

/-- A nonfinal finish transfers the parked invariant to the next active bank,
provided the just-completed active bank has been parked by fixed rewind. -/
theorem RepeatOtherParked.finish (tm : NTM n)
    {C : Cfg (k * (n + 1)) (RepeatQ tm k T)} {j : Fin k}
    {q : tm.Q} {votes : Fin k → Bool} (hparked : RepeatOtherParked j C)
    (hactive : ∀ i, RepeatParked (C.work (repeatTapeIdx j i)))
    (hstate : C.state = .finish j q votes) (hj : j.val + 1 < k)
    (choice : Fin 1 → Bool) :
    let j' : Fin k := ⟨j.val + 1, hj⟩
    RepeatOtherParked j' ((repeatAtTime tm k T).trace 1 choice C) := by
  let j' : Fin k := ⟨j.val + 1, hj⟩
  dsimp only
  constructor
  · intro i hi
    have hp : RepeatParked (C.work i) := by
      by_cases hij : (repeatTapeCoord i).1 = j
      · have hidx : repeatTapeIdx j (repeatTapeCoord i).2 = i := by
          rw [← hij]
          exact finProdFinEquiv.apply_symm_apply i
        rw [← hidx]
        exact hactive _
      · exact hparked.1 i hij
    have hstable := hp.writeAndMove_idle
    have heq : ((repeatAtTime tm k T).trace 1 choice C).work i = C.work i := by
      cases C with
      | mk state input work output =>
        simp only at hstate hstable ⊢
        subst state
        simpa [trace, repeatAtTime, repeatGuardTransition, hj,
          repeatPositionBankDirs, hi] using hstable
    rw [heq]
    exact hp
  · have hp := hparked.2
    have hstable := hp.writeAndMove_idle
    have heq : ((repeatAtTime tm k T).trace 1 choice C).output = C.output := by
      cases C with
      | mk state input work output =>
        simp only at hstate hstable ⊢
        subst state
        simpa [trace, repeatAtTime, repeatGuardTransition, hj] using hstable
    rw [heq]
    exact hp

end NTM

end Complexity

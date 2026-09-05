/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators

/-!
# Running one nondeterministic path deterministically

An `NTM`'s transition function has exactly the shape of a `TM`'s, plus a
`Bool`. Feeding that `Bool` from a dedicated work tape — one cell per step,
scanned left to right and written back unchanged — turns the nondeterministic
machine into a deterministic one whose run is the chosen path.

This is the primitive that lets deterministic machines reason about
nondeterministic runs: a decider that must evaluate "does `tm` accept `x` along
choice sequence `c`" places `c` on the choice tape and runs `choiceTM tm`.

## Main definitions

- `NTM.choiceTM` — the deterministic machine with a choice tape appended
- `NTM.dropChoice` — forget the choice tape from a configuration
- `NTM.choiceStream` — the choice bits under and to the right of the head

## Main results

- `NTM.choiceTM_step` — one step of `choiceTM` is one step of the path
- `NTM.choiceTM_simulates` — a `T`-step run of `choiceTM` is `tm.trace T`
  along the choice bits found on the tape
-/

@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- The configuration update inlined in `TM.step`. -/
def stepCfg (tm : TM k) (c : Cfg k tm.Q) : Cfg k tm.Q :=
  let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
    tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
  { state := q'
    input := c.input.move inDir
    work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
    output := c.output.writeAndMove outWrite outDir }

/-- A non-halted configuration steps to `stepCfg`. -/
theorem step_of_not_halted (tm : TM k) {c : Cfg k tm.Q} (h : c.state ≠ tm.qhalt) :
    tm.step c = some (tm.stepCfg c) := by
  unfold TM.step
  rw [ite_eq_right h]
  rfl

end TM

namespace NTM

variable {k : ℕ}

/-- The deterministic machine that runs one path of `tm`, reading its choice
bits from the appended last work tape: each step consults the cell under that
head, writes it back unchanged, and advances the head one cell right. -/
def choiceTM (tm : NTM k) : TM (k + 1) where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ q iHead wHeads oHead :=
    let cHead := wHeads (Fin.last k)
    let r := tm.δ (decide (cHead = Γ.one)) q iHead (fun i => wHeads i.castSucc) oHead
    (r.1, Fin.snoc r.2.1 (TM.readBackWrite cHead), r.2.2.1,
      r.2.2.2.1, Fin.snoc r.2.2.2.2.1 Dir3.right, r.2.2.2.2.2)
  δ_right_of_start := by
    intro q iHead wHeads oHead
    have h := tm.δ_right_of_start (decide (wHeads (Fin.last k) = Γ.one)) q iHead
      (fun i => wHeads i.castSucc) oHead
    dsimp only at h ⊢
    refine ⟨h.1, ?_, h.2.2⟩
    intro i
    refine Fin.lastCases ?_ ?_ i
    · intro _
      simp
    · intro j hj
      rw [Fin.snoc_castSucc]
      exact h.2.1 j (by simpa using hj)

/-- One step of an NTM along a fixed choice bit: the configuration update
inlined in `NTM.trace`. -/
def stepCfg (tm : NTM k) (b : Bool) (c : Cfg k tm.Q) : Cfg k tm.Q :=
  let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
    tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
  { state := q'
    input := c.input.move inDir
    work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
    output := c.output.writeAndMove outWrite outDir }

/-- Unfolding one non-halted step of `trace`. -/
theorem trace_succ_of_not_halted (tm : NTM k) (T : ℕ) (choices : Fin (T + 1) → Bool)
    {c : Cfg k tm.Q} (h : c.state ≠ tm.qhalt) :
    tm.trace (T + 1) choices c =
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
        (stepCfg tm (choices ⟨0, Nat.zero_lt_succ T⟩) c) := by
  rw [NTM.trace]
  simp [h, stepCfg]

/-- Forget the choice tape from a configuration. -/
def dropChoice {Q : Type} (c : Cfg (k + 1) Q) : Cfg k Q where
  state := c.state
  input := c.input
  work := fun i => c.work i.castSucc
  output := c.output

/-- The choice bits under and to the right of the choice head. -/
def choiceStream {Q : Type} (c : Cfg (k + 1) Q) (j : ℕ) : Bool :=
  decide ((c.work (Fin.last k)).cells ((c.work (Fin.last k)).head + j) = Γ.one)

/-- **One step of `choiceTM` is one step of the chosen path.** The choice tape
is written back unchanged and its head advances one cell. -/
theorem choiceTM_step (tm : NTM k) (c : Cfg (k + 1) tm.Q) (hhalt : c.state ≠ tm.qhalt)
    (hread : (c.work (Fin.last k)).read ≠ Γ.start) :
    ∃ c₁, (choiceTM tm).step c = some c₁ ∧
      dropChoice c₁ = stepCfg tm (choiceStream c 0) (dropChoice c) ∧
      c₁.work (Fin.last k) = (c.work (Fin.last k)).move Dir3.right := by
  refine ⟨(choiceTM tm).stepCfg c, TM.step_of_not_halted _ hhalt, ?_, ?_⟩
  · refine Cfg.ext rfl rfl ?_ rfl
    funext i
    simp [TM.stepCfg, choiceTM, stepCfg, dropChoice, choiceStream, Tape.read]
  · simp only [TM.stepCfg, choiceTM, Fin.snoc_last]
    exact TM.writeAndMove_readBack _ hread Dir3.right

/-- **A `T`-step run of `choiceTM` is the `T`-step trace of `tm` along the
choice bits on the tape.** The run stops early exactly when the path halts;
the choice tape is left untouched apart from its head, which advances one cell
per step. -/
theorem choiceTM_simulates (tm : NTM k) (T : ℕ) (c : Cfg (k + 1) tm.Q)
    (hinv : (c.work (Fin.last k)).StartInvariant)
    (hhead : 1 ≤ (c.work (Fin.last k)).head) :
    ∃ (c' : Cfg (k + 1) tm.Q) (t : ℕ), t ≤ T ∧
      (choiceTM tm).reachesIn t c c' ∧
      (t < T → (choiceTM tm).halted c') ∧
      dropChoice c' = tm.trace T (fun j => choiceStream c j.val) (dropChoice c) := by
  induction T generalizing c with
  | zero => exact ⟨c, 0, le_rfl, TM.reachesIn.zero, by omega, rfl⟩
  | succ T ih =>
    by_cases hhalt : c.state = tm.qhalt
    · refine ⟨c, 0, Nat.zero_le _, TM.reachesIn.zero, fun _ => hhalt, ?_⟩
      rw [NTM.trace]
      simp [dropChoice, hhalt]
    · have hread : (c.work (Fin.last k)).read ≠ Γ.start := hinv.read_ne_start hhead
      obtain ⟨c₁, hstep, hdrop, hchoice⟩ := choiceTM_step tm c hhalt hread
      have hinv₁ : (c₁.work (Fin.last k)).StartInvariant := by
        rw [hchoice]
        exact hinv
      have hhead₁ : 1 ≤ (c₁.work (Fin.last k)).head := by
        rw [hchoice]
        show 1 ≤ (c.work (Fin.last k)).head + 1
        omega
      obtain ⟨c', t, hle, hreach, hstop, heq⟩ := ih c₁ hinv₁ hhead₁
      refine ⟨c', t + 1, by omega, TM.reachesIn.step hstep hreach, fun _ => hstop (by omega), ?_⟩
      rw [trace_succ_of_not_halted tm T _ (by simpa [dropChoice] using hhalt), ← hdrop]
      rw [heq]
      congr 1
      funext j
      have harg : ((c.work (Fin.last k)).move Dir3.right).head + j.val
          = (c.work (Fin.last k)).head + (j.val + 1) := by
        show (c.work (Fin.last k)).head + 1 + j.val = _
        omega
      show choiceStream c₁ j.val = choiceStream c (j.val + 1)
      simp only [choiceStream, hchoice, harg]
      rfl

end NTM

end Complexity

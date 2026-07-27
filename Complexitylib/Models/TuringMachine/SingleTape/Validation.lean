/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.SingleTape.Internal.Delta
meta import Complexitylib.Models.TuringMachine.SingleTape.Internal.Delta

/-!
# Single-tape simulation — executable validation (regression suite)

A computable cross-check that `NTM.singleTapeSim` actually simulates its source
machine, run on concrete tiny machines. Built via a computable step-iterator
(`simStep`, using `simDelta` directly) so it bypasses `singleTapeSim`'s
*noncomputable* `Fintype`/`DecidableEq` instances. The `#guard`s fail the build
if a future change breaks the phase logic.

This file is **not** imported by the library aggregation; build it explicitly
with
`lake build --wfail Complexitylib.Models.TuringMachine.SingleTape.Validation`.

These tests caught two real design bugs (see commit history): a head moving off
cell 0 never getting a marker, and a misaligned `scatter1 → scatter2` position
hand-off. They cover off-0 moves, right/left moves with writes, repeated
materialization, distant writes read back, and `k = 2` tape interleaving.
-/

@[expose] public section

namespace Complexity

namespace NTM.SingleTape.Validation

open NTM TM

/-- One computable simulator step (mirrors `trace`'s step; halts at `SimQ.halt`). -/
private def simStep {k : ℕ} (N : NTM k) (cfg : Cfg 1 (SimQ k N.Q)) :
    Cfg 1 (SimQ k N.Q) :=
  match cfg.state with
  | SimQ.halt => cfg
  | _ =>
    let r := simDelta N false cfg.state cfg.input.read (fun i => (cfg.work i).read) cfg.output.read
    { state := r.1, input := cfg.input.move r.2.2.2.1,
      work := fun i => (cfg.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
      output := cfg.output.writeAndMove r.2.2.1 r.2.2.2.2.2 }

/-- One computable source-machine step (halts at `N.qhalt`). -/
private def nStep {k : ℕ} (N : NTM k) [DecidableEq N.Q]
    (cfg : Cfg k N.Q) : Cfg k N.Q :=
  if cfg.state = N.qhalt then cfg
  else
    let r := N.δ false cfg.state cfg.input.read (fun i => (cfg.work i).read) cfg.output.read
    { state := r.1, input := cfg.input.move r.2.2.2.1,
      work := fun i => (cfg.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
      output := cfg.output.writeAndMove r.2.2.1 r.2.2.2.2.2 }

/-- Run `singleTapeSim`'s step `n` times from the simulator's initial config. -/
private def simResult {k : ℕ} (N : NTM k) (n : ℕ) : Γ :=
  let rec go : ℕ → Cfg 1 (SimQ k N.Q) → Cfg 1 (SimQ k N.Q)
    | 0, c => c
    | m + 1, c => go m (simStep N c)
  (go n (Cfg.init (SimQ.run N.qstart) [])).output.cells 1

/-- Run `N`'s step `n` times from `N`'s initial config. -/
private def nResult {k : ℕ} (N : NTM k) [DecidableEq N.Q] (n : ℕ) : Γ :=
  let rec go : ℕ → Cfg k N.Q → Cfg k N.Q
    | 0, c => c
    | m + 1, c => go m (nStep N c)
  (go n (Cfg.init N.qstart [])).output.cells 1

-- ── Test 1: k=1, write/read round-trip + right/left moves + materialization ──
private def δ1 : Bool → Fin 5 → Γ → (Fin 1 → Γ) → Γ →
    Fin 5 × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  fun _ q iHead wHeads oHead => match q.val with
    | 0 => (1, fun _ => .blank, .blank, .right, fun _ => .right, .right)
    | 1 => (2, fun _ => .one, .blank, idleDir iHead, fun _ => .right, idleDir oHead)
    | 2 => (3, fun _ => .zero, .blank, idleDir iHead,
            fun _ => moveLeftDir (wHeads 0), idleDir oHead)
    | 3 => if wHeads 0 = .one
           then (4, fun _ => .one, .one, idleDir iHead, fun _ => idleDir (wHeads 0), idleDir oHead)
           else (4, fun _ => .blank, .zero, idleDir iHead,
                 fun _ => idleDir (wHeads 0), idleDir oHead)
    | _ => (4, fun _ => .blank, .blank, idleDir iHead, fun _ => idleDir (wHeads 0), idleDir oHead)

private def N1 : NTM 1 where
  Q := Fin 5; qstart := 0; qhalt := 4; δ := δ1; δ_right_of_start := by decide

#guard simResult N1 500 = nResult N1 20
#guard nResult N1 20 = Γ.one

-- ── Test 2: k=2, interleaved tapes, heads at different positions ──
private def δ2 : Bool → Fin 5 → Γ → (Fin 2 → Γ) → Γ →
    Fin 5 × (Fin 2 → Γw) × Γw × Dir3 × (Fin 2 → Dir3) × Dir3 :=
  fun _ q iHead wHeads oHead => match q.val with
    | 0 => (1, fun _ => .blank, .blank, .right, fun _ => .right, .right)
    | 1 => (2, fun i => if i.val = 0 then .one else .zero, .blank, idleDir iHead,
            fun i => if i.val = 0 then .right else idleDir (wHeads i), idleDir oHead)
    | 2 => (3, fun i => readBackWrite (wHeads i), .blank, idleDir iHead,
            fun i => if i.val = 0 then moveLeftDir (wHeads 0) else idleDir (wHeads i),
            idleDir oHead)
    | 3 => if wHeads 0 = .one ∧ wHeads 1 = .zero
           then (4, fun i => readBackWrite (wHeads i), .one, idleDir iHead,
                 fun i => idleDir (wHeads i), idleDir oHead)
           else (4, fun i => readBackWrite (wHeads i), .zero, idleDir iHead,
                 fun i => idleDir (wHeads i), idleDir oHead)
    | _ => (4, fun i => readBackWrite (wHeads i), .blank, idleDir iHead,
            fun i => idleDir (wHeads i), idleDir oHead)

private def N2 : NTM 2 where
  Q := Fin 5; qstart := 0; qhalt := 4; δ := δ2; δ_right_of_start := by decide

#guard simResult N2 800 = nResult N2 20
#guard nResult N2 20 = Γ.one

-- ── Test 3: k=1, head journey 0→1→2→3→2→1, distant write survives + read back ──
private def δ3 : Bool → Fin 7 → Γ → (Fin 1 → Γ) → Γ →
    Fin 7 × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  fun _ q iHead wHeads oHead => match q.val with
    | 0 => (1, fun _ => .blank, .blank, .right, fun _ => .right, .right)
    | 1 => (2, fun _ => .one, .blank, idleDir iHead, fun _ => .right, idleDir oHead)
    | 2 => (3, fun _ => .zero, .blank, idleDir iHead, fun _ => .right, idleDir oHead)
    | 3 => (4, fun _ => .one, .blank, idleDir iHead, fun _ => moveLeftDir (wHeads 0), idleDir oHead)
    | 4 => (5, fun _ => readBackWrite (wHeads 0), .blank, idleDir iHead,
            fun _ => moveLeftDir (wHeads 0), idleDir oHead)
    | 5 => if wHeads 0 = .one
           then (6, fun _ => readBackWrite (wHeads 0), .one, idleDir iHead,
                 fun _ => idleDir (wHeads 0), idleDir oHead)
           else (6, fun _ => readBackWrite (wHeads 0), .zero, idleDir iHead,
                 fun _ => idleDir (wHeads 0), idleDir oHead)
    | _ => (6, fun _ => readBackWrite (wHeads 0), .blank, idleDir iHead,
            fun _ => idleDir (wHeads 0), idleDir oHead)

private def N3 : NTM 1 where
  Q := Fin 7; qstart := 0; qhalt := 6; δ := δ3; δ_right_of_start := by decide

#guard simResult N3 1500 = nResult N3 30
#guard nResult N3 30 = Γ.one

end NTM.SingleTape.Validation

end Complexity

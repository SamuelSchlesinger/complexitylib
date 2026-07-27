/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Combinators
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Pair-splitting machine — definitions

This file defines the deterministic machine that decodes the library's
self-delimiting binary pair from the input tape onto two work tapes. Proofs
and the public compositional specification live in the adjacent internal and
surface modules.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Control states of `pairSplitCoreTM`: `.init` steps off `▷`; `.scanX`,
`.afterFalse`, and `.writeTrue` decode the doubled-bit prefix (with `01` as
separator); `.copyY` copies the suffix; `.done` is the halting state. -/
inductive PairSplitPhase where
  | init
  | scanX
  | afterFalse
  | writeTrue
  | copyY
  | done
  deriving DecidableEq

instance : Fintype PairSplitPhase where
  elems := {.init, .scanX, .afterFalse, .writeTrue, .copyY, .done}
  complete := by
    intro q
    cases q <;> simp

variable {k : ℕ}

/-- Idle pair-split transition. It preserves every work and output tape away
from the left-end marker; a tape on `▷` takes the structurally required right
move. Unlike the generic `allIdle`, it writes back the symbols under the heads
instead of blanking them. -/
def pairSplitIdle {k : ℕ} (newState : PairSplitPhase)
    (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    PairSplitPhase × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  (newState, fun i => readBackWrite (wHeads i), readBackWrite oHead,
    idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

/-- `pairSplitIdle` satisfies the mandatory right move at every left-end
marker. -/
theorem rightOfStart_pairSplitIdle (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  rightOfStart_allIdle iHead wHeads oHead

/-- Core pair-splitting machine. On well-formed inputs `pair x y`, it decodes
the doubled-bit prefix onto work tape `xIdx` and copies the remaining suffix to
work tape `yIdx`. Invalid inputs halt early; clients that need total malformed
input semantics must use a parser with a distinct failure result, since this
machine's halting state does not distinguish success from early failure. -/
def pairSplitCoreTM (xIdx yIdx : Fin k) : TM k where
  Q := PairSplitPhase
  qstart := .init
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .init =>
        (.scanX,
          fun i => readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead,
          fun i => idleDir (wHeads i),
          idleDir oHead)
    | .scanX =>
        if iHead = Γ.zero then
          (.afterFalse,
            fun i => readBackWrite (wHeads i), readBackWrite oHead,
            Dir3.right,
            fun i => idleDir (wHeads i),
            idleDir oHead)
        else if iHead = Γ.one then
          (.writeTrue,
            fun i => readBackWrite (wHeads i), readBackWrite oHead,
            Dir3.right,
            fun i => idleDir (wHeads i),
            idleDir oHead)
        else
          pairSplitIdle .done iHead wHeads oHead
    | .afterFalse =>
        if iHead = Γ.zero then
          (.scanX,
            fun i => if i = xIdx then Γw.zero else readBackWrite (wHeads i),
            readBackWrite oHead,
            Dir3.right,
            fun i => if i = xIdx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else if iHead = Γ.one then
          (.copyY,
            fun i => readBackWrite (wHeads i), readBackWrite oHead,
            Dir3.right,
            fun i => idleDir (wHeads i),
            idleDir oHead)
        else
          pairSplitIdle .done iHead wHeads oHead
    | .writeTrue =>
        if iHead = Γ.one then
          (.scanX,
            fun i => if i = xIdx then Γw.one else readBackWrite (wHeads i),
            readBackWrite oHead,
            Dir3.right,
            fun i => if i = xIdx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else
          pairSplitIdle .done iHead wHeads oHead
    | .copyY =>
        if iHead = Γ.blank then
          pairSplitIdle .done iHead wHeads oHead
        else
          let w : Γw :=
            match iHead with
            | .zero => .zero
            | .one => .one
            | .blank => .blank
            | .start => .blank
          (.copyY,
            fun i => if i = yIdx then w else readBackWrite (wHeads i),
            readBackWrite oHead,
            Dir3.right,
            fun i => if i = yIdx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
    | .done =>
        pairSplitIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .init =>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
    | .scanX =>
        dsimp only []
        split
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
        · split
          · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
          · exact rightOfStart_pairSplitIdle iHead wHeads oHead
    | .afterFalse =>
        dsimp only []
        split
        · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
          intro i hwi
          simp only []
          split
          · rfl
          · exact idleDir_right_of_start hwi
        · split
          · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
          · exact rightOfStart_pairSplitIdle iHead wHeads oHead
    | .writeTrue =>
        dsimp only []
        split
        · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
          intro i hwi
          simp only []
          split
          · rfl
          · exact idleDir_right_of_start hwi
        · exact rightOfStart_pairSplitIdle iHead wHeads oHead
    | .copyY =>
        dsimp only []
        split
        · exact rightOfStart_pairSplitIdle iHead wHeads oHead
        · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
          intro i hwi
          simp only []
          split
          · rfl
          · exact idleDir_right_of_start hwi
    | .done =>
        exact rightOfStart_pairSplitIdle iHead wHeads oHead

/-- Exact running time of the core split phase on canonical `pair x y`
inputs, including its initial controller step. -/
def pairSplitCoreTime (xLen yLen : ℕ) : ℕ :=
  2 * xLen + yLen + 4

end TM

end Complexity

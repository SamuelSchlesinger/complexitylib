/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHornerLoop
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiply

/-!
# Unrestricted depth-three lower bound: tape horner prepare

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHornerPrepare.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHornerPrepare

open TapeMultiProgram TapeRouting TapeRegister TapeUnary TapeHornerMultiply

/-- Register allocation for the horner prepare routine. -/
structure Clean (σ : TapeStore) : Prop where
  count : σ loop2 = []
  cursor : σ loop3 = []
  countScratch : σ loop4 = []
  mulScratch : σ loop5 = []
  coefficient : σ scratchB = []
  accumulator : σ accumBits = []

/-- Control states for the zero stage of the horner prepare routine. -/
abbrev ZeroState := TapeCopy.State ⊕ TapeFill.FillState
/-- Control states for the count stage of the horner prepare routine. -/
abbrev CountState := ZeroState ⊕ TapeCopy.State
/-- Control states for the cursor stage of the horner prepare routine. -/
abbrev CursorState := CountState ⊕ TapeCopy.State
/-- Control states of the horner prepare routine. -/
abbrev State := CursorState ⊕ TapeMultiply.State

/-- Transition function for the zero stage of the horner prepare routine. -/
def zeroProgram : TapeMultiProgram ZeroState :=
  joinCode (TapeCopy.code ringDegree scratchA) (TapeFill.fillProgram scratchA accumBits false)
    (fun _ => TapeFill.fillStart)

/-- Transition function for the count stage of the horner prepare routine. -/
def countProgram : TapeMultiProgram CountState :=
  joinCode zeroProgram (TapeCopy.code coeffCount loop2) (fun _ => TapeCopy.State.start)

/-- Transition function for the cursor stage of the horner prepare routine. -/
def cursorProgram : TapeMultiProgram CursorState :=
  joinCode countProgram (TapeCopy.code coeffCount loop4) (fun _ => TapeCopy.State.start)

/-- Transition function of the horner prepare routine. -/
def program : TapeMultiProgram State :=
  joinCode cursorProgram (TapeMultiply.program loop4 ringDegree loop5 loop3)
    (fun _ => TapeMultiply.start)

/-- Initial control state of the horner prepare routine. -/
def start : State := .inl (.inl (.inl (.inl TapeCopy.State.start)))
/-- Terminal control state of the horner prepare routine. -/
def done : State := .inr TapeMultiply.done

/-- Transition budget for the horner prepare routine. -/
def cost (r t : ℕ) : ℕ := t * (10 * r + 18) + 10 * r + 22

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_zero (σ : TapeStore) (r : ℕ)
    (hr : σ ringDegree = List.replicate r true)
    (hs : σ scratchA = []) (ha : σ accumBits = []) :
    RunsIn zeroProgram.step (cfg (.inl TapeCopy.State.start) (storeTapes σ))
      (cfg (.inr TapeFill.fillDone)
        (storeTapes (Function.update σ accumBits (List.replicate r false)))) (10 * r + 8) := by
  let U := Function.update σ scratchA (σ ringDegree)
  have hc := TapeStoreRuns.copy (by decide : ringDegree ≠ scratchA) σ hs
  have hf := TapeStoreRuns.fill (by decide : scratchA ≠ accumBits) false U r
    (by simp [U, hr])
  have hall := join_runs (TapeCopy.code ringDegree scratchA)
    (TapeFill.fillProgram scratchA accumBits false) (fun _ => TapeFill.fillStart) hc rfl hf
  have hfinal : Function.update (Function.update U scratchA []) accumBits
      (List.replicate r false ++ U accumBits) =
      Function.update σ accumBits (List.replicate r false) := by
    have hu : Function.update U scratchA [] = σ := by
      simp only [U, Function.update_idem, ← hs, Function.update_eq_self]
    rw [hu]
    simp [U, ha, accumBits, scratchA]
  have ht : 2 * r + 4 + 1 + (8 * r + 3) = 10 * r + 8 := by omega
  simpa only [zeroProgram, hfinal, hr, List.length_replicate, ht] using hall

theorem runs_prepare (σ : TapeStore) (r t : ℕ) (hW : Workspace σ r) (hC : Clean σ)
    (ht : σ coeffCount = List.replicate t true) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (TapeHornerLoop.frame σ t (t * r) (List.replicate r false))))
      (cost r t) := by
  let U := Function.update σ accumBits (List.replicate r false)
  let V := Function.update U loop2 (List.replicate t true)
  let W := Function.update V loop4 (List.replicate t true)
  have hz := runs_zero σ r hW.degree hW.scratch_empty hC.accumulator
  have hc := TapeStoreRuns.copy (by decide : coeffCount ≠ loop2) U
    (by simp [U, hC.count, accumBits, loop2])
  have hc' : RunsIn (TapeCopy.code coeffCount loop2).step
      (cfg TapeCopy.State.start (storeTapes U)) (cfg TapeCopy.State.done (storeTapes V))
      (2 * t + 4) := by
    simpa [V, U, ht, coeffCount, accumBits] using hc
  have hzc := join_runs zeroProgram (TapeCopy.code coeffCount loop2)
    (fun _ => TapeCopy.State.start) hz rfl hc'
  have hmcopy := TapeStoreRuns.copy (by decide : coeffCount ≠ loop4) V
    (by simp [V, U, hC.countScratch, loop4, loop2, accumBits])
  have hmcopy' : RunsIn (TapeCopy.code coeffCount loop4).step
      (cfg TapeCopy.State.start (storeTapes V)) (cfg TapeCopy.State.done (storeTapes W))
      (2 * t + 4) := by
    simpa [W, V, U, ht, coeffCount, loop2, accumBits] using hmcopy
  have hp := join_runs countProgram (TapeCopy.code coeffCount loop4)
    (fun _ => TapeCopy.State.start) hzc rfl hmcopy'
  have hm := TapeMultiply.runs_mul
    (outer := loop4) (source := ringDegree) (scratch := loop5) (destination := loop3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (storeTapes V) t r 0
  have hi : TapeMultiply.tapes loop4 ringDegree loop5 loop3 (storeTapes V) t r 0 0 =
      storeTapes W := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases hd : q = ringDegree <;>
      by_cases h5 : q = loop5 <;> by_cases h3 : q = loop3 <;>
      simp_all [TapeMultiply.tapes, TapeCopy.onPair, storeTapes, counterTape,
        W, V, U, Function.update, hW.degree, hC.mulScratch, hC.cursor,
        loop4, ringDegree, loop5, loop3, loop2, accumBits]
  have ho : TapeMultiply.tapes loop4 ringDegree loop5 loop3 (storeTapes V) 0 r 0 (0 + t * r) =
      storeTapes (Function.update V loop3 (List.replicate (t * r) true)) := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases hd : q = ringDegree <;>
      by_cases h5 : q = loop5 <;> by_cases h3 : q = loop3 <;>
      simp_all [TapeMultiply.tapes, TapeCopy.onPair, storeTapes, counterTape,
        V, U, Function.update, hW.degree, hC.countScratch, hC.mulScratch,
        loop4, ringDegree, loop5, loop3, loop2, accumBits]
  rw [hi, ho] at hm
  have hall := join_runs cursorProgram (TapeMultiply.program loop4 ringDegree loop5 loop3)
    (fun _ => TapeMultiply.start) hp rfl hm
  have hfinal : Function.update V loop3 (List.replicate (t * r) true) =
      TapeHornerLoop.frame σ t (t * r) (List.replicate r false) := by
    funext q
    by_cases h2 : q = loop2 <;> by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
      simp_all [V, U, TapeHornerLoop.frame, Function.update, loop2, loop3, accumBits]
  have htime : ((10 * r + 8 + 1 + (2 * t + 4)) + 1 + (2 * t + 4)) +
      1 + (t * (10 * r + 14) + 3) = cost r t := by
    unfold cost
    ring
  simpa only [program, start, done, hfinal, htime] using hall

end TapeHornerPrepare
end DepthThreeLowerBound

end Complexity

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHornerPrepare

/-!
# Unrestricted depth-three lower bound: tape horner

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHorner.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHorner

open TapeMultiProgram TapeRouting TapeRegister TapeHornerMultiply

/-- Control states of the horner routine. -/
abbrev State := TapeHornerPrepare.State ⊕ TapeHornerLoop.State

/-- Transition function of the horner routine. -/
def program : TapeMultiProgram State :=
  joinCode TapeHornerPrepare.program TapeHornerLoop.program (fun _ => TapeHornerLoop.start)

/-- Initial control state of the horner routine. -/
def start : State := .inl TapeHornerPrepare.start
/-- Terminal control state of the horner routine. -/
def done : State := .inr TapeHornerLoop.done

/-- Transition budget for the horner routine. -/
def cost (r t : ℕ) : ℕ :=
  TapeHornerPrepare.cost r t + t * (TapeHornerBody.cost r (t * r) + 6) + 4

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem cost_le (r t : ℕ) : cost r t ≤ 1000 * (r + t + 1) ^ 4 := by
  unfold cost TapeHornerPrepare.cost TapeHornerBody.cost TapeHornerMultiply.cost
    TapeConvolve.cost TapeRemainder.cost TapeRemainderOuter.iterationCost
  ring_nf
  omega

theorem runs_horner (σ : TapeStore) (p h : List Bool) (blocks : List (List Bool)) (r : ℕ)
    (hW : Workspace σ r) (hC : TapeHornerPrepare.Clean σ)
    (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hB : σ coeffBits = blocks.flatten)
    (hT : σ coeffCount = List.replicate blocks.length true)
    (hp : p.length = r) (hh : h.length = r)
    (hblocks : ∀ b ∈ blocks, b.length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ accumBits (hornerBitLists r p h blocks))))
      (cost r blocks.length) := by
  have hlen := block_flatten_length r blocks hblocks
  have hpref := TapeHornerPrepare.runs_prepare σ r blocks.length hW hC hT
  have hl := TapeHornerLoop.runs_loop σ p h blocks [] (List.replicate r false)
    r (blocks.length * r) hW hP hH hp hh (by simp) hblocks
    (by simpa only [List.append_nil] using hB) (by omega) hC.countScratch hC.coefficient
  rw [hlen, hornerFrom_zero_eq_hornerBitLists r p h blocks hblocks] at hl
  have hfinal : TapeHornerLoop.frame σ 0 0 (hornerBitLists r p h blocks) =
      Function.update σ accumBits (hornerBitLists r p h blocks) := by
    funext q
    by_cases h2 : q = loop2 <;> by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
      simp_all [TapeHornerLoop.frame, Function.update, hC.count, hC.cursor,
        loop2, loop3, accumBits]
  rw [hfinal] at hl
  have hall := join_runs TapeHornerPrepare.program TapeHornerLoop.program
    (fun _ => TapeHornerLoop.start) hpref rfl hl
  have ht : TapeHornerPrepare.cost r blocks.length + 1 +
      (blocks.length * (TapeHornerBody.cost r (blocks.length * r) + 6) + 3) =
      cost r blocks.length := by unfold cost; omega
  simpa only [program, start, done, ht] using hall

end TapeHorner
end DepthThreeLowerBound

end Complexity

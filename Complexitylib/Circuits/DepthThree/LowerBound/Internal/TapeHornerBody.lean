/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHornerExtract
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHornerMultiply
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeXor
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitHornerLoop

/-!
# Unrestricted depth-three lower bound: tape horner body

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHornerBody.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHornerBody

open TapeMultiProgram TapeRouting TapeRegister TapeHornerMultiply

/-- Control states for the product stage of the horner body routine. -/
abbrev ProductState := TapeHornerExtract.State ⊕ TapeHornerMultiply.State
/-- Control states for the work stage of the horner body routine. -/
abbrev WorkState := ProductState ⊕ TapeXor.State
/-- Control states of the horner body routine. -/
abbrev State := WorkState ⊕ TapeErase.State

/-- Extract the next coefficient block and multiply the Horner accumulator. -/
def product : TapeMultiProgram ProductState :=
  joinCode TapeHornerExtract.program TapeHornerMultiply.program
    (fun _ => TapeHornerMultiply.start)

/-- Compose the main computational stages of the routine. -/
def work : TapeMultiProgram WorkState :=
  joinCode product (TapeXor.program scratchB accumBits) (fun _ => TapeXor.start)

/-- Transition function of the horner body routine. -/
def program : TapeMultiProgram State :=
  joinCode work (TapeErase.code scratchB) (fun _ => TapeErase.State.start)

/-- Initial control state of the horner body routine. -/
def start : State := .inl (.inl (.inl TapeHornerExtract.start))
/-- Terminal control state of the horner body routine. -/
def done : State := .inr TapeErase.State.done

/-- Transition budget for the horner body routine. -/
def cost (r offset : ℕ) : ℕ :=
  r * (2 * offset + r + 19) + TapeHornerMultiply.cost r + 4 * r + 20

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_body (σ : TapeStore) (p h a «prefix» b suffix : List Bool) (r : ℕ)
    (hW : Workspace σ r) (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hA : σ accumBits = a) (hp : p.length = r) (hh : h.length = r)
    (ha : a.length = r) (hb : b.length = r)
    (hsource : σ coeffBits = «prefix» ++ b ++ suffix)
    (hcursor : σ loop3 = List.replicate («prefix».length + r) true)
    (hcount : σ loop4 = []) (hbuffer : σ scratchB = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update
        (Function.update σ loop3 (List.replicate «prefix».length true))
        accumBits (hornerStep r p h b a)))) (cost r «prefix».length) := by
  let U := Function.update (Function.update σ loop3 (List.replicate «prefix».length true))
    scratchB b
  let V := Function.update U accumBits (multiplyBitLists r p h a)
  let W := Function.update V accumBits (hornerStep r p h b a)
  have he := TapeHornerExtract.runs_extract σ «prefix» b suffix r hsource hcursor
    hW.degree hb hcount hbuffer
  have hU : Workspace U r := by
    rcases hW with ⟨hd, h0, h1, hi, hj, hk, hs, ho⟩
    constructor <;>
      simp_all [U, Function.update, loop3, scratchB, ringDegree, loop0, loop1,
        indexA, indexB, indexC, scratchA, productBits]
  have hm := TapeHornerMultiply.runs_multiply U p h a r hU
    (by simp [U, hP, polyBits, loop3, scratchB])
    (by simp [U, hH, hashBits, loop3, scratchB])
    (by simp [U, hA, accumBits, loop3, scratchB]) hp hh ha
  have hprod := join_runs TapeHornerExtract.program TapeHornerMultiply.program
    (fun _ => TapeHornerMultiply.start) he rfl hm
  have hx := TapeXor.runs_store (src := scratchB) (dst := accumBits) (by decide)
    V b (multiplyBitLists r p h a)
    (by simp [V, U, scratchB, accumBits]) (by simp [V])
    (by simp [hb])
  have hx' : RunsIn (TapeXor.program scratchB accumBits).step
      (cfg TapeXor.start (storeTapes V)) (cfg TapeXor.done (storeTapes W))
      (2 * r + 4) := by
    simpa only [W, hornerStep, hb] using hx
  have hw := join_runs product (TapeXor.program scratchB accumBits)
    (fun _ => TapeXor.start) hprod rfl hx'
  have hclear := TapeStoreRuns.erase scratchB W
  have hclear' : RunsIn (TapeErase.code scratchB).step
      (cfg TapeErase.State.start (storeTapes W))
      (cfg TapeErase.State.done (storeTapes (Function.update W scratchB [])))
      (2 * r + 5) := by
    simpa [W, V, U, hb, scratchB, accumBits] using hclear
  have hall := join_runs work (TapeErase.code scratchB)
    (fun _ => TapeErase.State.start) hw rfl hclear'
  have hfinal : Function.update W scratchB [] =
      Function.update (Function.update σ loop3 (List.replicate «prefix».length true))
        accumBits (hornerStep r p h b a) := by
    funext q
    by_cases hb' : q = scratchB <;> by_cases ha' : q = accumBits <;>
      by_cases hl : q = loop3 <;>
      simp_all [W, V, U, Function.update, scratchB, accumBits, loop3]
  have htime : ((r * (2 * «prefix».length + r + 19) + 8 + 1 +
      TapeHornerMultiply.cost r) + 1 + (2 * r + 4)) + 1 + (2 * r + 5) =
      cost r «prefix».length := by unfold cost; omega
  simpa only [program, start, done, hfinal, htime] using hall

end TapeHornerBody
end DepthThreeLowerBound

end Complexity

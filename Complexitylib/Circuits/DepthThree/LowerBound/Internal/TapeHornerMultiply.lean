/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeConvolve
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeRemainder
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeHornerTake
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitReductionLoop

/-!
# Unrestricted depth-three lower bound: tape horner multiply

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeHornerMultiply.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeHornerMultiply

open TapeMultiProgram TapeRouting TapeRegister

/-- Register allocation for the horner multiply routine. -/
structure Workspace (σ : TapeStore) (r : ℕ) : Prop where
  degree : σ ringDegree = List.replicate r true
  loop0_empty : σ loop0 = []
  loop1_empty : σ loop1 = []
  indexA_empty : σ indexA = []
  indexB_empty : σ indexB = []
  indexC_empty : σ indexC = []
  scratch_empty : σ scratchA = []
  product_empty : σ productBits = []

/-- Control states for the work stage of the horner multiply routine. -/
abbrev WorkState := TapeConvolve.State ⊕ TapeRemainder.State
/-- Control states of the horner multiply routine. -/
abbrev State := WorkState ⊕ TapeHornerTake.State

/-- Compose the main computational stages of the routine. -/
def work : TapeMultiProgram WorkState :=
  joinCode TapeConvolve.program TapeRemainder.program (fun _ => TapeRemainder.start)

/-- Transition function of the horner multiply routine. -/
def program : TapeMultiProgram State :=
  joinCode work TapeHornerTake.program (fun _ => TapeHornerTake.start)

/-- Initial control state of the horner multiply routine. -/
def start : State := .inl (.inl TapeConvolve.start)
/-- Terminal control state of the horner multiply routine. -/
def done : State := .inr TapeHornerTake.done

/-- Transition budget for the horner multiply routine. -/
def cost (r : ℕ) : ℕ :=
  TapeConvolve.cost r + TapeRemainder.cost r + r * (r + 27) + 8 * r + 31

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_multiply (σ : TapeStore) (p h a : List Bool) (r : ℕ)
    (hW : Workspace σ r) (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hA : σ accumBits = a) (hp : p.length = r) (hh : h.length = r)
    (ha : a.length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ accumBits (multiplyBitLists r p h a))))
      (cost r) := by
  let c := convolveBitLists h a
  let U := Function.update σ productBits c
  let v := reduceByUpdates p r c
  let V := Function.update σ productBits v
  have hc := TapeConvolve.runs_convolve σ h a r hH hA hh ha hW.degree
    hW.loop0_empty hW.loop1_empty hW.indexA_empty hW.indexB_empty
    hW.indexC_empty hW.scratch_empty hW.product_empty
  have hc' : RunsIn TapeConvolve.program.step (cfg TapeConvolve.start (storeTapes σ))
      (cfg TapeConvolve.done (storeTapes U)) (TapeConvolve.cost r) := hc
  have hr := TapeRemainder.runs_remainder U p c
    (by simp [U, hP, polyBits, productBits]) (by simp [U])
    (by simp [U, hp, hW.degree, ringDegree, productBits])
    (by simp [c, hp, hh, ha, Nat.two_mul])
    (by simp [U, hW.loop0_empty, loop0, productBits])
    (by simp [U, hW.loop1_empty, loop1, productBits])
    (by simp [U, hW.indexA_empty, indexA, productBits])
    (by simp [U, hW.indexB_empty, indexB, productBits])
    (by simp [U, hW.indexC_empty, indexC, productBits])
    (by simp [U, hW.scratch_empty, scratchA, productBits])
  have hr' : RunsIn TapeRemainder.program.step (cfg TapeRemainder.start (storeTapes U))
      (cfg TapeRemainder.done (storeTapes V)) (TapeRemainder.cost r) := by
    simpa only [U, V, v, hp, Function.update_idem] using hr
  have hw := join_runs TapeConvolve.program TapeRemainder.program
    (fun _ => TapeRemainder.start) hc' rfl hr'
  have hvlen : v.length = 2 * r := by
    simp [v, c, reduceByUpdates_length, hh, ha, Nat.two_mul]
  have ht := TapeHornerTake.runs_take V a v r
    (by simp [V, hA, accumBits, productBits]) (by simp [V]) ha hvlen
    (by simp [V, hW.degree, ringDegree, productBits])
    (by simp [V, hW.loop1_empty, loop1, productBits])
    (by simp [V, hW.indexA_empty, indexA, productBits])
    (by simp [V, hW.scratch_empty, scratchA, productBits])
  have hv : v.take r = multiplyBitLists r p h a :=
    reduceByUpdates_convolve_eq_multiplyBitLists r p h a hp hh ha
  have hfinal : Function.update (Function.update V accumBits (v.take r)) productBits [] =
      Function.update σ accumBits (multiplyBitLists r p h a) := by
    funext q
    by_cases hprod : q = productBits <;> by_cases hacc : q = accumBits <;>
      simp_all [V, Function.update, hW.product_empty, accumBits, productBits]
  rw [hfinal] at ht
  have hall := join_runs work TapeHornerTake.program (fun _ => TapeHornerTake.start) hw rfl ht
  have htime : (TapeConvolve.cost r + 1 + TapeRemainder.cost r) + 1 +
      (r * (r + 27) + 8 * r + 29) = cost r := by unfold cost; omega
  simpa only [program, start, done, htime] using hall

end TapeHornerMultiply
end DepthThreeLowerBound

end Complexity

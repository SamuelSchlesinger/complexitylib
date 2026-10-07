/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeRemainderOuter

/-!
# Unrestricted depth-three lower bound: tape remainder

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeRemainder.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeRemainder

open TapeMultiProgram TapeRouting TapeRegister

/-- Control states of the remainder routine. -/
abbrev State := TapeCopy.State ⊕ TapeRemainderOuter.State

/-- Transition function of the remainder routine. -/
def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code ringDegree loop0) TapeRemainderOuter.program
    (fun _ => TapeRemainderOuter.start)

/-- Initial control state of the remainder routine. -/
def start : State := .inl TapeCopy.State.start
/-- Terminal control state of the remainder routine. -/
def done : State := .inr TapeRemainderOuter.done

/-- Transition budget for the remainder routine. -/
def cost (r : ℕ) : ℕ := r * TapeRemainderOuter.iterationCost r + 2*r + 8

theorem cost_le (r : ℕ) : cost r ≤ 100 * (r+1)^3 := by
  unfold cost TapeRemainderOuter.iterationCost
  nlinarith [Nat.zero_le (r*r), Nat.zero_le (r*r*r)]

theorem input_frame (σ : TapeStore) (c : List Bool) (r : ℕ)
    (hOut : σ productBits = c) :
    Function.update σ loop0 (List.replicate r true) = TapeRemainderOuter.frame σ r c := by
  funext q
  by_cases hl : q = loop0
  · subst q
    simp
  · by_cases hp : q = productBits
    · subst q
      simp [hOut, loop0, productBits]
    · simp [TapeRemainderOuter.frame, Function.update, hl, hp]

theorem output_frame (σ : TapeStore) (out : List Bool) (hLoop0 : σ loop0 = []) :
    TapeRemainderOuter.frame σ 0 out = Function.update σ productBits out := by
  funext q
  by_cases hl : q = loop0
  · subst q
    simp [hLoop0, loop0, productBits]
  · by_cases hp : q = productBits
    · subst q
      simp
    · simp [TapeRemainderOuter.frame, Function.update, hl, hp]

theorem runs_remainder (σ : TapeStore) (p c : List Bool)
    (hP : σ polyBits = p) (hOut : σ productBits = c)
    (hDegree : σ ringDegree = List.replicate p.length true)
    (hWidth : c.length = 2*p.length)
    (hLoop0 : σ loop0 = []) (hLoop1 : σ loop1 = [])
    (hA : σ indexA = []) (hB : σ indexB = []) (hC : σ indexC = [])
    (hScratch : σ scratchA = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes
        (Function.update σ productBits (reduceByUpdates p p.length c)))) (cost p.length) := by
  have hcopy := TapeStoreRuns.copy (by decide : ringDegree ≠ loop0) σ hLoop0
  have hcopy' : RunsIn (TapeCopy.code ringDegree loop0).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes (TapeRemainderOuter.frame σ p.length c)))
      (2*p.length+4) := by
    simpa only [hDegree, List.length_replicate, input_frame σ c p.length hOut] using hcopy
  have hloop := TapeRemainderOuter.runs_loop σ p c p.length hP hDegree
    ⟨hLoop1, hA, hB, hC, hScratch⟩ le_rfl (by omega)
  rw [output_frame σ _ hLoop0] at hloop
  have hall := join_runs (TapeCopy.code ringDegree loop0) TapeRemainderOuter.program
    (fun _ => TapeRemainderOuter.start) hcopy' rfl hloop
  have htime : (2*p.length+4)+1+(p.length*TapeRemainderOuter.iterationCost p.length+3) =
      cost p.length := by unfold cost; omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeRemainder
end DepthThreeLowerBound

end Complexity

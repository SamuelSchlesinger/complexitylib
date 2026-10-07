/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapePowerCompare

/-!
# Unrestricted depth-three lower bound: tape search body

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeSearchBody.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeSearchBody

open TapeMultiProgram TapeRouting TapeUnary

/-- The search increment: one or two according to the supplied flag. -/
def amount (two : Bool) : ℕ := if two then 2 else 1
/-- Transition budget for the search body routine at its increment stage. -/
def incrementCost (two : Bool) : ℕ := if two then 5 else 3

/-- Control states for the increment stage of the search body routine. -/
abbrev IncrementState := IncState ⊕ IncState

/-- Transition function for the tail stage of the search body routine. -/
def tailProgram (two : Bool) (candidate : TapeRegister) : TapeMultiProgram IncState :=
  if two then incProgram candidate else fun _ _ => none

/-- Transition function for the increment stage of the search body routine. -/
def incrementProgram (two : Bool) (candidate : TapeRegister) :
    TapeMultiProgram IncrementState :=
  joinCode (incProgram candidate) (tailProgram two candidate) (fun _ => IncState.start)

/-- Initial control state of the increment stage of the search body routine. -/
def incrementStart : IncrementState := .inl .start
/-- Terminal control state of the increment stage of the search body routine. -/
def incrementDone (two : Bool) : IncrementState :=
  .inr (if two then IncState.done else IncState.start)

private theorem increment_store (r : TapeRegister) (σ : TapeStore) (c : ℕ)
    (hc : σ r = List.replicate c true) :
    RunsIn (incProgram r).step (cfg IncState.start (storeTapes σ))
      (cfg IncState.done
        (storeTapes (Function.update σ r (List.replicate (c + 1) true)))) 2 := by
  have h := increment r (storeTapes σ) c (by simp [storeTapes, counterTape, hc])
  simpa only [storeTapes_update, counterTape] using h

theorem runs_increment (two : Bool) (r : TapeRegister) (σ : TapeStore) (c : ℕ)
    (hc : σ r = List.replicate c true) :
    RunsIn (incrementProgram two r).step (cfg incrementStart (storeTapes σ))
      (cfg (incrementDone two)
        (storeTapes (Function.update σ r (List.replicate (c + amount two) true))))
      (incrementCost two) := by
  have hfirst := increment_store r σ c hc
  cases two with
  | false =>
      have hrest := RunsIn.refl (tailProgram false r).step
        (cfg IncState.start (storeTapes (Function.update σ r (List.replicate (c + 1) true))))
      have h := join_runs (incProgram r) (tailProgram false r)
        (fun _ => IncState.start) hfirst rfl hrest
      exact h
  | true =>
      have hsecond := increment_store r (Function.update σ r (List.replicate (c + 1) true))
        (c + 1) (by simp)
      simp only [Function.update_idem] at hsecond
      have h := join_runs (incProgram r) (tailProgram true r)
        (fun _ => IncState.start) hfirst rfl hsecond
      have ha : c + 1 + 1 = c + 2 := by omega
      simpa only [IncrementState, incrementProgram, incrementStart, incrementDone,
        amount, incrementCost, ite_true, ha] using h

@[simp] theorem increment_done (two : Bool) (r : TapeRegister) (h : TapeHeads) :
    incrementProgram two r (incrementDone two) h = none := by
  cases two <;> rfl

/-- Control states of the search body routine. -/
abbrev State := TapeErase.State ⊕ IncrementState

/-- Transition function of the search body routine. -/
def program (k : ℕ) (two : Bool) (outer destination candidate : TapeRegister) :
    TapeMultiProgram State :=
  joinCode (TapeErase.code (TapePower.resultRegister k outer destination))
    (incrementProgram two candidate) (fun _ => incrementStart)

/-- Initial control state of the search body routine. -/
def start : State := .inl .start
/-- Terminal control state of the search body routine. -/
def done (two : Bool) : State := .inr (incrementDone two)

/-- Transition budget for the search body routine. -/
def cost (k : ℕ) (two : Bool) (c : ℕ) : ℕ :=
  2 * c ^ k + 5 + 1 + incrementCost two

theorem runs_body (k : ℕ) (two : Bool) (outer destination candidate : TapeRegister)
    (σ : TapeStore) (c : ℕ) (ho : σ outer = []) (hd : σ destination = [])
    (hc : σ candidate = List.replicate c true) :
    RunsIn (program k two outer destination candidate).step
      (cfg start (storeTapes (TapePowerCompare.outputStore k outer destination σ c)))
      (cfg (done two)
        (storeTapes (Function.update σ candidate (List.replicate (c + amount two) true))))
      (cost k two c) := by
  have he := TapeStoreRuns.erase (TapePower.resultRegister k outer destination)
    (TapePowerCompare.outputStore k outer destination σ c)
  simp only [TapePowerCompare.outputStore_result, List.length_replicate,
    TapePowerCompare.outputStore_clear k outer destination σ c ho hd] at he
  have hi := runs_increment two candidate σ c hc
  have h := join_runs (TapeErase.code (TapePower.resultRegister k outer destination))
    (incrementProgram two candidate) (fun _ => incrementStart) he rfl hi
  exact h

@[simp] theorem program_done (k : ℕ) (two : Bool)
    (outer destination candidate : TapeRegister) (h : TapeHeads) :
    program k two outer destination candidate (done two) h = none := by
  exact join_done _ _ _ (incrementDone two) h (increment_done two candidate h)

end TapeSearchBody
end DepthThreeLowerBound

end Complexity

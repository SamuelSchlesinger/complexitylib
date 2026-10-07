/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeInitialization
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeParametersBound
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeInputGuard

/-!
# Unrestricted depth-three lower bound: tape parse

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeParse.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeParse

open TapeMultiProgram TapeRouting

/-- The input bits and their unary length, with every other register empty. -/
def inputStore (w : List Bool) : TapeStore := fun r =>
  if r = TapeRegister.input then w
  else if r = TapeRegister.length then List.replicate w.length true else []

theorem initializedTapes_eq_store (w : List Bool) :
    initializedTapes w = storeTapes (inputStore w) := by
  funext r
  unfold initializedTapes storeTapes inputStore
  split_ifs <;> rfl

/-- Tape-store contents at the output stage of the parse routine. -/
def outputStore (w : List Bool) : TapeStore :=
  TapeInputGuard.outputStore (TapeParameters.outputStore (inputStore w) w.length)
    (dataDimension w.length) (hashDimension (dataDimension w.length))
    (independenceOrder (dataDimension w.length))

@[simp] theorem outputStore_input (w : List Bool) : outputStore w 0 = w := by
  simp [outputStore, TapeInputGuard.outputStore, TapeParameters.outputStore,
    TapeParameters.dataStore, inputStore, TapeRegister.input]

@[simp] theorem outputStore_data (w : List Bool) :
    outputStore w 2 = List.replicate (dataDimension w.length) true := by
  simp [outputStore, TapeInputGuard.outputStore]

@[simp] theorem outputStore_hash (w : List Bool) :
    outputStore w 3 = List.replicate (hashDimension (dataDimension w.length)) true := by
  simp [outputStore, TapeInputGuard.outputStore]

@[simp] theorem outputStore_order (w : List Bool) :
    outputStore w 4 = List.replicate (independenceOrder (dataDimension w.length)) true := by
  simp [outputStore, TapeInputGuard.outputStore]

theorem outputStore_empty (w : List Bool) (r : TapeRegister)
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3)
    (h4 : r ≠ 4) (h8 : r ≠ 8) : outputStore w r = [] := by
  simp [outputStore, TapeInputGuard.outputStore, TapeParameters.outputStore,
    TapeParameters.dataStore, inputStore, TapeRegister.input, TapeRegister.length,
    Function.update, h0, h1, h2, h3, h4, h8]

/-- Control states for the work stage of the parse routine. -/
abbrev WorkState := TapeParameters.State ⊕ TapeInputGuard.State

/-- Transition function for the work stage of the parse routine. -/
def workProgram : TapeMultiProgram WorkState :=
  joinCode TapeParameters.program TapeInputGuard.program (fun _ => TapeInputGuard.start)

/-- Initial control state of the work stage of the parse routine. -/
def workStart : WorkState := .inl TapeParameters.start
/-- Terminal control state of the work stage of the parse routine. -/
def workDone (accepted : Bool) : WorkState := .inr (TapeInputGuard.done accepted)

/-- Control states of the parse routine. -/
abbrev State := InitState ⊕ WorkState

/-- Transition function of the parse routine. -/
def program : TapeMultiProgram State :=
  joinCode initializationCode workProgram (fun _ => workStart)

/-- Initial control state of the parse routine. -/
def start : State := .inl InitState.start
/-- Terminal control state of the parse routine. -/
def done (accepted : Bool) : State := .inr (workDone accepted)

/-- Read the Boolean verdict from the terminal control state of the parse routine. -/
def acceptFlag : State → Bool
  | .inr (.inr (.inr (.inr (.done b)))) => b
  | _ => false

@[simp] theorem acceptFlag_done (b : Bool) : acceptFlag (done b) = b := rfl

@[simp] theorem program_done (b : Bool) (h : TapeHeads) : program (done b) h = none := rfl

theorem runs_parse (w : List Bool) :
    RunsIn program.step (cfg start (rawInputTapes w))
      (cfg (done (decide (InputFits w))) (storeTapes (outputStore w)))
      (1000 * (w.length + 3) ^ 8) := by
  let σ := inputStore w
  let τ := TapeParameters.outputStore σ w.length
  have hi := initialization_runs w
  rw [initializedTapes_eq_store] at hi
  have hp := TapeParameters.runs_parameters σ w.length
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
  have hp' := hp.mono (TapeParameters.cost_le w.length)
  have hg := TapeInputGuard.runs_inputFits_quadratic w τ
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ]) (by simp [τ]) (by simp [τ])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
  have hw := join_runs TapeParameters.program TapeInputGuard.program
    (fun _ => TapeInputGuard.start) hp' (by simp) hg
  have hall := join_runs initializationCode workProgram (fun _ => workStart) hi rfl hw
  apply hall.mono
  have hquad : (w.length + 1) ^ 2 ≤ (w.length + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : w.length + 1 ≤ w.length + 3) 2)
      (Nat.pow_le_pow_right (by omega : 0 < w.length + 3) (by decide : 2 ≤ 8))
  have hn : w.length ≤ (w.length + 3) ^ 8 := by
    calc
      w.length ≤ w.length + 3 := by omega
      _ = (w.length + 3) ^ 1 := by simp
      _ ≤ (w.length + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 1 ≤ (w.length + 3) ^ 8 := Nat.pow_pos (by omega)
  omega

end TapeParse
end DepthThreeLowerBound

end Complexity

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeDecodeParsed
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeEvaluation
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeBranch

/-!
# Unrestricted depth-three lower bound: machine language

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/MachineLanguage.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace MachineLanguage

open TapeMultiProgram TapeRouting TapeRegister

theorem decoded_prepared (w : List Bool) :
    TapeEvaluation.Prepared (TapeDecodeParsed.outputStore w) w := by
  constructor
  · constructor
    · exact TapeDecodeParsed.outputStore_hash w
    all_goals apply TapeDecodeParsed.outputStore_empty <;> decide
  · constructor
    all_goals apply TapeDecodeParsed.outputStore_empty <;> decide
  · exact TapeDecodeParsed.outputStore_data w
  · exact TapeDecodeParsed.outputStore_order w
  · exact TapeDecodeParsed.outputStore_block w .data
  · exact TapeDecodeParsed.outputStore_block w .hash
  · exact TapeDecodeParsed.outputStore_block w .polynomial
  · exact TapeDecodeParsed.outputStore_block w .coefficients
  · apply TapeDecodeParsed.outputStore_empty <;> decide

/-- Control states for the body stage of the complete language decider. -/
abbrev BodyState := TapeDecodeBlocks.State ⊕ TapeEvaluation.State

/-- Transition function for the body stage of the complete language decider. -/
def bodyProgram : TapeMultiProgram BodyState :=
  joinCode TapeDecodeBlocks.program TapeEvaluation.program (fun _ => TapeEvaluation.start)

/-- Initial control state of the body stage of the complete language decider. -/
def bodyStart : BodyState := .inl TapeDecodeBlocks.start
/-- Terminal control state of the body stage of the complete language decider. -/
def bodyDone (answer : Bool) : BodyState := .inr (TapeEvaluation.done answer)

@[simp] theorem bodyProgram_done (answer : Bool) (h : TapeHeads) :
    bodyProgram (bodyDone answer) h = none := rfl

theorem runs_body (w : List Bool) (hfit : InputFits w) :
    RunsIn bodyProgram.step (cfg bodyStart (storeTapes (TapeParse.outputStore w)))
      (cfg (bodyDone (language w)) (storeTapes
        (TapeEvaluation.outputStore (TapeDecodeParsed.outputStore w) w)))
      (21000 * (w.length + 1) ^ 4) := by
  have hd := TapeDecodeParsed.runs_decode w hfit
  have he := TapeEvaluation.runs_evaluate w (TapeDecodeParsed.outputStore w)
    hfit (decoded_prepared w)
  have hall := join_runs TapeDecodeBlocks.program TapeEvaluation.program
    (fun _ => TapeEvaluation.start) hd (by simp) he
  apply hall.mono
  have h24 : (w.length + 1) ^ 2 ≤ (w.length + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hpos : 1 ≤ (w.length + 1) ^ 4 := Nat.pow_pos (Nat.succ_pos _)
  omega

/-- Control states of the complete language decider. -/
abbrev State := TapeBranch.State TapeParse.State BodyState

/-- Transition function of the complete language decider. -/
def program : TapeMultiProgram State :=
  TapeBranch.program TapeParse.program bodyProgram bodyStart TapeParse.acceptFlag

/-- Initial control state of the complete language decider. -/
def start : State := TapeBranch.test TapeParse.start

/-- Read the Boolean verdict from the terminal control state of the complete language decider. -/
def acceptFlag : State → Bool
  | .inr (.inl (.inr q)) => TapeEvaluation.acceptFlag q
  | _ => false

instance stateFintype : Fintype State := by
  letI : Fintype TapeParse.State := inferInstance
  letI : Fintype TapeDecodeBlocks.State := inferInstance
  letI : Fintype TapeHornerMultiply.WorkState := inferInstance
  letI : Fintype TapeHorner.State := inferInstance
  infer_instance

/-- The bundled finite multitape machine deciding the explicit language. -/
def machine : FiniteMultiTapeMachine := TapeMultiProgram.machine program start acceptFlag

@[simp] theorem machine_init (w : List Bool) :
    machine.init w = cfg start (rawInputTapes w) := rfl

theorem halts (w : List Bool) :
    MultiTapeHaltsIn machine w (language w) (24000 * (w.length + 3) ^ 8) := by
  apply (multiTapeHaltsIn_iff_runsIn machine w (language w) _).2
  have hp := TapeParse.runs_parse w
  have hpos : 1 ≤ (w.length + 3) ^ 8 := Nat.pow_pos (by omega)
  by_cases hfit : InputFits w
  · have hflag : decide (InputFits w) = true := by simp [hfit]
    rw [hflag] at hp
    have hb := runs_body w hfit
    have hall := TapeBranch.runs_accept TapeParse.program bodyProgram bodyStart
      TapeParse.acceptFlag hp (by simp) (by simp) hb
    refine ⟨cfg (TapeBranch.body (bodyDone (language w)))
      (storeTapes (TapeEvaluation.outputStore (TapeDecodeParsed.outputStore w) w)),
      hall.mono ?_, ?_, ?_⟩
    · have h48 : (w.length + 1) ^ 4 ≤ (w.length + 3) ^ 8 :=
        Nat.le_trans (Nat.pow_le_pow_left (by omega : w.length + 1 ≤ w.length + 3) 4)
          (Nat.pow_le_pow_right (by omega : 0 < w.length + 3) (by decide : 4 ≤ 8))
      omega
    · apply (multiTapeStep_eq_none_iff program _).2
      exact TapeBranch.body_halts _ _ _ _ _ _ (by simp)
    · change acceptFlag (TapeBranch.body (bodyDone (language w))) = language w
      simp [acceptFlag, TapeBranch.body, bodyDone]
  · have hflag : decide (InputFits w) = false := by simp [hfit]
    rw [hflag] at hp
    have hall := TapeBranch.runs_reject TapeParse.program bodyProgram bodyStart
      TapeParse.acceptFlag hp (by simp) (by simp)
    refine ⟨cfg TapeBranch.rejected (storeTapes (TapeParse.outputStore w)),
      hall.mono ?_, ?_, ?_⟩
    · omega
    · apply (multiTapeStep_eq_none_iff program _).2
      exact TapeBranch.rejected_halts _ _ _ _ _
    · change false = language w
      exact (language_of_not_fits hfit).symm

theorem cost_le_standard (n : ℕ) :
    24000 * (n + 3) ^ 8 ≤ (24000 * 3 ^ 8) * (n + 1) ^ 8 := by
  calc
    24000 * (n + 3) ^ 8 ≤ 24000 * (3 * (n + 1)) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8)
    _ = _ := by rw [mul_pow]; ring

theorem polynomial_time : MultiTapePolynomialTimeDecider language := by
  refine ⟨machine, 24000 * 3 ^ 8, 8, by decide, by decide, ?_⟩
  intro w
  exact (halts w).mono (cost_le_standard w.length)

end MachineLanguage

theorem language_polynomial_time : MultiTapePolynomialTimeDecider language :=
  MachineLanguage.polynomial_time

end DepthThreeLowerBound

end Complexity

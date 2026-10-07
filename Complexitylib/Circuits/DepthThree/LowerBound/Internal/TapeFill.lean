/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeArithmetic

/-!
# Unrestricted depth-three lower bound: tape fill

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeFill.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeFill

open Turing TapeMultiProgram TapeRouting TapeUnary TapeCopy TapeArithmetic

/-- Transition function for the push stage of the fill routine. -/
def pushProgram (r : TapeRegister) (b : Bool) : TapeMultiProgram IncState
  | .start, h => writeMove r (rawInputSymbol b) .left .newHome h
  | .newHome, h => writeMove r (cleanAtom .home) .stay .done h
  | .done, _ => none

theorem runs_push (r : TapeRegister) (b : Bool) (T : TapeTapes) (bits : List Bool)
    (hT : T r = wordTape bits) :
    RunsIn (pushProgram r b).step (cfg IncState.start T)
      (cfg IncState.done (Function.update T r (wordTape (b :: bits)))) 2 := by
  let middle := ((T r).write (rawInputSymbol b)).move Dir.left
  have h₁ := step_writeMove (pushProgram r b) IncState.start IncState.newHome
    T r (rawInputSymbol b) HeadMove.left rfl
  have h₂ := step_writeMove (pushProgram r b) IncState.newHome IncState.done
    (Function.update T r middle) r (cleanAtom .home) HeadMove.stay rfl
  have hm : middle.write (cleanAtom .home) = wordTape (b :: bits) := by
    dsimp [middle]
    rw [hT, prepend_home]
  have h₁' : (pushProgram r b).step (cfg IncState.start T) =
      some (cfg IncState.newHome (Function.update T r middle)) := h₁
  have h₂' : (pushProgram r b).step (cfg IncState.newHome (Function.update T r middle)) =
      some (cfg IncState.done (Function.update T r (wordTape (b :: bits)))) := by
    simpa only [Function.update_self, HeadMove.apply_stay, Function.update_idem, hm] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

/-- Control states for the fill stage of the fill routine. -/
abbrev FillState := LoopState DecState IncState

/-- Transition function for the fill stage of the fill routine. -/
def fillProgram (counter destination : TapeRegister) (b : Bool) : TapeMultiProgram FillState :=
  loopCode (decProgram counter) (pushProgram destination b)
    DecState.start IncState.start decPositive

/-- Initial control state of the fill stage of the fill routine. -/
def fillStart : FillState := loopTest DecState.start
/-- Terminal control state of the fill stage of the fill routine. -/
def fillDone : FillState := loopDone

theorem runs_fill {counter destination : TapeRegister} (hne : counter ≠ destination)
    (b : Bool) (T : TapeTapes) (n : ℕ) (bits : List Bool) :
    RunsIn (fillProgram counter destination b).step
      (cfg fillStart (onPair counter destination T (counterTape n) (wordTape bits)))
      (cfg fillDone (onPair counter destination T
        (counterTape 0) (wordTape (List.replicate n b ++ bits))))
      (8 * n + 3) := by
  induction n generalizing bits with
  | zero =>
      have hd := decrement_empty counter
        (onPair counter destination T (counterTape 0) (wordTape bits)) (by simp [counterTape])
      have he := loop_exit (decProgram counter) (pushProgram destination b)
        DecState.start IncState.start decPositive hd rfl rfl
      simpa only [fillProgram, fillStart, fillDone, List.replicate_zero, List.nil_append,
        Nat.mul_zero, Nat.zero_add] using he
  | succ n ih =>
      have hd := decrement_cons counter
        (onPair counter destination T (counterTape (n + 1)) (wordTape bits))
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      simp only [update_onPair_src] at hd
      have hp := runs_push destination b
        (onPair counter destination T (counterTape n) (wordTape bits)) bits (by simp [hne])
      simp only [update_onPair_dst hne] at hp
      have hit := loop_iter (decProgram counter) (pushProgram destination b)
        DecState.start IncState.start decPositive hd rfl rfl hp rfl
      have hrest := ih (b :: bits)
      have hall := hit.trans hrest
      have hword : List.replicate n b ++ b :: bits = List.replicate (n + 1) b ++ bits := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have htime : 4 + 1 + 2 + 1 + (8 * n + 3) = 8 * (n + 1) + 3 := by omega
      simpa only [fillProgram, fillStart, fillDone, hword, htime] using hall

@[simp] theorem fill_done (counter destination : TapeRegister) (b : Bool) (h : TapeHeads) :
    fillProgram counter destination b fillDone h = none := rfl

end TapeFill
end DepthThreeLowerBound

end Complexity

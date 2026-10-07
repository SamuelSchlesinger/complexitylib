/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiRoutines

/-!
# Unrestricted depth-three lower bound: tape unary

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeUnary.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

open Turing TapeMultiProgram

namespace TapeUnary

/-- Represent a natural number by a unary word of true bits. -/
def counterTape (n : ℕ) : Tape TapeSymbol := wordTape (List.replicate n true)

private theorem blank_singleton :
    ListBlank.mk [blankSymbol] = ListBlank.mk ([] : List TapeSymbol) := by
  exact Quotient.sound' (Or.inr (show BlankExtends [] [blankSymbol] from ⟨1, rfl⟩))

theorem prepend_home (bits : List Bool) (b : Bool) :
    (((wordTape bits).write (rawInputSymbol b)).move Dir.left).write
      (cleanAtom .home) = wordTape (b :: bits) := rfl

theorem remove_home (bits : List Bool) (b : Bool) :
    (((wordTape (b :: bits)).write blankSymbol).move Dir.right).write
      (cleanAtom .home) = wordTape bits := by
  change Tape.mk' (ListBlank.mk [blankSymbol])
      (ListBlank.mk (cleanAtom .home :: (encodeInput bits ++ [cleanAtom .endMark]))) = _
  rw [blank_singleton]
  rfl

/-- Control states for the inc stage of the unary routine. -/
inductive IncState where
  | start
  | newHome
  | done
  deriving DecidableEq

instance : Fintype IncState where
  elems := {.start, .newHome, .done}
  complete := by
    intro state
    cases state <;> simp

/-- Transition function for the inc stage of the unary routine. -/
def incProgram (r : TapeRegister) : TapeMultiProgram IncState
  | .start, h => writeMove r (rawInputSymbol true) .left .newHome h
  | .newHome, h => writeMove r (cleanAtom .home) .stay .done h
  | .done, _ => none

theorem increment_word (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (hT : T r = wordTape bits) :
    RunsIn (incProgram r).step (cfg IncState.start T)
      (cfg IncState.done (Function.update T r (wordTape (true :: bits)))) 2 := by
  let middle := ((T r).write (rawInputSymbol true)).move Dir.left
  have h₁ := step_writeMove (incProgram r) IncState.start IncState.newHome
    T r (rawInputSymbol true) HeadMove.left rfl
  have h₂ := step_writeMove (incProgram r) IncState.newHome IncState.done
    (Function.update T r middle) r (cleanAtom .home) HeadMove.stay rfl
  have hmiddle : middle.write (cleanAtom .home) = wordTape (true :: bits) := by
    dsimp [middle]
    rw [hT, prepend_home]
  have h₁' : (incProgram r).step (cfg IncState.start T) =
      some (cfg IncState.newHome (Function.update T r middle)) := h₁
  have h₂' : (incProgram r).step
      (cfg IncState.newHome (Function.update T r middle)) =
      some (cfg IncState.done (Function.update T r (wordTape (true :: bits)))) := by
    simpa only [Function.update_self, HeadMove.apply_stay, Function.update_idem,
      hmiddle] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

theorem increment (r : TapeRegister) (T : TapeTapes) (n : ℕ)
    (hT : T r = counterTape n) :
    RunsIn (incProgram r).step (cfg IncState.start T)
      (cfg IncState.done (Function.update T r (counterTape (n + 1)))) 2 := by
  simpa only [counterTape, List.replicate_succ] using increment_word r T
    (List.replicate n true) hT

/-- Control states for the dec stage of the unary routine. -/
inductive DecState where
  | start
  | inspect
  | eraseHome
  | newHome
  | done (wasPositive : Bool)
  deriving DecidableEq, Fintype

/-- Transition function for the dec stage of the unary routine. -/
def decProgram (r : TapeRegister) : TapeMultiProgram DecState
  | .start, h => move r .right .inspect h
  | .inspect, h =>
      if isAtom .endMark r h then move r .left (.done false) h
      else move r .left .eraseHome h
  | .eraseHome, h => writeMove r blankSymbol .right .newHome h
  | .newHome, h => writeMove r (cleanAtom .home) .stay (.done true) h
  | .done _, _ => none

theorem decrement_empty (r : TapeRegister) (T : TapeTapes)
    (hT : T r = wordTape []) :
    RunsIn (decProgram r).step (cfg DecState.start T) (cfg (DecState.done false) T) 2 := by
  let U := Function.update T r ((T r).move Dir.right)
  have h₁ := step_move (decProgram r) DecState.start DecState.inspect T r
    HeadMove.right rfl
  have hhead : isAtom .endMark r (heads U) = true := by
    simp [U, heads, isAtom, hT, wordTape_right]
  have h₂ := step_move (decProgram r) DecState.inspect (DecState.done false) U r
    HeadMove.left (by simp [decProgram, hhead])
  have h₁' : (decProgram r).step (cfg DecState.start T) =
      some (cfg DecState.inspect U) := h₁
  have h₂' : (decProgram r).step (cfg DecState.inspect U) =
      some (cfg (DecState.done false) T) := by
    simpa only [U, Function.update_self, HeadMove.apply_left,
      Tape.move_right_left, Function.update_idem, Function.update_eq_self] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

theorem decrement_cons (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (b : Bool) (hT : T r = wordTape (b :: bits)) :
    RunsIn (decProgram r).step (cfg DecState.start T)
      (cfg (DecState.done true) (Function.update T r (wordTape bits))) 4 := by
  let U := Function.update T r ((T r).move Dir.right)
  let middle := ((T r).write blankSymbol).move Dir.right
  have h₁ := step_move (decProgram r) DecState.start DecState.inspect T r
    HeadMove.right rfl
  have hhead : isAtom .endMark r (heads U) = false := by
    simp [U, heads, isAtom, hT, wordTape_right, rawInputSymbol, cleanAtom]
  have h₂ := step_move (decProgram r) DecState.inspect DecState.eraseHome U r
    HeadMove.left (by simp [decProgram, hhead])
  have h₃ := step_writeMove (decProgram r) DecState.eraseHome DecState.newHome
    T r blankSymbol HeadMove.right rfl
  have h₄ := step_writeMove (decProgram r) DecState.newHome (DecState.done true)
    (Function.update T r middle) r (cleanAtom .home) HeadMove.stay rfl
  have hmiddle : middle.write (cleanAtom .home) = wordTape bits := by
    dsimp [middle]
    rw [hT, remove_home]
  have h₁' : (decProgram r).step (cfg DecState.start T) =
      some (cfg DecState.inspect U) := h₁
  have h₂' : (decProgram r).step (cfg DecState.inspect U) =
      some (cfg DecState.eraseHome T) := by
    simpa only [U, Function.update_self, HeadMove.apply_left,
      Tape.move_right_left, Function.update_idem, Function.update_eq_self] using h₂
  have h₃' : (decProgram r).step (cfg DecState.eraseHome T) =
      some (cfg DecState.newHome (Function.update T r middle)) := h₃
  have h₄' : (decProgram r).step (cfg DecState.newHome (Function.update T r middle)) =
      some (cfg (DecState.done true) (Function.update T r (wordTape bits))) := by
    simpa only [Function.update_self, HeadMove.apply_stay, Function.update_idem,
      hmiddle] using h₄
  exact ((RunsIn.single h₁').trans (RunsIn.single h₂')).trans
    ((RunsIn.single h₃').trans (RunsIn.single h₄'))

theorem decrement (r : TapeRegister) (T : TapeTapes) (n : ℕ)
    (hT : T r = counterTape n) :
    RunsIn (decProgram r).step (cfg DecState.start T)
      (cfg (DecState.done (decide (0 < n)))
        (Function.update T r (counterTape (n - 1)))) 4 := by
  cases n with
  | zero =>
      have h := (decrement_empty r T hT).mono (by decide : 2 ≤ 4)
      simpa only [Nat.zero_sub, Nat.lt_irrefl, decide_false, ← hT,
        Function.update_eq_self] using h
  | succ n =>
      simpa only [counterTape, List.replicate_succ, Nat.succ_sub_one,
        Nat.succ_pos, decide_true] using
        decrement_cons r T (List.replicate n true) true hT

end TapeUnary
end DepthThreeLowerBound

end Complexity

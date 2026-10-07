/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeEncoding
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeWord
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MultiTapeMachine

/-!
# Unrestricted depth-three lower bound: tape multi program

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeMultiProgram.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7

namespace DepthThreeLowerBound

open Turing

/-- One scanned tape symbol for each register. -/
abbrev TapeHeads := TapeRegister → TapeSymbol
/-- One head movement for each register. -/
abbrev TapeMoves := TapeRegister → HeadMove
/-- The collection of tapes indexed by registers. -/
abbrev TapeTapes := TapeRegister → Tape TapeSymbol
/-- Multitape configurations for the register and symbol types used by the evaluator. -/
abbrev TapeMultiCfg (Q : Type uDepth1) := MultiTapeCfg TapeRegister TapeSymbol Q
/-- Transition programs over the evaluator's fixed register and symbol types. -/
abbrev TapeMultiProgram (Q : Type uDepth2) :=
  Q → TapeHeads → Option (Q × TapeHeads × TapeMoves)

/-- Encode a bit word on a tape with its head at the start of the word. -/
def wordTape (bits : List Bool) : Tape TapeSymbol :=
  Tape.mk₁ (cleanAtom .home :: (encodeInput bits ++ [cleanAtom .endMark]))

/-- Encode a bit word with a specified prefix already passed by the head. -/
def cursorTape (before after : List Bool) : Tape TapeSymbol :=
  Tape.mk₂ ((encodeInput before).reverse ++ [cleanAtom .home])
    (encodeInput after ++ [cleanAtom .endMark])

@[simp] theorem wordTape_head (bits : List Bool) :
    (wordTape bits).head = cleanAtom .home := rfl

@[simp] theorem cursorTape_head_cons (before after : List Bool) (b : Bool) :
    (cursorTape before (b :: after)).head = rawInputSymbol b := rfl

@[simp] theorem cursorTape_head_nil (before : List Bool) :
    (cursorTape before []).head = cleanAtom .endMark := rfl

@[simp] theorem wordTape_right (bits : List Bool) :
    (wordTape bits).move Dir.right = cursorTape [] bits := rfl

theorem cursorTape_right (before after : List Bool) (b : Bool) :
    (cursorTape before (b :: after)).move Dir.right =
      cursorTape (before ++ [b]) after := by
  simp only [cursorTape, encodeInput, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, TapeWord.move_right_mk₂_cons]

namespace TapeMultiProgram

/-- Execute one transition of the fixed-register multitape program. -/
def step {Q : Type uDepth3} (P : TapeMultiProgram Q) : TapeMultiCfg Q → Option (TapeMultiCfg Q) :=
  multiTapeStep P

/-- Bundle a control state with the collection of tapes. -/
def cfg {Q : Type uDepth4} (q : Q) (T : TapeTapes) : TapeMultiCfg Q := ⟨q, T⟩

/-- Read the scanned symbol of every tape. -/
def heads (T : TapeTapes) : TapeHeads := fun r => (T r).head

/-- Keep every tape head stationary. -/
def stayMoves : TapeMoves := fun _ => .stay

/-- Move the selected tape head and keep the remaining heads stationary. -/
def moveOnly (r : TapeRegister) (d : HeadMove) : TapeMoves :=
  Function.update stayMoves r d

/-- Change the selected scanned symbol and retain all other scanned symbols. -/
def writeOnly (r : TapeRegister) (symbol : TapeSymbol) (h : TapeHeads) : TapeHeads :=
  Function.update h r symbol

/-- Change only the control state, leaving all tape contents and heads fixed. -/
def jump {Q : Type uDepth5} (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) := some (q, h, stayMoves)

/-- Move a selected tape head while changing the control state. -/
def move {Q : Type uDepth6} (r : TapeRegister) (d : HeadMove) (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) := some (q, h, moveOnly r d)

/-- Write and move on a selected tape while changing the control state. -/
def writeMove {Q : Type uDepth7} (r : TapeRegister) (symbol : TapeSymbol)
    (d : HeadMove) (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) :=
  some (q, writeOnly r symbol h, moveOnly r d)

/-- Test whether the selected tape head scans the specified atom. -/
def isAtom (a : TapeAtom) (r : TapeRegister) (h : TapeHeads) : Bool :=
  decide ((h r).1 = a)

/-- Bundle a finite-state register program, initial state, and verdict function as a machine. -/
def machine {Q : Type} [Fintype Q] (P : TapeMultiProgram Q)
    (initial : Q) (accept : Q → Bool) : FiniteMultiTapeMachine where
  K := TapeRegister
  inputTape := TapeRegister.input
  Γ := TapeSymbol
  Q := Q
  initialState := initial
  inputSymbol := rawInputSymbol
  input_injective := rawInputSymbol_injective
  input_ne_blank := by simpa only [default_tapeSymbol] using rawInputSymbol_ne_blank
  code := P
  accept := accept

end TapeMultiProgram
end DepthThreeLowerBound

end Complexity

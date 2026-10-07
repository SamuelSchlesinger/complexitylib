/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiRoutines
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeWordRewind
public import Mathlib.Data.List.Induction

/-!
# Unrestricted depth-three lower bound: tape rewind

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeRewind.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

open Turing TapeMultiProgram

theorem cursorTape_left_nil (after : List Bool) :
    (cursorTape [] after).move Dir.left = wordTape after :=
  TapeWord.move_left_mk₂_cons [] (encodeInput after ++ [cleanAtom .endMark])
    (cleanAtom .home)

theorem cursorTape_left_append (before after : List Bool) (b : Bool) :
    (cursorTape (before ++ [b]) after).move Dir.left =
      cursorTape before (b :: after) := by
  simp only [cursorTape, encodeInput, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, TapeWord.move_left_mk₂_cons]

namespace TapeRewind

/-- Control states of the rewind routine. -/
inductive State
  | run
  | done
  deriving DecidableEq, Inhabited

instance : Fintype State where
  elems := {.run, .done}
  complete := by
    intro state
    cases state <;> simp

/-- Transition function of the rewind routine. -/
def program (r : TapeRegister) : TapeMultiProgram State
  | .run, h => if isAtom .home r h then jump .done h else move r .left .run h
  | .done, _ => none

theorem step_cursor (r : TapeRegister) (T : TapeTapes) (before after : List Bool) :
    (program r).step (cfg .run (Function.update T r (cursorTape before after))) =
      some (cfg .run (Function.update T r ((cursorTape before after).move Dir.left))) := by
  have h := step_move (program r) .run .run
    (Function.update T r (cursorTape before after)) r .left (by
      cases after <;> simp [program, isAtom, heads, rawInputSymbol, cleanAtom])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_left] using h

theorem step_home (r : TapeRegister) (T : TapeTapes) (bits : List Bool) :
    (program r).step (cfg .run (Function.update T r (wordTape bits))) =
      some (cfg .done (Function.update T r (wordTape bits))) := by
  apply step_jump
  simp [program, isAtom, heads]

theorem runs_cursor (r : TapeRegister) (T : TapeTapes) (before after : List Bool) :
    RunsIn (program r).step
      (cfg .run (Function.update T r (cursorTape before after)))
      (cfg .done (Function.update T r (wordTape (before ++ after))))
      (before.length + 2) := by
  induction before using List.reverseRecOn generalizing after with
  | nil =>
      have h₁ := RunsIn.single (step_cursor r T [] after)
      rw [cursorTape_left_nil] at h₁
      have h₂ := RunsIn.single (step_home r T after)
      simpa only [List.nil_append, List.length_nil, Nat.zero_add] using h₁.trans h₂
  | append_singleton before b ih =>
      have h₁ := RunsIn.single (step_cursor r T (before ++ [b]) after)
      rw [cursorTape_left_append] at h₁
      have h₂ := ih (b :: after)
      simpa only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h₁.trans h₂

end TapeRewind
end DepthThreeLowerBound

end Complexity

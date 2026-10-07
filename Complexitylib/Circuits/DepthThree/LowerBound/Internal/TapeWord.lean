/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Computability.TuringMachine.Tape

/-!
# Unrestricted depth-three lower bound: tape word

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeWord.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

namespace TapeWord

open Turing

variable {Γ : Type uDepth1} [Inhabited Γ]

@[simp] theorem head_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ L (a :: R)).head = a := rfl

@[simp] theorem move_right_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ L (a :: R)).move Dir.right = Tape.mk₂ (a :: L) R := rfl

@[simp] theorem write_mk₂_cons (L R : List Γ) (a b : Γ) :
    (Tape.mk₂ L (a :: R)).write b = Tape.mk₂ L (b :: R) := rfl

theorem move_right_iterate_mk₂_append («prefix» L R : List Γ) :
    (Tape.move Dir.right)^[«prefix».length] (Tape.mk₂ L («prefix» ++ R)) =
      Tape.mk₂ («prefix».reverse ++ L) R := by
  induction «prefix» generalizing L with
  | nil => rfl
  | cons a «prefix» ih =>
    rw [List.length_cons, List.cons_append, Function.iterate_succ_apply,
      move_right_mk₂_cons]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append] using ih (a :: L)

end TapeWord

end DepthThreeLowerBound

end Complexity

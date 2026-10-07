/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeRouting
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeUnary
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCopy
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: tape arithmetic

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeArithmetic.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

namespace DepthThreeLowerBound
namespace TapeArithmetic

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

theorem update_onPair_src {α : Type uDepth1} (src dst : TapeRegister)
    (T : TapeRegister → α) (s d s' : α) :
    Function.update (onPair src dst T s d) src s' = onPair src dst T s' d := by
  funext r
  by_cases h : r = src
  · subst r
    simp
  · simp [Function.update, onPair, h]

theorem update_onPair_dst {α : Type uDepth2} {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeRegister → α) (s d d' : α) :
    Function.update (onPair src dst T s d) dst d' = onPair src dst T s d' := by
  funext r
  by_cases hs : r = src
  · subst r
    simp [Function.update, onPair, hne]
  · by_cases hd : r = dst
    · subst r
      simp [Function.update, onPair, Ne.symm hne]
    · simp [Function.update, onPair, hs, hd]

/-- Read whether the decrement routine removed a positive unit. -/
def decPositive : DecState → Bool
  | .done b => b
  | _ => false

/-- Control states for the add stage of the arithmetic routine. -/
abbrev AddState := LoopState DecState IncState

/-- Transition function for the add stage of the arithmetic routine. -/
def addProgram (counter destination : TapeRegister) : TapeMultiProgram AddState :=
  loopCode (decProgram counter) (incProgram destination)
    DecState.start IncState.start decPositive

/-- Initial control state of the add stage of the arithmetic routine. -/
def addStart : AddState := loopTest DecState.start
/-- Terminal control state of the add stage of the arithmetic routine. -/
def addDone : AddState := loopDone

theorem runs_add {counter destination : TapeRegister} (hne : counter ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    RunsIn (addProgram counter destination).step
      (cfg addStart (onPair counter destination T (counterTape n) (counterTape m)))
      (cfg addDone (onPair counter destination T (counterTape 0) (counterTape (m + n))))
      (8 * n + 3) := by
  induction n generalizing m with
  | zero =>
      have hdec := decrement_empty counter
        (onPair counter destination T (counterTape 0) (counterTape m)) (by
          simp [counterTape])
      have he := loop_exit (decProgram counter) (incProgram destination)
        DecState.start IncState.start decPositive hdec rfl rfl
      simpa only [addProgram, addStart, addDone, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero] using he
  | succ n ih =>
      have hdec := decrement_cons counter
        (onPair counter destination T (counterTape (n + 1)) (counterTape m))
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      simp only [update_onPair_src] at hdec
      have hinc := increment destination
        (onPair counter destination T (counterTape n) (counterTape m)) m (by
          simp [hne])
      simp only [update_onPair_dst hne] at hinc
      have hit := loop_iter (decProgram counter) (incProgram destination)
        DecState.start IncState.start decPositive hdec rfl rfl hinc rfl
      have hrest := ih (m + 1)
      have hall := hit.trans hrest
      have hacc : m + 1 + n = m + (n + 1) := by omega
      have htime : 4 + 1 + 2 + 1 + (8 * n + 3) = 8 * (n + 1) + 3 := by omega
      simpa only [addProgram, addStart, addDone, hacc, htime] using hall

@[simp] theorem add_done (counter destination : TapeRegister) (h : TapeHeads) :
    addProgram counter destination addDone h = none := rfl

end TapeArithmetic
end DepthThreeLowerBound

end Complexity

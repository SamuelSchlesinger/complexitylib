/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeArithmetic
public import Mathlib.Data.Fintype.Sigma

/-!
# Unrestricted depth-three lower bound: tape divide five

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeDivideFive.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeDivideFive

open TapeMultiProgram TapeUnary TapeCopy TapeArithmetic

/-- Control states of the divide five routine. -/
inductive State where
  | dec (phase : Fin 5) (q : DecState)
  | inc (q : IncState)
  | done (remainder : Fin 5)
  deriving DecidableEq, Fintype

/-- Advance the remainder counter modulo five. -/
def nextPhase (phase : Fin 5) : Fin 5 :=
  ⟨(phase.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

/-- The remainder modulo five, viewed as an element of `Fin 5`. -/
def residue (n : ℕ) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by decide)⟩

/-- Transition function of the divide five routine. -/
def program (counter destination : TapeRegister) : TapeMultiProgram State
  | .dec phase q, h =>
      match decProgram counter q h with
      | some (q', writes, moves) => some (.dec phase q', writes, moves)
      | none =>
          match q with
          | .done false => jump (.done phase) h
          | .done true =>
              if phase.val = 4 then jump (.inc .start) h
              else jump (.dec (nextPhase phase) .start) h
          | _ => none
  | .inc q, h =>
      match incProgram destination q h with
      | some (q', writes, moves) => some (.inc q', writes, moves)
      | none => jump (.dec 0 .start) h
  | .done _, _ => none

private theorem dec_runs (counter destination : TapeRegister) (phase : Fin 5)
    {a b : DecState} {T U : TapeTapes} {n : ℕ}
    (h : RunsIn (decProgram counter).step (cfg a T) (cfg b U) n) :
    RunsIn (program counter destination).step
      (cfg (.dec phase a) T) (cfg (.dec phase b) U) n := by
  have he := runs_map (decProgram counter) (program counter destination)
    (State.dec phase) (by
      intro q heads q' writes moves hc
      simp only [program, hc]) h
  exact he

private theorem inc_runs (counter destination : TapeRegister)
    {a b : IncState} {T U : TapeTapes} {n : ℕ}
    (h : RunsIn (incProgram destination).step (cfg a T) (cfg b U) n) :
    RunsIn (program counter destination).step
      (cfg (.inc a) T) (cfg (.inc b) U) n := by
  have he := runs_map (incProgram destination) (program counter destination)
    State.inc (by
      intro q heads q' writes moves hc
      simp only [program, hc]) h
  exact he

theorem runs_phase {counter destination : TapeRegister} (hne : counter ≠ destination)
    (T : TapeTapes) (n m : ℕ) (phase : Fin 5) :
    RunsIn (program counter destination).step
      (cfg (.dec phase .start)
        (onPair counter destination T (counterTape n) (counterTape m)))
      (cfg (.done (residue (phase.val + n)))
        (onPair counter destination T (counterTape 0)
          (counterTape (m + (phase.val + n) / 5))))
      (8 * n + 3) := by
  induction n generalizing m phase with
  | zero =>
      have hd := decrement_empty counter
        (onPair counter destination T (counterTape 0) (counterTape m))
        (by simp [counterTape])
      have hrun := dec_runs counter destination phase hd
      have hj := step_jump (program counter destination)
        (.dec phase (.done false)) (.done phase)
        (onPair counter destination T (counterTape 0) (counterTape m)) rfl
      have hall := hrun.trans (RunsIn.single hj)
      have hr : residue phase.val = phase := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt phase.is_lt
      simpa only [Nat.add_zero, Nat.mul_zero, Nat.zero_add,
        Nat.div_eq_of_lt phase.is_lt, hr] using hall
  | succ n ih =>
      have hd := decrement_cons counter
        (onPair counter destination T (counterTape (n + 1)) (counterTape m))
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      simp only [update_onPair_src] at hd
      have hrun := dec_runs counter destination phase hd
      have hpBound := phase.is_lt
      by_cases hp : phase.val = 4
      · have hj := step_jump (program counter destination)
          (.dec phase (.done true)) (.inc .start)
          (onPair counter destination T (counterTape n) (counterTape m))
          (by simp [program, decProgram, hp])
        have hi := increment destination
          (onPair counter destination T (counterTape n) (counterTape m)) m
          (by simp [hne])
        simp only [update_onPair_dst hne] at hi
        have hinc := inc_runs counter destination hi
        have hk := step_jump (program counter destination) (.inc .done)
          (.dec 0 .start)
          (onPair counter destination T (counterTape n) (counterTape (m + 1))) rfl
        have hall := (((hrun.trans (RunsIn.single hj)).trans hinc).trans
          (RunsIn.single hk)).trans (ih (m + 1) 0)
        have hv : m + 1 + n / 5 = m + (phase.val + (n + 1)) / 5 := by omega
        have hr : residue (phase.val + (n + 1)) = residue n := by
          apply Fin.ext
          dsimp [residue]
          omega
        have ht : 4 + 1 + 2 + 1 + (8 * n + 3) = 8 * (n + 1) + 3 := by omega
        simpa only [Fin.val_zero, Nat.zero_add, hv, hr, ht] using hall
      · have hphase : phase.val + 1 < 5 := by omega
        have hnext : (nextPhase phase).val = phase.val + 1 :=
          Nat.mod_eq_of_lt hphase
        have hj := step_jump (program counter destination)
          (.dec phase (.done true)) (.dec (nextPhase phase) .start)
          (onPair counter destination T (counterTape n) (counterTape m))
          (by simp [program, decProgram, hp])
        have hall := (hrun.trans (RunsIn.single hj)).trans (ih m (nextPhase phase))
        have hv : (nextPhase phase).val + n = phase.val + (n + 1) := by omega
        have ht : 4 + 1 + (8 * n + 3) ≤ 8 * (n + 1) + 3 := by omega
        simpa only [hv] using hall.mono ht

theorem runs_divide {counter destination : TapeRegister} (hne : counter ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    RunsIn (program counter destination).step
      (cfg (.dec 0 .start)
        (onPair counter destination T (counterTape n) (counterTape m)))
      (cfg (.done (residue n))
        (onPair counter destination T (counterTape 0) (counterTape (m + n / 5))))
      (8 * n + 3) := by
  simpa only [Fin.val_zero, Nat.zero_add] using runs_phase hne T n m 0

@[simp] theorem done_halts (counter destination : TapeRegister) (r : Fin 5)
    (h : TapeHeads) : program counter destination (.done r) h = none := rfl

end TapeDivideFive
end DepthThreeLowerBound

end Complexity

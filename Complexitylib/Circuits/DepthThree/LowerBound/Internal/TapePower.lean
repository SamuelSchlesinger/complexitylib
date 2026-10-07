/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiply
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: tape power

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapePower.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapePower

open TapeMultiProgram TapeRouting TapeUnary TapeCopy
open scoped BigOperators

/-- Control states of the power routine. -/
def State : ℕ → Type
  | 0 => Unit
  | k + 1 => TapeMultiply.State ⊕ State k

instance (k : ℕ) : Fintype (State k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
      change Fintype (TapeMultiply.State ⊕ State k)
      letI := ih
      infer_instance

/-- Initial control state of the power routine. -/
def start : (k : ℕ) → State k
  | 0 => ()
  | _ + 1 => .inl TapeMultiply.start

/-- Terminal control state of the power routine. -/
def done : (k : ℕ) → State k
  | 0 => ()
  | k + 1 => .inr (done k)

/-- Transition function of the power routine. -/
def program : (k : ℕ) → (outer source scratch destination : TapeRegister) →
    TapeMultiProgram (State k)
  | 0, _, _, _, _ => fun _ _ => none
  | k + 1, outer, source, scratch, destination =>
      joinCode (TapeMultiply.program outer source scratch destination)
        (program k destination source scratch outer) (fun _ => start k)

/-- The counter-tape contents after the recursive power computation. -/
def resultTapes : ℕ → TapeRegister → TapeRegister → TapeRegister → TapeRegister →
    TapeTapes → ℕ → ℕ → TapeTapes
  | 0, outer, source, scratch, destination, T, n, m =>
      TapeMultiply.tapes outer source scratch destination T n m 0 0
  | k + 1, outer, source, scratch, destination, T, n, m =>
      resultTapes k destination source scratch outer T (n * m) m

/-- Select the register holding the result after alternating power stages. -/
def resultRegister : ℕ → TapeRegister → TapeRegister → TapeRegister
  | 0, outer, _ => outer
  | k + 1, outer, destination => resultRegister k destination outer

/-- Transition budget for the power routine. -/
def cost : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, n, m => n * (10 * m + 14) + 3 + 1 + cost k (n * m) m

private theorem swap_tapes {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    TapeMultiply.tapes outer source scratch destination T 0 m 0 n =
      TapeMultiply.tapes destination source scratch outer T n m 0 0 := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [TapeMultiply.tapes, onPair, hos, hoc, hod]
  · by_cases hs : r = source
    · subst r
      simp [TapeMultiply.tapes, onPair, Ne.symm hos, hsd]
    · by_cases hc : r = scratch
      · subst r
        simp [TapeMultiply.tapes, onPair, Ne.symm hoc, Ne.symm hsc, hcd]
      · by_cases hd : r = destination
        · subst r
          simp [TapeMultiply.tapes, onPair, Ne.symm hod, Ne.symm hsd, Ne.symm hcd]
        · simp [TapeMultiply.tapes, onPair, ho, hs, hc, hd]

theorem runs_power (k : ℕ) {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    RunsIn (program k outer source scratch destination).step
      (cfg (start k) (TapeMultiply.tapes outer source scratch destination T n m 0 0))
      (cfg (done k) (resultTapes k outer source scratch destination T n m))
      (cost k n m) := by
  induction k generalizing outer source scratch destination n with
  | zero => exact RunsIn.refl _ _
  | succ k ih =>
      have hm := TapeMultiply.runs_mul hos hoc hod hsc hsd hcd T n m 0
      simp only [Nat.zero_add, swap_tapes hos hoc hod hsc hsd hcd] at hm
      have hr := ih (Ne.symm hsd) (Ne.symm hcd) (Ne.symm hod)
        hsc (Ne.symm hos) (Ne.symm hoc) (n * m)
      have h := join_runs (TapeMultiply.program outer source scratch destination)
        (program k destination source scratch outer) (fun _ => start k)
        hm rfl hr
      exact h

theorem program_done (k : ℕ) (outer source scratch destination : TapeRegister)
    (h : TapeHeads) : program k outer source scratch destination (done k) h = none := by
  induction k generalizing outer source scratch destination with
  | zero => rfl
  | succ k ih =>
      exact join_done _ _ _ (done k) h (ih destination source scratch outer)

theorem resultTapes_result (k : ℕ)
    (outer source scratch destination : TapeRegister) (T : TapeTapes) (n m : ℕ) :
    resultTapes k outer source scratch destination T n m
      (resultRegister k outer destination) = counterTape (n * m ^ k) := by
  induction k generalizing outer destination n with
  | zero => simp [resultTapes, resultRegister]
  | succ k ih =>
      rw [resultTapes, resultRegister, ih]
      congr 1
      rw [pow_succ]
      ring

theorem resultTapes_source (k : ℕ) {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hsd : source ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    resultTapes k outer source scratch destination T n m source = counterTape m := by
  induction k generalizing outer destination n with
  | zero => exact TapeMultiply.tapes_source hos T n m 0 0
  | succ k ih => exact ih (Ne.symm hsd) (Ne.symm hos) (n * m)

theorem resultTapes_scratch (k : ℕ) {outer source scratch destination : TapeRegister}
    (hoc : outer ≠ scratch) (hsc : source ≠ scratch) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    resultTapes k outer source scratch destination T n m scratch = counterTape 0 := by
  induction k generalizing outer destination n with
  | zero => exact TapeMultiply.tapes_scratch hoc hsc T n m 0 0
  | succ k ih => exact ih (Ne.symm hcd) (Ne.symm hoc) (n * m)

theorem resultTapes_other (k : ℕ)
    (outer source scratch destination : TapeRegister) (T : TapeTapes) (n m : ℕ)
    (r : TapeRegister) (ho : r ≠ outer) (hs : r ≠ source)
    (hc : r ≠ scratch) (hd : r ≠ destination) :
    resultTapes k outer source scratch destination T n m r = T r := by
  induction k generalizing outer destination n with
  | zero => exact TapeMultiply.tapes_other _ _ _ _ _ _ _ _ _ _ ho hs hc hd
  | succ k ih => exact ih destination outer (n * m) hd ho

theorem cost_eq_sum (k n m : ℕ) :
    cost k n m = n * (10 * m + 14) * (∑ j ∈ Finset.range k, m ^ j) + 4 * k := by
  induction k generalizing n with
  | zero => simp [cost]
  | succ k ih =>
      rw [cost, ih, Finset.sum_range_succ']
      simp only [pow_zero, pow_succ]
      rw [← Finset.sum_mul]
      ring

end TapePower
end DepthThreeLowerBound

end Complexity

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeSearchBody
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageSearchTests

/-!
# Unrestricted depth-three lower bound: tape power search

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapePowerSearch.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapePowerSearch

open TapeMultiProgram TapeRouting TapeUnary

/-- Register allocation for the power search routine. -/
abbrev Registers := Fin 5 ↪ TapeRegister

/-- Tape-store contents at the candidate stage of the power search routine. -/
def candidateStore (R : Registers) (σ : TapeStore) (c : ℕ) : TapeStore :=
  Function.update σ (R 1) (List.replicate c true)

/-- Read the continuation predicate from a terminal power comparison. -/
def flag (k : ℕ) (again : Ordering → Bool) : TapePowerCompare.State k → Bool
  | .inr (.inr (.done o)) => again o
  | _ => false

/-- Control states of the power search routine. -/
abbrev State (k : ℕ) := LoopState (TapePowerCompare.State k) TapeSearchBody.State

/-- Transition function of the power search routine. -/
def program (k : ℕ) (two : Bool) (again : Ordering → Bool) (R : Registers) :
    TapeMultiProgram (State k) :=
  loopCode (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4))
    (TapeSearchBody.program k two (R 0) (R 3) (R 1))
    (TapePowerCompare.start k) TapeSearchBody.start (flag k again)

/-- Initial control state of the power search routine. -/
def start (k : ℕ) : State k := loopTest (TapePowerCompare.start k)
/-- Terminal control state of the power search routine. -/
def done (k : ℕ) : State k := loopDone

/-- Transition budget for the power search routine. -/
def cost (k : ℕ) (two : Bool) (D : ℕ) : ℕ → ℕ → ℕ
  | 0, c => TapePowerCompare.cost k c D + 1
  | fuel + 1, c => TapePowerCompare.cost k c D + 1 + TapeSearchBody.cost k two c + 1 +
      cost k two D fuel (c + TapeSearchBody.amount two)

private theorem runs_test (k : ℕ) (R : Registers) (σ : TapeStore) (c D : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate D true) :
    RunsIn (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4)).step
      (cfg (TapePowerCompare.start k) (storeTapes (candidateStore R σ c)))
      (cfg (TapePowerCompare.done k (TapeUnaryCompareScan.result (c ^ k) D))
        (storeTapes (TapePowerCompare.outputStore k (R 0) (R 3)
          (candidateStore R σ c) c))) (TapePowerCompare.cost k c D) := by
  apply TapePowerCompare.runs_compare k (outer := R 0) (source := R 1)
    (scratch := R 2) (destination := R 3) (target := R 4)
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (candidateStore R σ c) c D
  · simpa [candidateStore, R.injective.ne (by decide : (0 : Fin 5) ≠ 1)] using ho
  · simp [candidateStore]
  · simpa [candidateStore, R.injective.ne (by decide : (2 : Fin 5) ≠ 1)] using hs
  · simpa [candidateStore, R.injective.ne (by decide : (3 : Fin 5) ≠ 1)] using hd
  · simpa [candidateStore, R.injective.ne (by decide : (4 : Fin 5) ≠ 1)] using ht

theorem runs_search (k : ℕ) (two : Bool) (again : Ordering → Bool) (R : Registers)
    (σ : TapeStore) (D fuel c : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate D true)
    (hgo : ∀ j < fuel, again (TapeUnaryCompareScan.result
      ((c + TapeSearchBody.amount two * j) ^ k) D) = true)
    (hstop : again (TapeUnaryCompareScan.result
      ((c + TapeSearchBody.amount two * fuel) ^ k) D) = false) :
    RunsIn (program k two again R).step
      (cfg (start k) (storeTapes (candidateStore R σ c)))
      (cfg (done k) (storeTapes (TapePowerCompare.outputStore k (R 0) (R 3)
        (candidateStore R σ (c + TapeSearchBody.amount two * fuel))
        (c + TapeSearchBody.amount two * fuel))))
      (cost k two D fuel c) := by
  induction fuel generalizing c with
  | zero =>
      have htst := runs_test k R σ c D ho hs hd ht
      have he := loop_exit
        (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4))
        (TapeSearchBody.program k two (R 0) (R 3) (R 1))
        (TapePowerCompare.start k) TapeSearchBody.start (flag k again)
        htst rfl (by simpa only [flag, TapePowerCompare.done, Nat.mul_zero,
          Nat.add_zero] using hstop)
      simpa only [program, start, done, cost, Nat.mul_zero, Nat.add_zero] using he
  | succ fuel ih =>
      have htst := runs_test k R σ c D ho hs hd ht
      have hb := TapeSearchBody.runs_body k two (R 0) (R 3) (R 1)
        (candidateStore R σ c) c
        (by simpa [candidateStore, R.injective.ne (by decide : (0 : Fin 5) ≠ 1)] using ho)
        (by simpa [candidateStore, R.injective.ne (by decide : (3 : Fin 5) ≠ 1)] using hd)
        (by simp [candidateStore])
      simp only [candidateStore, Function.update_idem] at hb
      have hi := loop_iter
        (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4))
        (TapeSearchBody.program k two (R 0) (R 3) (R 1))
        (TapePowerCompare.start k) TapeSearchBody.start (flag k again)
        htst rfl (by simpa only [flag, TapePowerCompare.done, Nat.mul_zero,
          Nat.add_zero] using hgo 0 (Nat.zero_lt_succ _))
        hb (TapeSearchBody.program_done k two (R 0) (R 3) (R 1) _)
      have hshift (j : ℕ) :
          c + TapeSearchBody.amount two + TapeSearchBody.amount two * j =
            c + TapeSearchBody.amount two * (j + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hr := ih (c + TapeSearchBody.amount two)
        (by
          intro j hj
          rw [hshift]
          exact hgo (j + 1) (Nat.succ_lt_succ hj))
        (by rw [hshift]; exact hstop)
      have h := hi.trans hr
      simpa only [program, start, done, cost, candidateStore, hshift] using h

@[simp] theorem program_done (k : ℕ) (two : Bool) (again : Ordering → Bool)
    (R : Registers) (h : TapeHeads) : program k two again R (done k) h = none := rfl

/-- Continue the search exactly when the comparison returns less-than. -/
def continueLt (o : Ordering) : Bool := decide (o = .lt)
/-- Continue the search unless the comparison returns greater-than. -/
def continueLe (o : Ordering) : Bool := !decide (o = .gt)

theorem continueLt_result (a b : ℕ) :
    continueLt (TapeUnaryCompareScan.result a b) = decide (a < b) := by
  simp [continueLt, TapeUnaryCompareScan.result_eq_lt_iff]

theorem continueLe_result (a b : ℕ) :
    continueLe (TapeUnaryCompareScan.result a b) = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · have hnot : ¬ b < a := by omega
    simp [continueLe, TapeUnaryCompareScan.result_eq_gt_iff, h, hnot]
  · have hlt : b < a := by omega
    simp [continueLe, TapeUnaryCompareScan.result_eq_gt_iff, h, hlt]

theorem runs_cube (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate (d ^ 2) true) :
    RunsIn (program 3 false continueLt R).step
      (cfg (start 3) (storeTapes (candidateStore R σ 0)))
      (cfg (done 3) (storeTapes (TapePowerCompare.outputStore 3 (R 0) (R 3)
        (candidateStore R σ (hashDimension d)) (hashDimension d))))
      (cost 3 false (d ^ 2) (hashDimension d) 0) := by
  have h := runs_search 3 false continueLt R σ (d ^ 2) (hashDimension d) 0
    ho hs hd ht
    (by
      intro j hj
      have hjp := (cube_lt_iff_lt_hashDimension d j).2 hj
      simpa [TapeSearchBody.amount, continueLt_result] using hjp)
    (by
      have hp := hashDimension_cube_bound d
      simp [TapeSearchBody.amount, continueLt_result, Nat.not_lt.mpr hp])
  simpa [TapeSearchBody.amount] using h

theorem runs_sixth_boundary (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate d true) :
    RunsIn (program 6 true continueLe R).step
      (cfg (start 6) (storeTapes (candidateStore R σ 0)))
      (cfg (done 6) (storeTapes (TapePowerCompare.outputStore 6 (R 0) (R 3)
        (candidateStore R σ (independenceOrder d + 2)) (independenceOrder d + 2))))
      (cost 6 true d (independenceOrder d / 2 + 1) 0) := by
  have htEven := independenceOrder_even d
  have hterminal : 2 * (independenceOrder d / 2 + 1) = independenceOrder d + 2 := by
    obtain ⟨a, ha⟩ := htEven
    omega
  have h := runs_search 6 true continueLe R σ d (independenceOrder d / 2 + 1) 0
    ho hs hd ht
    (by
      intro j hj
      have hjle : 2 * j ≤ independenceOrder d := by omega
      have hp := Nat.le_trans (Nat.pow_le_pow_left hjle 6) (independenceOrder_pow_le d)
      simpa [TapeSearchBody.amount, continueLe_result] using hp)
    (by
      have hp := independenceOrder_next_pow_gt d
      simp [TapeSearchBody.amount, continueLe_result, hterminal, Nat.not_le.mpr hp])
  simpa [TapeSearchBody.amount, hterminal] using h

end TapePowerSearch
end DepthThreeLowerBound

end Complexity

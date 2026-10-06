/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexitylib.Algebraic.LowerBound.MCSP.SubcubeRepetition

/-!
# Repeated exact-cost anchors

Validates: fixing one selector block to a target of exact positive De Morgan
AND/OR cost `s` forces every block of a cost-at-most-`s` completion to equal it.
This checked research artifact is outside the public library import graph.
-/

namespace Complexity.MCSP.Exploration

open Algebraic

/-- Restrict each of the leading selector inputs to false. -/
def zeroCofactor {n : ℕ} : (k : ℕ) → Target Bool (n + k) 1 → Target Bool n 1
  | 0, target => target
  | k + 1, target => zeroCofactor k (fun x => target (Fin.cons false x))

/-- Repeat a target on every setting of the leading selector inputs. -/
def repeatTarget {n : ℕ} (target : Target Bool n 1) : (k : ℕ) → Target Bool (n + k) 1
  | 0 => target
  | k + 1 => Algebraic.MCSP.muxTarget (repeatTarget target k) (repeatTarget target k)

/-- The repeated completion has the required anchor. -/
theorem zeroCofactor_repeatTarget {n : ℕ} (target : Target Bool n 1) (k : ℕ) :
    zeroCofactor k (repeatTarget target k) = target := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- Adding ignored selector variables preserves the inner De Morgan cost. -/
theorem repeatTarget_cost {n : ℕ} (target : Target Bool n 1) (k : ℕ) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
      (repeatTarget target k) =
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost target := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [repeatTarget, Algebraic.MCSP.costComplexity_muxTarget_self] using ih

/-- An exact-cost anchor forbids all dependence on additional selector inputs. -/
theorem eq_repeatTarget_of_exact_anchor {n s : ℕ} (hs : 1 ≤ s)
    (anchor : Target Bool n 1)
    (hanchor : Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost anchor = s)
    (k : ℕ) (target : Target Bool (n + k) 1)
    (hzero : zeroCofactor k target = anchor)
    (hsmall : Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost target ≤ s) :
    target = repeatTarget anchor k := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    let left : Target Bool (n + k) 1 := fun x => target (Fin.cons false x)
    let right : Target Bool (n + k) 1 := fun x => target (Fin.cons true x)
    have hsplit : target = Algebraic.MCSP.muxTarget left right := by
      funext x o
      have hx := Fin.cons_self_tail x
      cases hb : x 0 <;> simpa [Algebraic.MCSP.muxTarget, left, right, hb] using
        congrArg (fun y => target y o) hx.symm
    have hleft : Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost left ≤ s :=
      (Algebraic.MCSP.costComplexity_le_muxTarget_left left right).trans (hsplit ▸ hsmall)
    have hrepeat : left = repeatTarget anchor k := ih left hzero hleft
    have hcost : Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost left = s := by
      rw [hrepeat, repeatTarget_cost, hanchor]
    have heq : left = right := by
      by_contra hne
      have hpos : (1 : ℕ∞) ≤
          Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost left := by
        rw [hcost]
        exact_mod_cast hs
      have hstrict :=
        (Algebraic.MCSP.costComplexity_muxTarget_ge_add_one hne (Or.inl hpos)).1
      rw [hcost, ← hsplit] at hstrict
      have hbad := hstrict.trans hsmall
      have hnat : s + 1 ≤ s := by exact_mod_cast hbad
      exact Nat.not_succ_le_self s hnat
    rw [hsplit, ← heq, hrepeat]
    rfl

/-- On the anchored slice, MCSP accepts exactly the repeated completion. -/
theorem cost_le_iff_eq_repeatTarget {n s : ℕ} (hs : 1 ≤ s)
    (anchor : Target Bool n 1)
    (hanchor : Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost anchor = s)
    (k : ℕ) (target : Target Bool (n + k) 1)
    (hzero : zeroCofactor k target = anchor) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost target ≤ s ↔
      target = repeatTarget anchor k := by
  constructor
  · exact eq_repeatTarget_of_exact_anchor hs anchor hanchor k target hzero
  · intro heq
    rw [heq, repeatTarget_cost, hanchor]

end Complexity.MCSP.Exploration

#print axioms Complexity.MCSP.Exploration.cost_le_iff_eq_repeatTarget

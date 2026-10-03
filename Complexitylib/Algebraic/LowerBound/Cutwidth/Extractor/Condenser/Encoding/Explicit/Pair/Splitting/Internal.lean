/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit
import Mathlib.Tactic.Linarith

/-!
# Integer budgets for splitting the scheduled condenser

The coordinate capacity supplies a lower bound on the total output width.
Its upper rate bound and a sufficient entropy budget then give both
inequalities required to split the output into two conditional blocks.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem pair_split_of_budget {u H k b s E : Nat}
    (positive : 0 < u) (capacity : k ≤ H + H)
    (rate : u * (H + H) ≤ (u + 1) * k + u * b)
    (budget : u * (b + 2 * (s + E)) ≤ (u - 1) * k) :
    s ≤ H ∧ H + s + E ≤ k := by
  have pred : u - 1 + 1 = u := Nat.sub_add_cancel positive
  have pred_mul := congrArg (fun z => z * k) pred
  have scaled : 2 * u * (H + s + E) ≤ 2 * u * k := by
    nlinarith only [rate, budget, pred_mul]
  have entropy : H + s + E ≤ k :=
    le_of_mul_le_mul_left scaled (by lia : 0 < 2 * u)
  exact ⟨by lia, entropy⟩

theorem explicitCondenserHalfWidth_capacity (n k e : Nat) {u : Nat} (rate : 0 < u) :
    k ≤ explicitCondenserHalfWidth n k e u + explicitCondenserHalfWidth n k e u := by
  rw [explicitCondenserHalfWidth_double]
  calc
    k ≤ sparsePowerBits u (explicitCondenserBudget n k e) *
        condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) :=
      explicitCondenser_entropy_capacity n k e rate
    _ ≤ sparseFieldBits u (explicitCondenserBudget n k e) *
        condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = _ := Nat.mul_comm _ _

theorem explicitCondenserPair_split_budget (n k e u s E : Nat) (rate : 1 < u)
    (budget : u * (sparseFieldBits u (explicitCondenserBudget n k e) +
        2 * (s + E)) ≤ (u - 1) * k) :
    s ≤ explicitCondenserHalfWidth n k e u ∧
      explicitCondenserHalfWidth n k e u + s + E ≤ k :=
  pair_split_of_budget (by lia) (explicitCondenserHalfWidth_capacity n k e (by lia))
    (explicitCondenserHalfWidth_rate n k e u) budget

theorem explicitCondenserPair_split_budget_of_bound (n k e u s E : Nat) (rate : 1 < u)
    (budget : u * (6 * (u + 1) * explicitCondenserBudget n k e +
        2 * (s + E)) ≤ (u - 1) * k) :
    s ≤ explicitCondenserHalfWidth n k e u ∧
      explicitCondenserHalfWidth n k e u + s + E ≤ k := by
  apply explicitCondenserPair_split_budget n k e u s E rate
  exact (Nat.mul_le_mul_left u
    (Nat.add_le_add_right (explicitCondenser_fieldBits_le n k e u) _)).trans budget

theorem explicitCondenserPair_next_entropy (n k e u E : Nat) (rate : 1 < u)
    (budget : u * (sparseFieldBits u (explicitCondenserBudget n k e) + 2 * E) ≤
      (u - 1) * k) :
    k - explicitCondenserHalfWidth n k e u - E ≤ explicitCondenserHalfWidth n k e u ∧
      explicitCondenserHalfWidth n k e u +
          (k - explicitCondenserHalfWidth n k e u - E) + E = k := by
  have enough := explicitCondenserPair_split_budget n k e u 0 E rate (by simpa using budget)
  have capacity := explicitCondenserHalfWidth_capacity n k e (u := u) (by lia)
  constructor <;> lia

end Algebraic.Cutwidth.Extractor.Internal

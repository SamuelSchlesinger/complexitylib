/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation.Optimal
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.ENatENNReal

/-!
# Directed simulation overhead

For finite source signatures, the local overhead of a realization is the
largest operation-gadget size, normalized to be at least one. The normalization
is essential because free output wires allow projections to have zero-gate
implementations. Taking the infimum over realizations gives an extended-natural
directed overhead; `⊤` means that no realization exists. Its logarithm is an
extended-real directed distance satisfying the triangle inequality.
-/

@[expose] public section

namespace Algebraic

namespace Realization

/-- Maximum selected gadget size, normalized to be at least one. -/
def overhead
    [Fintype σ.Op]
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target) : Nat :=
  max 1 (Finset.univ.sup fun op => (realization.operation op).size)

theorem one_le_overhead
    [Fintype σ.Op]
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target) :
    1 ≤ realization.overhead :=
  Nat.le_max_left 1 _

theorem operation_size_le_overhead
    [Fintype σ.Op]
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (op : σ.Op) :
    (realization.operation op).size ≤ realization.overhead := by
  exact (Finset.le_sup (f := fun op => (realization.operation op).size)
    (Finset.mem_univ op)).trans (Nat.le_max_right 1 _)

@[simp] theorem overhead_id
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) :
    (Realization.id interpretation).overhead = 1 := by
  apply Nat.le_antisymm
  · apply max_le le_rfl
    apply Finset.sup_le
    intro op _
    rfl
  · exact (Realization.id interpretation).one_le_overhead

/-- Local overhead is submultiplicative under realization composition. -/
theorem overhead_comp
    [Fintype σ.Op] [Fintype τ.Op]
    {source : Interpretation σ U}
    {middle : Interpretation τ U}
    {target : Interpretation υ U}
    (outer : Realization τ υ middle target)
    (inner : Realization σ τ source middle) :
    (outer.comp inner).overhead ≤ outer.overhead * inner.overhead := by
  apply max_le
  · exact Nat.one_le_iff_ne_zero.mpr <|
      Nat.mul_ne_zero
        (Nat.ne_of_gt outer.one_le_overhead)
        (Nat.ne_of_gt inner.one_le_overhead)
  · apply Finset.sup_le
    intro op _
    change (outer.toTranslation.compile (inner.operation op)).size ≤
      outer.overhead * inner.overhead
    exact (outer.toTranslation.compile_size_le_mul (inner.operation op)
      (fun targetOp => outer.operation_size_le_overhead targetOp)).trans <|
        Nat.mul_le_mul_left outer.overhead
          (inner.operation_size_le_overhead op)

end Realization

namespace Interpretation

/-- Optimal normalized local overhead for realizing `source` in `target`.
The value is `⊤` if no realization exists. -/
noncomputable def _root_.Cslib.Circuits.Interpretation.simulationOverhead
    [Fintype σ.Op]
    (source : Interpretation σ U)
    (target : Interpretation τ U) : ℕ∞ :=
  ⨅ realization : Realization σ τ source target,
    (realization.overhead : ℕ∞)

export Cslib.Circuits.Interpretation (simulationOverhead)

theorem _root_.Cslib.Circuits.Interpretation.simulationOverhead_le
    [Fintype σ.Op]
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target) :
    source.simulationOverhead target ≤ realization.overhead :=
  iInf_le _ realization

export Cslib.Circuits.Interpretation (simulationOverhead_le)

theorem _root_.Cslib.Circuits.Interpretation.one_le_simulationOverhead
    [Fintype σ.Op]
    (source : Interpretation σ U)
    (target : Interpretation τ U) :
    1 ≤ source.simulationOverhead target := by
  apply le_iInf
  intro realization
  exact_mod_cast realization.one_le_overhead

export Cslib.Circuits.Interpretation (one_le_simulationOverhead)

@[simp] theorem _root_.Cslib.Circuits.Interpretation.simulationOverhead_self
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) :
    interpretation.simulationOverhead interpretation = 1 := by
  apply le_antisymm
  · simpa using
      (Interpretation.simulationOverhead_le
        (Realization.id interpretation))
  · exact interpretation.one_le_simulationOverhead interpretation

export Cslib.Circuits.Interpretation (simulationOverhead_self)

/-- A directed overhead is finite exactly when a realization exists. -/
theorem _root_.Cslib.Circuits.Interpretation.simulationOverhead_lt_top_iff
    [Fintype σ.Op]
    (source : Interpretation σ U)
    (target : Interpretation τ U) :
    source.simulationOverhead target < ⊤ ↔
      Nonempty (Realization σ τ source target) := by
  unfold Interpretation.simulationOverhead
  exact ENat.iInf_natCast_lt_top

export Cslib.Circuits.Interpretation (simulationOverhead_lt_top_iff)

/-- Every interpretation has finite directed overhead into a functionally
complete target interpretation. -/
theorem _root_.Cslib.Circuits.Interpretation.simulationOverhead_lt_top_of_functionallyComplete
    [Fintype σ.Op]
    (source : Interpretation σ U)
    (target : Interpretation τ U)
    (complete : target.FunctionallyComplete) :
    source.simulationOverhead target < ⊤ := by
  rw [source.simulationOverhead_lt_top_iff target]
  exact ⟨Realization.ofFunctionalCompleteness source target complete⟩

export Cslib.Circuits.Interpretation (simulationOverhead_lt_top_of_functionallyComplete)

/-- Multiplicative triangle inequality for optimal local overhead. -/
theorem _root_.Cslib.Circuits.Interpretation.simulationOverhead_triangle
    [Fintype σ.Op] [Fintype τ.Op]
    (source : Interpretation σ U)
    (middle : Interpretation τ U)
    (target : Interpretation υ U) :
    source.simulationOverhead target ≤
      source.simulationOverhead middle *
        middle.simulationOverhead target := by
  let left := source.simulationOverhead middle
  let right := middle.simulationOverhead target
  have leftNonzero : left ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le
      (source.one_le_simulationOverhead middle))
  have rightNonzero : right ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le
      (middle.one_le_simulationOverhead target))
  calc
    source.simulationOverhead target ≤
        ⨅ inner : Realization σ τ source middle,
          ⨅ outer : Realization τ υ middle target,
            (inner.overhead : ℕ∞) * outer.overhead := by
      refine le_iInf fun inner => le_iInf fun outer => ?_
      exact (Interpretation.simulationOverhead_le (outer.comp inner)).trans <|
        by
          exact_mod_cast (outer.overhead_comp inner).trans_eq
            (Nat.mul_comm outer.overhead inner.overhead)
    _ = ⨅ inner : Realization σ τ source middle,
          (inner.overhead : ℕ∞) * right := by
      congr 1
      funext inner
      unfold right Interpretation.simulationOverhead
      rw [ENat.mul_iInf_of_ne]
      exact_mod_cast Nat.ne_of_gt inner.one_le_overhead
    _ = left * right := by
      unfold left Interpretation.simulationOverhead
      rw [ENat.iInf_mul_of_ne rightNonzero]
    _ = source.simulationOverhead middle *
        middle.simulationOverhead target := rfl

export Cslib.Circuits.Interpretation (simulationOverhead_triangle)

/-- Logarithmic directed distance associated with optimal local overhead. -/
noncomputable def _root_.Cslib.Circuits.Interpretation.simulationDistance
    [Fintype σ.Op]
    (source : Interpretation σ U)
    (target : Interpretation τ U) : EReal :=
  ENNReal.log (ENat.toENNReal (source.simulationOverhead target))

export Cslib.Circuits.Interpretation (simulationDistance)

@[simp] theorem _root_.Cslib.Circuits.Interpretation.simulationDistance_self
    [Fintype σ.Op]
    (interpretation : Interpretation σ U) :
    interpretation.simulationDistance interpretation = 0 := by
  simp [Interpretation.simulationDistance]

export Cslib.Circuits.Interpretation (simulationDistance_self)

theorem _root_.Cslib.Circuits.Interpretation.simulationDistance_nonnegative
    [Fintype σ.Op]
    (source : Interpretation σ U)
    (target : Interpretation τ U) :
    0 ≤ source.simulationDistance target := by
  rw [Interpretation.simulationDistance, ENNReal.zero_le_log_iff]
  exact_mod_cast source.one_le_simulationOverhead target

export Cslib.Circuits.Interpretation (simulationDistance_nonnegative)

/-- Additive triangle inequality for logarithmic directed distance. -/
theorem _root_.Cslib.Circuits.Interpretation.simulationDistance_triangle
    [Fintype σ.Op] [Fintype τ.Op]
    (source : Interpretation σ U)
    (middle : Interpretation τ U)
    (target : Interpretation υ U) :
    source.simulationDistance target ≤
      source.simulationDistance middle +
        middle.simulationDistance target := by
  unfold Interpretation.simulationDistance
  calc
    ENNReal.log (ENat.toENNReal (source.simulationOverhead target)) ≤
        ENNReal.log
          (ENat.toENNReal (source.simulationOverhead middle *
            middle.simulationOverhead target)) := by
      apply ENNReal.log_le_log
      exact ENat.toENNReal_mono
        (source.simulationOverhead_triangle middle target)
    _ = ENNReal.log
          (ENat.toENNReal (source.simulationOverhead middle)) +
        ENNReal.log
          (ENat.toENNReal (middle.simulationOverhead target)) := by
      rw [ENat.toENNReal_mul, ENNReal.log_mul_add]

export Cslib.Circuits.Interpretation (simulationDistance_triangle)

end Interpretation

end Algebraic

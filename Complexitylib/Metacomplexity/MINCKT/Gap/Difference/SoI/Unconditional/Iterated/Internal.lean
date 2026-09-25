/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Internal
import Complexitylib.Models.TuringMachine.OutputBounds

/-!
# The iterated-clock schedule -- proof internals
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

theorem clockIterate_zero_internal (clock : ℕ → ℕ) (time : ℕ) :
    clockIterate clock 0 time = time := rfl

theorem clockIterate_succ_internal (clock : ℕ → ℕ)
    (iterations time : ℕ) :
    clockIterate clock (iterations + 1) time =
      clock (clockIterate clock iterations time) := rfl

theorem clockIterate_monotone_internal {clock : ℕ → ℕ}
    (hclock : Monotone clock) (iterations : ℕ) :
    Monotone (clockIterate clock iterations) := by
  induction iterations with
  | zero => exact fun _ _ h => h
  | succ iterations ih =>
      intro first second hle
      exact hclock (ih hle)

theorem clockIterate_dominates_internal {clock : ℕ → ℕ}
    (hclock : ∀ time, time ≤ clock time) (iterations time : ℕ) :
    time ≤ clockIterate clock iterations time := by
  induction iterations with
  | zero => exact le_rfl
  | succ iterations ih => exact ih.trans (hclock _)

theorem paddedTime_size_le_internal (inst : MINCKT.Instance) :
    inst.output.length + inst.condition.length ≤ paddedTime inst :=
  le_max_left _ _

theorem paddedTime_time_le_internal (inst : MINCKT.Instance) :
    inst.time ≤ paddedTime inst :=
  le_max_right _ _

theorem paddedTime_le_total_internal (inst : MINCKT.Instance) :
    paddedTime inst ≤ inst.time + inst.output.length + inst.condition.length := by
  apply max_le
  · omega
  · omega

theorem ordinaryParameters_transformedTime_internal (clock : ℕ → ℕ)
    (inst : MINKT.Instance) :
    (ordinaryParameters clock).transformedTime inst = clock inst.time := rfl

theorem conditionalParameters_transformedTime_internal (clock : ℕ → ℕ)
    (inst : MINCKT.Instance) :
    (conditionalParameters clock).transformedTime inst =
      clockIterate clock 4
        (inst.time + inst.output.length + inst.condition.length) := rfl

theorem plan_pairInputTime_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).pairInputTime inst =
      clockIterate clock 1 (paddedTime inst) := rfl

theorem plan_conditionInputTime_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).conditionInputTime inst =
      clockIterate clock 3 (paddedTime inst) := rfl

theorem plan_soiTime_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).soiTime inst =
      clockIterate clock 2 (paddedTime inst) := rfl

theorem plan_pairUpperLoss_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).pairUpperLoss inst =
      pairUpperLoss inst := rfl

theorem plan_correction_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).correction inst = correction inst := rfl

theorem IsRegularClock.ordinaryParameters_widening_internal
    {clock : ℕ → ℕ} (hclock : IsRegularClock clock) :
    (ordinaryParameters clock).IsWidening := by
  intro _outputLength time
  exact hclock.dominates time

theorem IsRegularClock.conditionalParameters_widening_internal
    {clock : ℕ → ℕ} (hclock : IsRegularClock clock) :
    (conditionalParameters clock).IsWidening := by
  intro outputLength conditionLength time
  exact (by omega : time ≤ time + outputLength + conditionLength) |>.trans
    (clockIterate_dominates_internal hclock.dominates 4 _)

theorem not_satisfiesBounds_ordinaryParameters_internal {tapes : ℕ}
    (machine : TM tapes) (clock : ℕ → ℕ)
    (estimate : GapMINKT.Logarithmic.Estimator) :
    ¬ estimate.SatisfiesBounds machine (ordinaryParameters clock) := by
  intro h
  have hlower := (h ⟨List.replicate (clock 0 + 1) true, 0⟩).2
  have htop : machine.timeBoundedKolmogorovComplexity
      (List.replicate (clock 0 + 1) true) (clock 0) = ⊤ := by
    rw [TM.timeBoundedKolmogorovComplexity_eq_top_iff_internal]
    rintro ⟨program, c, steps, hsteps, hrun, -, hout⟩
    have hfar := TM.reachesIn_output_cells_far hrun (clock 0 + 1)
      (by show 0 + steps < clock 0 + 1; omega)
    have hbit := hout.1 (clock 0) (by simp)
    rw [hfar] at hbit
    simp [Γ.ofBool] at hbit
  change machine.timeBoundedKolmogorovComplexity
      (List.replicate (clock 0 + 1) true) (clock 0) ≤ _ at hlower
  rw [htop] at hlower
  exact WithTop.not_top_le_coe _ hlower

theorem IsRegularClock.compatible_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock soiLoss : ℕ → ℕ}
    {pairUpperLoss correction : MINCKT.Instance → ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hloss : LossBudget clock pairUpperLoss correction soiLoss)
    (hpair : ∀ inst,
      ordinaryMachine.timeBoundedKolmogorovComplexity
            (pair inst.output inst.condition)
              ((plan clock pairUpperLoss correction).pairInputTime inst) ≤
        inst.complexity conditionalMachine +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              inst.condition inst.time +
          ((plan clock pairUpperLoss correction).pairUpperLoss inst : WithTop ℕ)) :
    Compatible (plan clock pairUpperLoss correction) ordinaryMachine
      conditionalMachine (ordinaryParameters clock) (conditionalParameters clock)
        clock soiLoss := by
  constructor
  · intro inst
    have hstep : clockIterate clock 3 (paddedTime inst) ≤
        clockIterate clock 4 (paddedTime inst) := by
      exact hclock.dominates _
    have hpad := clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_total_internal inst)
    exact hstep.trans hpad
  · intro inst
    exact (paddedTime_size_le_internal inst).trans
      (clockIterate_dominates_internal hclock.dominates 2 _)
  · intro inst
    rfl
  · intro inst
    exact clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_total_internal inst)
  · intro inst
    rfl
  · exact hpair
  · intro inst
    simp [Plan.conditionInput, GapMINKT.Logarithmic.Parameters.logarithmicSlack,
      GapMINKT.Logarithmic.Parameters.transformedTime, ordinaryParameters, plan]
    exact hloss.upper inst
  · intro inst
    simp [Plan.pairInput, GapMINKT.Logarithmic.Parameters.logarithmicSlack,
      GapMINKT.Logarithmic.Parameters.transformedTime, GapMINCKT.Parameters.logarithmicSlack,
      GapMINCKT.Parameters.transformedTime, ordinaryParameters, conditionalParameters, plan]
    exact hloss.lower inst

theorem IsRegularClock.compatible_of_pairComposition_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock soiLoss : ℕ → ℕ}
    {pairUpperLoss correction : MINCKT.Instance → ℕ}
    {composition : PairCompositionPlan}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hloss : LossBudget clock pairUpperLoss correction soiLoss)
    (hsupports : SupportsPairUpper (plan clock pairUpperLoss correction)
      composition ordinaryMachine conditionalMachine) :
    Compatible (plan clock pairUpperLoss correction) ordinaryMachine
      conditionalMachine (ordinaryParameters clock) (conditionalParameters clock)
        clock soiLoss :=
  hclock.compatible_internal hloss hsupports.pair_upper_internal

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlots.Defs
import Complexitylib.Circuits.BarringtonStreaming.Internal

/-!
# Fixed-address Barrington compilation slots -- proof internals
-/

namespace Complexity

namespace BPSlots

theorem length_postMulFirst_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) :
    (postMulFirst permutation slots).length = slots.length := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      cases slot <;> simp [postMulFirst, ih]

theorem length_postMul_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) :
    (slots.postMul permutation).length = slots.length := by
  rw [postMul.eq_def]
  split
  · cases slots <;> rfl
  · simp [length_postMulFirst_internal]

theorem length_inverse_internal (slots : BPSlots w) :
    slots.inverse.length = slots.length := by
  simp [inverse]

theorem length_singletonAt_internal (fuel : ℕ) (instruction : BPInstr w) :
    (singletonAt fuel instruction).length = 4 ^ fuel := by
  simp [singletonAt]
  have hpositive : 0 < 4 ^ fuel := pow_pos (by omega) fuel
  omega

theorem length_emptyAt_internal (fuel : ℕ) :
    (emptyAt fuel : BPSlots w).length = 4 ^ fuel := by
  simp [emptyAt]

private theorem filterMap_postMulFirst_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) :
    (postMulFirst permutation slots).filterMap id =
      match slots.filterMap id with
      | [] => []
      | instruction :: program =>
          BPInstr.postMul instruction permutation :: program := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      cases slot with
      | none =>
          change (postMulFirst permutation slots).filterMap id = _
          exact ih
      | some instruction => simp [postMulFirst]

theorem filterMap_postMul_internal (slots : BPSlots w)
    (permutation : Equiv.Perm (Fin w)) (hne : slots ≠ []) :
    (slots.postMul permutation).filterMap id =
      BP.postMul (slots.filterMap id) permutation := by
  by_cases hprogram : slots.filterMap id = []
  · rw [postMul.eq_def, if_pos hprogram]
    cases slots with
    | nil => exact (hne rfl).elim
    | cons slot slots =>
        cases slot with
        | none =>
            have hrest : slots.filterMap id = [] := by
              simpa using hprogram
            rw [BP.postMul, if_pos hprogram]
            change BPInstr.const permutation ::
              slots.filterMap id = [BPInstr.const permutation]
            rw [hrest]
        | some instruction =>
            simp at hprogram
  · rw [postMul.eq_def, if_neg hprogram, List.filterMap_reverse,
      filterMap_postMulFirst_internal]
    rw [BP.postMul, if_neg hprogram]
    rw [List.filterMap_reverse]
    let program := slots.filterMap id
    change (match program.reverse with
      | [] => []
      | instruction :: rest =>
          BPInstr.postMul instruction permutation :: rest).reverse =
        program.modifyLast fun instruction =>
          BPInstr.postMul instruction permutation
    have hreverse : program.reverse ≠ [] := by
      simpa [program] using hprogram
    cases hreverseEq : program.reverse with
    | nil => exact (hreverse hreverseEq).elim
    | cons instruction prefixReverse =>
        have hprogramEq :
            program = prefixReverse.reverse ++ [instruction] := by
          rw [← List.reverse_inj]
          simp [hreverseEq]
        rw [hprogramEq, List.modifyLast_concat]
        simp

theorem filterMap_inverse_internal (slots : BPSlots w) :
    slots.inverse.filterMap id = BP.inverse (slots.filterMap id) := by
  rw [inverse, BP.inverse, List.filterMap_reverse]
  rw [List.reverse_inj]
  rw [List.filterMap_map]
  change List.filterMap (fun slot => slot.map BPInstr.inverse) slots =
    List.map BPInstr.inverse (List.filterMap (fun slot => slot) slots)
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      cases slot <;> simp [ih]

end BPSlots

theorem barringtonCompileSlots_length_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    (barringtonCompileSlots fuel formula target).length = 4 ^ fuel := by
  induction fuel generalizing formula target with
  | zero =>
      cases formula <;>
        simp [barringtonCompileSlots, BPSlots.singletonAt,
          BPSlots.emptyAt]
  | succ fuel ih =>
      cases formula <;>
        simp [barringtonCompileSlots,
          BPSlots.length_singletonAt_internal,
          BPSlots.length_emptyAt_internal,
          BPSlots.length_postMul_internal,
          BPSlots.length_inverse_internal, ih, pow_succ] <;>
        ring

private theorem barringtonCompileSlots_ne_nil_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonCompileSlots fuel formula target ≠ [] := by
  intro hempty
  have hlength := barringtonCompileSlots_length_internal fuel formula target
  rw [hempty] at hlength
  have hpositive : 0 < 4 ^ fuel := pow_pos (by omega) fuel
  simp at hlength
  omega

theorem barringtonCompileSlots_filterMap_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    (barringtonCompileSlots fuel formula target).filterMap id =
      barringtonCompile formula target := by
  induction fuel generalizing formula target with
  | zero =>
      cases formula with
      | var index =>
          simp [barringtonCompileSlots, BPSlots.singletonAt,
            barringtonCompile]
      | tru =>
          simp [barringtonCompileSlots, BPSlots.singletonAt,
            barringtonCompile]
      | fls =>
          simp [barringtonCompileSlots, BPSlots.emptyAt,
            barringtonCompile]
      | neg formula =>
          simp [BoolFormula.depth] at hdepth
      | conj left right =>
          simp [BoolFormula.depth] at hdepth
      | disj left right =>
          simp [BoolFormula.depth] at hdepth
  | succ fuel ih =>
      cases formula with
      | var index =>
          simp [barringtonCompileSlots, BPSlots.singletonAt,
            barringtonCompile]
      | tru =>
          simp [barringtonCompileSlots, BPSlots.singletonAt,
            barringtonCompile]
      | fls =>
          simp [barringtonCompileSlots, BPSlots.emptyAt,
            barringtonCompile]
      | neg formula =>
          have hchildDepth : formula.depth ≤ fuel := by
            simpa [BoolFormula.depth] using hdepth
          have hchild := ih formula target⁻¹ hchildDepth
          have hne := barringtonCompileSlots_ne_nil_internal
            fuel formula target⁻¹
          simp only [barringtonCompileSlots, List.filterMap_append]
          rw [BPSlots.filterMap_postMul_internal _ _ hne, hchild]
          simp [barringtonCompile]
      | conj left right =>
          have hmax : max left.depth right.depth ≤ fuel := by
            simpa [BoolFormula.depth] using hdepth
          have hleftDepth : left.depth ≤ fuel :=
            le_trans (le_max_left _ _) hmax
          have hrightDepth : right.depth ≤ fuel :=
            le_trans (le_max_right _ _) hmax
          have hleft := ih left (barringtonLeft target) hleftDepth
          have hright := ih right (barringtonRight target) hrightDepth
          let leftSlots :=
            barringtonCompileSlots fuel left (barringtonLeft target)
          let rightSlots :=
            barringtonCompileSlots fuel right (barringtonRight target)
          have hleftInverse :
              leftSlots.inverse.filterMap id =
                BP.inverse (barringtonCompile left
                  (barringtonLeft target)) := by
            rw [BPSlots.filterMap_inverse_internal, hleft]
          have hrightInverse :
              rightSlots.inverse.filterMap id =
                BP.inverse (barringtonCompile right
                  (barringtonRight target)) := by
            rw [BPSlots.filterMap_inverse_internal, hright]
          simp only [barringtonCompileSlots, List.filterMap_append]
          rw [hleft, hright, hleftInverse, hrightInverse]
          rfl
      | disj left right =>
          have hmax : max left.depth right.depth ≤ fuel := by
            simpa [BoolFormula.depth] using hdepth
          have hleftDepth : left.depth ≤ fuel :=
            le_trans (le_max_left _ _) hmax
          have hrightDepth : right.depth ≤ fuel :=
            le_trans (le_max_right _ _) hmax
          let innerTarget := target⁻¹
          let leftTarget := barringtonLeft innerTarget
          let rightTarget := barringtonRight innerTarget
          let leftBase :=
            barringtonCompileSlots fuel left leftTarget⁻¹
          let rightBase :=
            barringtonCompileSlots fuel right rightTarget⁻¹
          let leftSlots := leftBase.postMul leftTarget
          let rightSlots := rightBase.postMul rightTarget
          let commSlots := leftSlots ++ rightSlots ++ leftSlots.inverse ++
            rightSlots.inverse
          have hleftBaseNe : leftBase ≠ [] :=
            barringtonCompileSlots_ne_nil_internal fuel left leftTarget⁻¹
          have hrightBaseNe : rightBase ≠ [] :=
            barringtonCompileSlots_ne_nil_internal fuel right rightTarget⁻¹
          have hleftFilter : leftSlots.filterMap id =
              BP.postMul (barringtonCompile left leftTarget⁻¹)
                leftTarget := by
            rw [show leftSlots = leftBase.postMul leftTarget from rfl,
              BPSlots.filterMap_postMul_internal _ _ hleftBaseNe]
            exact congrArg (BP.postMul · leftTarget)
              (ih left leftTarget⁻¹ hleftDepth)
          have hrightFilter : rightSlots.filterMap id =
              BP.postMul (barringtonCompile right rightTarget⁻¹)
                rightTarget := by
            rw [show rightSlots = rightBase.postMul rightTarget from rfl,
              BPSlots.filterMap_postMul_internal _ _ hrightBaseNe]
            exact congrArg (BP.postMul · rightTarget)
              (ih right rightTarget⁻¹ hrightDepth)
          have hleftInverse :
              leftSlots.inverse.filterMap id =
                BP.inverse (BP.postMul
                  (barringtonCompile left leftTarget⁻¹) leftTarget) := by
            rw [BPSlots.filterMap_inverse_internal, hleftFilter]
          have hrightInverse :
              rightSlots.inverse.filterMap id =
                BP.inverse (BP.postMul
                  (barringtonCompile right rightTarget⁻¹) rightTarget) := by
            rw [BPSlots.filterMap_inverse_internal, hrightFilter]
          have hcommNe : commSlots ≠ [] := by
            intro hempty
            have hlength := congrArg List.length hempty
            simp [commSlots, leftSlots, leftBase,
              BPSlots.length_postMul_internal,
              barringtonCompileSlots_length_internal] at hlength
          rw [show barringtonCompileSlots (fuel + 1) (.disj left right)
            target = commSlots.postMul target from rfl]
          rw [BPSlots.filterMap_postMul_internal _ _ hcommNe]
          simp only [barringtonCompile]
          apply congrArg (BP.postMul · target)
          simp only [commSlots, List.filterMap_append,
            BP.commutatorProgram]
          rw [hleftFilter, hrightFilter, hleftInverse, hrightInverse]

theorem barringtonCompileSlots_occupiedCount_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    ((barringtonCompileSlots fuel formula target).filterMap id).length =
      barringtonInstructionCount formula := by
  rw [barringtonCompileSlots_filterMap_internal fuel formula target hdepth]
  exact (barringtonInstructionCount_eq_length_internal formula target).symm

end Complexity

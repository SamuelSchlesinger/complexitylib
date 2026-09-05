/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BarringtonCompiler
public import Complexitylib.Circuits.BarringtonConverse
public import Complexitylib.Circuits.BarringtonTyped.Defs

/-!
# Fixed-arity nonuniform Barrington families -- proof internals
-/


public section

namespace Complexity

/-- Compile every positive-arity formula through the fixed Barrington target.
The zero-input answer is evaluated directly. -/
private def formulaToBP
    (F : FixedArityFormulaFamily) : FixedArityBPFamily 5 where
  emptyOutput := BoolFormula.eval (fun _ => false) (F.formula 0)
  positiveProgram n :=
    barringtonCompile (F.formula (n + 1)) barringtonTargetBase
  positiveQuery _ := 0
  variables_lt := by
    intro n instruction hinstruction
    apply Nat.lt_succ_iff.mpr
    apply barringtonCompile_var_bound
      (F.formula (n + 1)) barringtonTargetBase n
    · intro index hindex
      exact Nat.lt_succ_iff.mp (F.variables_lt (n + 1) index hindex)
    · exact hinstruction

private theorem formulaToBP_function
    (F : FixedArityFormulaFamily) :
    (formulaToBP F).function = F.function := by
  funext n input
  cases n with
  | zero =>
      simp only [FixedArityBPFamily.function,
        formulaToBP, FixedArityFormulaFamily.function]
      apply BoolFormula.eval_eq_of_agree
      intro index hindex
      exact False.elim (Nat.not_lt_zero index
        (F.variables_lt 0 index hindex))
  | succ n =>
      have hsemantics := barringtonCompile_computes
        (F.formula (n + 1)) barringtonTargetBase
        barringtonTargetBase_spec.1 barringtonTargetBase_spec.2
      simp only [FixedArityBPFamily.function, formulaToBP,
        FixedArityFormulaFamily.function]
      cases hvalue :
          BoolFormula.eval input.toTotal (F.formula (n + 1)) with
      | false =>
          have heval := hsemantics input.toTotal
          simp only [hvalue] at heval
          simp [heval]
      | true =>
          have heval := hsemantics input.toTotal
          simp only [hvalue] at heval
          simpa only [heval, ite_true] using
            (show
              decide (barringtonTargetBase (0 : Fin 5) ≠ 0) = true by
              decide)

private theorem formulaToBP_polynomialLength
    (F : FixedArityFormulaFamily) (hF : F.LogDepth) :
    (formulaToBP F).PolynomialLength := by
  obtain ⟨c, hc⟩ := hF
  refine ⟨4 ^ c, 2 * c, fun n => ?_⟩
  cases n with
  | zero => simp [FixedArityBPFamily.length]
  | succ n =>
      calc
        (formulaToBP F).length (n + 1)
            = (barringtonCompile (F.formula (n + 1))
                barringtonTargetBase).length := rfl
        _ ≤ 4 ^ (F.formula (n + 1)).depth :=
          barringtonCompile_length_le _ _
        _ ≤ 4 ^ (c * Nat.log 2 (n + 1) + c) :=
          Nat.pow_le_pow_right (by omega) (hc (n + 1))
        _ ≤ 4 ^ c * ((n + 1) + 1) ^ (2 * c) :=
          four_pow_logDepth_le_poly c (n + 1)

/-- Turn each positive-arity program into its balanced decision formula and
turn the separate zero-input answer into a Boolean constant. -/
private def bpToFormula {w : ℕ}
    (R : FixedArityBPFamily w) : FixedArityFormulaFamily where
  formula
    | 0 => if R.emptyOutput then .tru else .fls
    | n + 1 =>
        BP.decisionFormula (R.positiveProgram n) (R.positiveQuery n)
  variables_lt := by
    intro n index hindex
    cases n with
    | zero =>
        simp only at hindex
        split_ifs at hindex <;> simp_all [BoolFormula.vars]
    | succ n =>
        exact BP.vars_decisionFormula_lt
          (R.positiveProgram n) (R.positiveQuery n)
          (R.variables_lt n) index hindex

private theorem bpToFormula_function {w : ℕ}
    (R : FixedArityBPFamily w) :
    (bpToFormula R).function = R.function := by
  funext n input
  cases n with
  | zero =>
      cases houtput : R.emptyOutput <;>
        simp [bpToFormula, FixedArityFormulaFamily.function,
          FixedArityBPFamily.function, houtput, BoolFormula.eval]
  | succ n =>
      apply Bool.eq_iff_iff.mpr
      simpa only [bpToFormula, FixedArityFormulaFamily.function,
        FixedArityBPFamily.function, decide_eq_true_eq] using
        BP.eval_decisionFormula_eq_true input.toTotal
          (R.positiveProgram n) (R.positiveQuery n)

private theorem bpToFormula_logDepth
    (R : FixedArityBPFamily 5) (hR : R.PolynomialLength) :
    (bpToFormula R).LogDepth := by
  obtain ⟨C, p, hp⟩ := hR
  let c := 6 * (Nat.clog 2 C + p + 1) + 2
  refine ⟨c, fun n => ?_⟩
  cases n with
  | zero =>
      cases houtput : R.emptyOutput <;>
        simp [FixedArityFormulaFamily.depth, bpToFormula,
          houtput, BoolFormula.depth]
  | succ n =>
      have hdepth :
          (BP.decisionFormula (R.positiveProgram n)
            (R.positiveQuery n)).depth ≤
            6 * Nat.clog 2 (R.positiveProgram n).length + 2 := by
        simpa using BP.depth_decisionFormula_le
          (R.positiveProgram n) (R.positiveQuery n)
      have hclog := clog_le_of_polynomial_bound C p (n + 1)
        (R.positiveProgram n).length (hp (n + 1))
      have hcoefficient : 6 * p ≤ c := by
        simp only [c]
        omega
      have hconstant : 6 * Nat.clog 2 C + 6 * p + 2 ≤ c := by
        simp only [c]
        omega
      calc
        (bpToFormula R).depth (n + 1)
            ≤ 6 * Nat.clog 2 (R.positiveProgram n).length + 2 :=
          hdepth
        _ ≤ 6 *
              (Nat.clog 2 C + p * (Nat.log 2 (n + 1) + 1)) + 2 := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 6 hclog) 2
        _ = (6 * p) * Nat.log 2 (n + 1) +
            (6 * Nat.clog 2 C + 6 * p + 2) := by ring
        _ ≤ c * Nat.log 2 (n + 1) + c :=
          Nat.add_le_add
            (Nat.mul_le_mul_right _ hcoefficient) hconstant

theorem fixedArityFormulaFamily_exists_bp_internal
    (F : FixedArityFormulaFamily) (hF : F.LogDepth) :
    ∃ R : FixedArityBPFamily 5,
      R.PolynomialLength ∧ R.function = F.function :=
  ⟨formulaToBP F, formulaToBP_polynomialLength F hF,
    formulaToBP_function F⟩

theorem fixedArityBPFamily_exists_formula_internal
    (R : FixedArityBPFamily 5) (hR : R.PolynomialLength) :
    ∃ F : FixedArityFormulaFamily,
      F.LogDepth ∧ F.function = R.function :=
  ⟨bpToFormula R, bpToFormula_logDepth R hR, bpToFormula_function R⟩

theorem formulaNC1_subset_width5BP_internal :
    FormulaNC1 ⊆ Width5BP := by
  rintro f ⟨F, hdepth, hcomputes⟩
  obtain ⟨R, hlength, hfunction⟩ :=
    fixedArityFormulaFamily_exists_bp_internal F hdepth
  exact ⟨R, hlength, hfunction.trans hcomputes⟩

theorem width5BP_subset_formulaNC1_internal :
    Width5BP ⊆ FormulaNC1 := by
  rintro f ⟨R, hlength, hdecides⟩
  obtain ⟨F, hdepth, hfunction⟩ :=
    fixedArityBPFamily_exists_formula_internal R hlength
  exact ⟨F, hdepth, hfunction.trans hdecides⟩

end Complexity

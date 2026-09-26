/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.ModelChecking.Defs
public import Complexitylib.DescriptiveComplexity.SecondOrder.ModelChecking.Internal
public import Complexitylib.DescriptiveComplexity.ModelChecking

/-!
# Verified checking of first-order matrices with relation witnesses

Boolean relation environments represent exactly the propositional relation
environments. The computable matrix evaluator agrees with SO satisfaction and
with the existing FO evaluator on embedded formulas. Existence of semantic
relation witnesses is equivalent to existence of Boolean tables accepted by the
evaluator, including nullary relations and empty contexts.

This supplies the logical verification interface for Immerman, Proposition 7.6.
`SecondOrder.Certificate` extends it to binary witnesses with exact length
bounds. `SecondOrder.PolynomialTime` gives arithmetic evaluation with the same
verdict and proves its polynomial-time machine bound on encoded tables.
-/

public section

namespace Complexity.DescriptiveComplexity

namespace DecREnv

/-- Converting the empty Boolean environment gives the empty semantic environment. -/
@[simp] theorem toREnv_empty (card : Nat) : (empty card).toREnv = emptyREnv card := by
  funext r args
  exact Fin.elim0 r

/-- Boolean environment extension represents semantic environment extension. -/
@[simp] theorem toREnv_cons {card k : Nat} {rctx : List Nat}
    (S : (Fin k → Fin card) → Bool) (ρ : DecREnv card rctx) :
    (ρ.cons S).toREnv = rCons (fun args => S args = true) ρ.toREnv :=
  toREnv_cons_internal S ρ

/-- Distinct Boolean relation environments have distinct propositional meanings. -/
theorem toREnv_injective (card : Nat) (rctx : List Nat) :
    Function.Injective (toREnv (card := card) (rctx := rctx)) :=
  toREnv_injective_internal card rctx

/-- Every semantic relation environment has a Boolean representation. -/
theorem toREnv_surjective (card : Nat) (rctx : List Nat) :
    Function.Surjective (toREnv (card := card) (rctx := rctx)) :=
  toREnv_surjective_internal card rctx

end DecREnv

namespace SOFormula

variable {V : Vocabulary} {rctx : List Nat} {n : Nat}

/-- Matrix evaluation agrees with satisfaction under the represented relation tables. -/
theorem evalMatrixB_eq_sat (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsFOMatrix) (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    φ.evalMatrixB A h σ ρ = true ↔ φ.Sat A.toFinStruct σ ρ.toREnv :=
  evalMatrixB_eq_sat_internal A φ h σ ρ

/-- Matrix evaluation extends the existing FO evaluator exactly. -/
theorem evalMatrixB_ofFormula (A : DecFinStruct V) (φ : Formula V n)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    (ofFormula φ rctx).evalMatrixB A (ofFormula_isFOMatrix φ rctx) σ ρ =
      Formula.evalB A σ φ := by
  apply Bool.eq_iff_iff.mpr
  exact (evalMatrixB_eq_sat A (ofFormula φ rctx) (ofFormula_isFOMatrix φ rctx) σ ρ).trans
    ((ofFormula_sat A.toFinStruct ρ.toREnv φ σ).trans (Formula.evalB_eq_sat A φ σ).symm)

/-- Checking an FO matrix with supplied Boolean tables is decidable without classical choice. -/
def decidableMatrixSat (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsFOMatrix) (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    Decidable (φ.Sat A.toFinStruct σ ρ.toREnv) :=
  decidable_of_iff _ (evalMatrixB_eq_sat A φ h σ ρ)

/-- Boolean tables are complete existential witnesses for an FO matrix. -/
theorem exists_evalMatrixB_iff (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsFOMatrix) (σ : Env A.card n) :
    (∃ ρ : DecREnv A.card rctx, φ.evalMatrixB A h σ ρ = true) ↔
      ∃ ρ : REnv A.card rctx, φ.Sat A.toFinStruct σ ρ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ.toREnv, (evalMatrixB_eq_sat A φ h σ ρ).mp hρ⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨τ, rfl⟩ := DecREnv.toREnv_surjective A.card rctx ρ
    exact ⟨τ, (evalMatrixB_eq_sat A φ h σ τ).mpr hρ⟩

/-- Universal matrix truth can also be checked over Boolean relation assignments. -/
theorem forall_evalMatrixB_iff (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsFOMatrix) (σ : Env A.card n) :
    (∀ ρ : DecREnv A.card rctx, φ.evalMatrixB A h σ ρ = true) ↔
      ∀ ρ : REnv A.card rctx, φ.Sat A.toFinStruct σ ρ := by
  constructor
  · intro hρ ρ
    obtain ⟨τ, rfl⟩ := DecREnv.toREnv_surjective A.card rctx ρ
    exact (evalMatrixB_eq_sat A φ h σ τ).mp (hρ τ)
  · intro hρ ρ
    exact (evalMatrixB_eq_sat A φ h σ ρ).mpr (hρ ρ.toREnv)

end SOFormula

end Complexity.DescriptiveComplexity

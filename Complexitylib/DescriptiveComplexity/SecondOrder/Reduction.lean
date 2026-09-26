/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Reduction
public import Complexitylib.DescriptiveComplexity.SecondOrder.Isomorphism

/-!
# Second-order transport through first-order interpretations

Pull back second-order formulas along the existing universe-preserving
`FOInterpretation`. Vocabulary atoms are replaced by their defining first-order
formulas; relation variables and their quantifiers retain their arities and scope.
The transport theorem holds for arbitrary open formulas and relation environments.
It preserves both FO matrices and existential second-order prefixes.

This supplies reduction closure for the logical classes before a machine capture
theorem is available. For tagged tuple interpretations, relation variables instead
need blocks of larger-arity variables; that generalization is separate work.

The pullback approach is standard in descriptive complexity; see Immerman,
*Descriptive Complexity* (1999), and Senellart and Gnatenko, *Descriptive Complexity
in Lean: Completeness by First-Order Reductions* (2026), Sections 3.3 and 4.1,
<https://arxiv.org/abs/2609.18261>. These proofs use Complexitylib's own syntax.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

variable {V W : Vocabulary}

/-- Pull back an SO formula along a universe-preserving FO interpretation. -/
def FOInterpretation.translateSO (I : FOInterpretation V W) :
    {rctx : List Nat} → {n : Nat} → SOFormula W rctx n → SOFormula V rctx n
  | rctx, _, .relApp i ts =>
    .ofFormula ((I.relFormula i).subst (fun k => I.translateTerm (ts k))) rctx
  | _, _, .soRelApp r ts => .soRelApp r (fun k => I.translateTerm (ts k))
  | _, _, .eq t₁ t₂ => .eq (I.translateTerm t₁) (I.translateTerm t₂)
  | _, _, .neg φ => .neg (I.translateSO φ)
  | _, _, .conj φ ψ => .conj (I.translateSO φ) (I.translateSO ψ)
  | _, _, .disj φ ψ => .disj (I.translateSO φ) (I.translateSO ψ)
  | _, _, .exist φ => .exist (I.translateSO φ)
  | _, _, .all φ => .all (I.translateSO φ)
  | _, _, .soExist k φ => .soExist k (I.translateSO φ)
  | _, _, .soAll k φ => .soAll k (I.translateSO φ)

/-- SO transport, including open element and relation environments. -/
theorem FOInterpretation.translateSO_sat (I : FOInterpretation V W) (A : FinStruct V)
    {rctx : List Nat} {n : Nat} (φ : SOFormula W rctx n)
    (σ : Env A.card n) (ρ : REnv A.card rctx) :
    φ.Sat (I.apply A) σ ρ ↔ (I.translateSO φ).Sat A σ ρ := by
  induction φ with
  | relApp i ts =>
    simp only [FOInterpretation.translateSO, SOFormula.ofFormula_sat, Formula.subst_sat,
      SOFormula.Sat, FOInterpretation.apply, FOInterpretation.translateTerm_eval]
  | soRelApp r ts =>
    simp only [FOInterpretation.translateSO, SOFormula.Sat, FOInterpretation.translateTerm_eval]
  | eq t₁ t₂ =>
    simp only [FOInterpretation.translateSO, SOFormula.Sat, FOInterpretation.translateTerm_eval]
    rfl
  | neg φ ih => exact not_congr (ih σ ρ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ σ ρ) (ihψ σ ρ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ σ ρ) (ihψ σ ρ)
  | exist φ ih => exact exists_congr fun a => ih (envCons a σ) ρ
  | all φ ih => exact forall_congr' fun a => ih (envCons a σ) ρ
  | soExist k φ ih => exact exists_congr fun S => ih σ (rCons S ρ)
  | soAll k φ ih => exact forall_congr' fun S => ih σ (rCons S ρ)

/-- Pullback preserves and reflects the absence of second-order quantifiers. -/
theorem FOInterpretation.isFOMatrix_translateSO (I : FOInterpretation V W)
    {rctx : List Nat} {n : Nat} (φ : SOFormula W rctx n) :
    (I.translateSO φ).IsFOMatrix ↔ φ.IsFOMatrix := by
  induction φ <;> simp [FOInterpretation.translateSO, SOFormula.IsFOMatrix,
    SOFormula.ofFormula_isFOMatrix, *]

/-- Pullback preserves existential second-order prefix form. -/
theorem FOInterpretation.isExistSO_translateSO (I : FOInterpretation V W)
    {rctx : List Nat} {n : Nat} (φ : SOFormula W rctx n) :
    (I.translateSO φ).IsExistSO ↔ φ.IsExistSO := by
  induction φ <;> simp [FOInterpretation.translateSO, SOFormula.IsExistSO,
    SOFormula.IsFOMatrix, SOFormula.ofFormula_isExistSO,
    FOInterpretation.isFOMatrix_translateSO, *]

/-- Second-order definability is closed under the existing FO reductions. -/
theorem SODefinable.of_reduces {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (hQ₂ : SODefinable Q₂) (hred : FOReduces Q₁ Q₂) : SODefinable Q₁ := by
  obtain ⟨I, hI⟩ := hred
  obtain ⟨φ, hφ⟩ := hQ₂
  refine ⟨I.translateSO φ, fun A => ?_⟩
  exact (hI A).trans ((hφ (I.apply A)).trans (I.translateSO_sat A φ _ _))

end Complexity.DescriptiveComplexity

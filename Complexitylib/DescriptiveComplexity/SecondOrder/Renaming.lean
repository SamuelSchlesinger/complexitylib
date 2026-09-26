/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Renaming.Defs
public import Complexitylib.DescriptiveComplexity.SecondOrder.Renaming.Internal

/-!
# Capture-avoiding relation renaming

Arity-preserving relation renaming preserves satisfaction under the pulled-back
environment, exact syntactic size, FO matrices, and existential SO prefixes.
Identity and composition hold as equalities of formulas. Weakening inserts an
unused relation binder, which is the basic operation for merging SO witnesses.
-/

public section

namespace Complexity.DescriptiveComplexity

namespace RelRenaming

/-- A relation renaming is determined by its map on indices. -/
@[ext] theorem ext {rctx sctx : List Nat} (f g : RelRenaming rctx sctx)
    (h : f.index = g.index) : f = g := relRenaming_ext_internal f g h

/-- Lifting fixes the identity renaming. -/
@[simp] theorem lift_id (rctx : List Nat) (k : Nat) :
    (RelRenaming.id rctx).lift k = RelRenaming.id (k :: rctx) := lift_id_internal rctx k

/-- Lifting commutes with composition. -/
theorem lift_comp {rctx sctx tctx : List Nat} (g : RelRenaming sctx tctx)
    (f : RelRenaming rctx sctx) (k : Nat) :
    (g.comp f).lift k = (g.lift k).comp (f.lift k) := lift_comp_internal g f k

/-- Pulling an environment through the identity does nothing. -/
@[simp] theorem pull_id {card : Nat} {rctx : List Nat} (ρ : REnv card rctx) :
    (RelRenaming.id rctx).pull ρ = ρ := rfl

/-- Pullback reverses the order of composition. -/
theorem pull_comp {rctx sctx tctx : List Nat} (g : RelRenaming sctx tctx)
    (f : RelRenaming rctx sctx) {card : Nat} (ρ : REnv card tctx) :
    (g.comp f).pull ρ = f.pull (g.pull ρ) := rfl

/-- A lifted renaming preserves the freshly bound relation. -/
@[simp] theorem pull_lift_rCons {rctx sctx : List Nat} (f : RelRenaming rctx sctx)
    {card k : Nat} (S : (Fin k → Fin card) → Prop) (ρ : REnv card sctx) :
    (f.lift k).pull (rCons S ρ) = rCons S (f.pull ρ) := pull_lift_internal f S ρ

/-- Weakening ignores the freshly bound relation. -/
@[simp] theorem pull_weaken_rCons {rctx : List Nat} {card k : Nat}
    (S : (Fin k → Fin card) → Prop) (ρ : REnv card rctx) :
    (RelRenaming.weaken rctx k).pull (rCons S ρ) = ρ := pull_weaken_internal S ρ

end RelRenaming

namespace SOFormula

variable {V : Vocabulary} {rctx sctx tctx : List Nat} {n : Nat}

/-- Satisfaction after relation renaming is satisfaction in the pulled-back environment. -/
theorem renameRel_sat (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx)
    (A : FinStruct V) (σ : Env A.card n) (ρ : REnv A.card sctx) :
    (φ.renameRel f).Sat A σ ρ ↔ φ.Sat A σ (f.pull ρ) :=
  renameRel_sat_internal φ f A σ ρ

/-- Inserting an unused relation variable leaves satisfaction unchanged. -/
theorem renameRel_weaken_sat (φ : SOFormula V rctx n) (A : FinStruct V)
    (σ : Env A.card n) (ρ : REnv A.card rctx) {k : Nat}
    (S : (Fin k → Fin A.card) → Prop) :
    (φ.renameRel (RelRenaming.weaken rctx k)).Sat A σ (rCons S ρ) ↔ φ.Sat A σ ρ := by
  rw [renameRel_sat, RelRenaming.pull_weaken_rCons]

/-- Relation renaming leaves the number of syntax nodes unchanged. -/
@[simp] theorem size_renameRel (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).size = φ.size := size_renameRel_internal φ f

/-- Relation renaming preserves and reflects being an FO matrix. -/
@[simp] theorem isFOMatrix_renameRel (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).IsFOMatrix ↔ φ.IsFOMatrix := isFOMatrix_renameRel_internal φ f

/-- Relation renaming preserves and reflects existential SO prefix form. -/
@[simp] theorem isExistSO_renameRel (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).IsExistSO ↔ φ.IsExistSO := isExistSO_renameRel_internal φ f

/-- Identity renaming fixes the formula exactly. -/
@[simp] theorem renameRel_id (φ : SOFormula V rctx n) :
    φ.renameRel (RelRenaming.id rctx) = φ := renameRel_id_internal φ

/-- Successive relation renamings equal their composite. -/
theorem renameRel_comp (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx)
    (g : RelRenaming sctx tctx) :
    (φ.renameRel f).renameRel g = φ.renameRel (g.comp f) := renameRel_comp_internal φ f g

end SOFormula

end Complexity.DescriptiveComplexity

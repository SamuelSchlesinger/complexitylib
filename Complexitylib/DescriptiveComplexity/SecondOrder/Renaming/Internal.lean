/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Renaming.Defs

/-!
# Relation-renaming proofs

Environment pullback commutes with binding a relation. Structural induction then
proves satisfaction, size, and fragment preservation under relation renaming.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem relRenaming_ext_internal {rctx sctx : List Nat} (f g : RelRenaming rctx sctx)
    (h : f.index = g.index) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem lift_id_internal (rctx : List Nat) (k : Nat) :
    (RelRenaming.id rctx).lift k = RelRenaming.id (k :: rctx) := by
  apply relRenaming_ext_internal
  funext r
  cases r using Fin.cases <;> rfl

theorem lift_comp_internal {rctx sctx tctx : List Nat} (g : RelRenaming sctx tctx)
    (f : RelRenaming rctx sctx) (k : Nat) :
    (g.comp f).lift k = (g.lift k).comp (f.lift k) := by
  apply relRenaming_ext_internal
  funext r
  cases r using Fin.cases <;> rfl

theorem pull_lift_internal {rctx sctx : List Nat} (f : RelRenaming rctx sctx)
    {card k : Nat} (S : (Fin k → Fin card) → Prop) (ρ : REnv card sctx) :
    (f.lift k).pull (rCons S ρ) = rCons S (f.pull ρ) := by
  funext r args
  cases r using Fin.cases <;> rfl

theorem pull_weaken_internal {rctx : List Nat} {card k : Nat}
    (S : (Fin k → Fin card) → Prop) (ρ : REnv card rctx) :
    (RelRenaming.weaken rctx k).pull (rCons S ρ) = ρ := rfl

theorem renameRel_sat_internal {V : Vocabulary} {rctx sctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) (A : FinStruct V)
    (σ : Env A.card n) (ρ : REnv A.card sctx) :
    (φ.renameRel f).Sat A σ ρ ↔ φ.Sat A σ (f.pull ρ) := by
  induction φ generalizing sctx with
  | relApp i args => rfl
  | soRelApp r args => rfl
  | eq a b => rfl
  | neg φ ih => exact not_congr (ih f σ ρ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ f σ ρ) (ihψ f σ ρ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ f σ ρ) (ihψ f σ ρ)
  | exist φ ih => exact exists_congr fun a => ih f (envCons a σ) ρ
  | all φ ih => exact forall_congr' fun a => ih f (envCons a σ) ρ
  | soExist k φ ih =>
    simpa only [SOFormula.renameRel, SOFormula.Sat, pull_lift_internal] using
      exists_congr (fun S => ih (f.lift k) σ (rCons S ρ))
  | soAll k φ ih =>
    simpa only [SOFormula.renameRel, SOFormula.Sat, pull_lift_internal] using
      forall_congr' (fun S => ih (f.lift k) σ (rCons S ρ))

theorem size_renameRel_internal {V : Vocabulary} {rctx sctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).size = φ.size := by
  induction φ generalizing sctx <;> simp [SOFormula.renameRel, SOFormula.size, *]

theorem isFOMatrix_renameRel_internal {V : Vocabulary} {rctx sctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).IsFOMatrix ↔ φ.IsFOMatrix := by
  induction φ generalizing sctx <;> simp [SOFormula.renameRel, SOFormula.IsFOMatrix, *]

theorem isExistSO_renameRel_internal {V : Vocabulary} {rctx sctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) :
    (φ.renameRel f).IsExistSO ↔ φ.IsExistSO := by
  induction φ generalizing sctx <;>
    simp [SOFormula.renameRel, SOFormula.IsExistSO, SOFormula.IsFOMatrix,
      isFOMatrix_renameRel_internal, *]

theorem renameRel_id_internal {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) : φ.renameRel (RelRenaming.id rctx) = φ := by
  induction φ <;> first | rfl | simp only [SOFormula.renameRel, lift_id_internal, *]

theorem renameRel_comp_internal {V : Vocabulary} {rctx sctx tctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (f : RelRenaming rctx sctx) (g : RelRenaming sctx tctx) :
    (φ.renameRel f).renameRel g = φ.renameRel (g.comp f) := by
  induction φ generalizing sctx tctx <;>
    first | rfl | simp only [SOFormula.renameRel, lift_comp_internal, *]

end Complexity.DescriptiveComplexity

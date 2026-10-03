/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs

/-!
# Coordinate laws for successive block splitting

The index equivalence puts each first coordinate immediately before its
second coordinate. Splitting a head pair therefore prepends two coordinates
to the split tail, with only the equality of the tuple lengths transported.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem splitBlockIndexEquiv_val {t : Nat} (i : Fin t) (j : Fin 2) :
    (splitBlockIndexEquiv t (i, j)).val = j.val + 2 * i.val := rfl

theorem splitBlockEquiv_apply {α : Type*} {t : Nat} (x : Fin t → α × α)
    (i : Fin t) (j : Fin 2) :
    splitBlockEquiv α t x (splitBlockIndexEquiv t (i, j)) =
      (finTwoArrowEquiv α).symm (x i) j := by
  simp [splitBlockEquiv]

theorem splitBlockEquiv_apply_fst {α : Type*} {t : Nat}
    (x : Fin t → α × α) (i : Fin t) :
    splitBlockEquiv α t x (splitBlockIndexEquiv t (i, 0)) = (x i).1 := by
  simpa using splitBlockEquiv_apply x i 0

theorem splitBlockEquiv_apply_snd {α : Type*} {t : Nat}
    (x : Fin t → α × α) (i : Fin t) :
    splitBlockEquiv α t x (splitBlockIndexEquiv t (i, 1)) = (x i).2 := by
  simpa using splitBlockEquiv_apply x i 1

theorem pairPrependEquiv_apply {α : Type*} {t : Nat} (ab : α × α) (z : Fin t → α) :
    pairPrependEquiv α t (ab, z) = Fin.cons ab.1 (Fin.cons ab.2 z) := rfl

theorem pairPrependEquiv_symm_apply {α : Type*} {t : Nat} (x : Fin (t + 2) → α) :
    (pairPrependEquiv α t).symm x = ((x 0, x 1), Fin.tail (Fin.tail x)) := rfl

theorem splitBlockIndexEquiv_succ_cast {t : Nat} (i : Fin t) (j : Fin 2) :
    Fin.cast (Nat.mul_succ 2 t) (splitBlockIndexEquiv (t + 1) (i.succ, j)) =
      (splitBlockIndexEquiv t (i, j)).succ.succ := by
  apply Fin.ext
  simp only [Fin.val_cast, splitBlockIndexEquiv_val, Fin.val_succ]
  lia

theorem splitBlockEquiv_cons {α : Type*} {t : Nat}
    (ab : α × α) (z : Fin t → α × α) :
    splitBlockEquiv α (t + 1) (Fin.cons ab z) =
      fun i => pairPrependEquiv α (2 * t) (ab, splitBlockEquiv α t z)
        (Fin.cast (Nat.mul_succ 2 t) i) := by
  funext i
  obtain ⟨⟨a, j⟩, rfl⟩ := (splitBlockIndexEquiv (t + 1)).surjective i
  rw [splitBlockEquiv_apply]
  refine Fin.cases ?_ (fun a => ?_) a
  · revert j
    exact Fin.forall_fin_two.mpr ⟨rfl, rfl⟩
  · rw [splitBlockIndexEquiv_succ_cast, pairPrependEquiv_apply]
    simp only [Fin.cons_succ]
    exact (splitBlockEquiv_apply z a j).symm

end Algebraic.Cutwidth.Extractor.Internal

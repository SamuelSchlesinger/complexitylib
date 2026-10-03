/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Tuple identities for shared-seed block condensation

Head/tail transport and the empty tuple case connect the block-source
induction to the finite weighted-output contract. These identities retain
the seed once and require no independence between source blocks.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem blockCondenser_mapWeight_cons {α : Type*} [Fintype α] {t : Nat}
    (w : α → ℝ) (p : α → (Fin t → α) → ℝ) :
    mapWeight (fun az : α × (Fin t → α) => (Fin.cons az.1 az.2 : Fin (t + 1) → α))
      (fun az => w az.1 * p az.1 az.2) =
        fun x : Fin (t + 1) → α => w (x 0) * p (x 0) (Fin.tail x) := by
  funext x
  exact mapWeight_equiv_apply (Fin.consEquiv (fun _ : Fin (t + 1) => α)) _ x

theorem blockCondenser_cons_map {α β : Type*} {t : Nat}
    (f : α → β) (a : α) (z : Fin t → α) :
    (fun i => f ((Fin.cons a z : Fin (t + 1) → α) i)) =
      (Fin.cons (f a) (fun i => f (z i)) : Fin (t + 1) → β) :=
  Fin.comp_cons f a z

theorem blockCondenser_zero {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    (C : α → Seed → Ω) (p : (Fin 0 → α) → ℝ) (hp : IsProbabilityWeight p)
    (K : Nat) :
    ∃ q : Seed → (Fin 0 → Ω) → ℝ,
      (∀ y, IsBlockSource (q y) K) ∧
        weightedSeededOutput p (fun x y i => C (x i) y) = seedFamilyWeight q := by
  refine ⟨fun _ => uniformWeight (Fin 0 → Ω), fun _ => ?_, ?_⟩
  · exact (isBlockSource_zero_iff _ K).mpr (isProbabilityWeight_uniform _)
  · funext yz
    have same (x : Fin 0 → α) : (fun i => C (x i) yz.1) = yz.2 :=
      Subsingleton.elim _ _
    simp only [weightedSeededOutput, mapWeight, same, ite_true, hp.2,
      seedFamilyWeight, uniformWeight]
    simp

end Algebraic.Cutwidth.Extractor.Internal

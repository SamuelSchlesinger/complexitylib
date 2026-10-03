/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Internal.Tuples
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!+# Transport for the multiblock splitting induction

A head/tail factorization identifies both the head marginal and the joint
weight. Splitting such a joint law splits the conditional tails and prepends
the two head coordinates. Equality of tuple lengths preserves block sources.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem splitBlock_source_cast {α : Type*} [Fintype α] {n m K : Nat}
    (h : n = m) (p : (Fin m → α) → ℝ) (source : IsBlockSource p K) :
    IsBlockSource
      (mapWeight (fun (x : Fin m → α) (i : Fin n) => x (Fin.cast h i)) p) K := by
  subst m
  change IsBlockSource (mapWeight id p) K
  rwa [mapWeight_id]

theorem splitBlock_head_eq {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (w : α → ℝ)
    (tail : α → (Fin t → α) → ℝ) (probability : ∀ a, IsProbabilityWeight (tail a))
    (factor : ∀ a z, p (Fin.cons a z) = w a * tail a z) :
    mapWeight (fun x => x 0) p = w := by
  funext a
  rw [mapWeight_blockHead_apply]
  simp_rw [factor]
  rw [← Finset.mul_sum, (probability a).2, mul_one]

theorem splitBlock_mapWeight_of_factor {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (w : α → ℝ) (tail : α → (Fin t → α) → ℝ)
    (factor : ∀ a z, p (Fin.cons a z) = w a * tail a z) :
    mapWeight (fun az : α × (Fin t → α) => (Fin.cons az.1 az.2 : Fin (t + 1) → α))
      (fun az => w az.1 * tail az.1 az.2) = p := by
  funext x
  change mapWeight (Fin.consEquiv (fun _ : Fin (t + 1) => α)) _ x = p x
  rw [mapWeight_equiv_apply]
  change w (x 0) * tail (x 0) (Fin.tail x) = p x
  simpa only [Fin.cons_self_tail] using (factor (x 0) (Fin.tail x)).symm

theorem splitBlock_map_of_factor {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α × α) → ℝ) (w : α × α → ℝ)
    (tail : α × α → (Fin t → α × α) → ℝ)
    (factor : ∀ a z, p (Fin.cons a z) = w a * tail a z) :
    mapWeight (splitBlockEquiv α (t + 1)) p =
      mapWeight
        (fun (x : Fin (2 * t + 2) → α) i => x (Fin.cast (Nat.mul_succ 2 t) i))
        (mapWeight (pairPrependEquiv α (2 * t))
          (fun az => w az.1 * mapWeight (splitBlockEquiv α t) (tail az.1) az.2)) := by
  rw [← splitBlock_mapWeight_of_factor p w tail factor, mapWeight_comp]
  rw [← mapWeight_tagged (fun _ => splitBlockEquiv α t) w tail,
    mapWeight_comp, mapWeight_comp]
  congr 1
  funext az
  exact splitBlockEquiv_cons az.1 az.2

end Algebraic.Cutwidth.Extractor.Internal

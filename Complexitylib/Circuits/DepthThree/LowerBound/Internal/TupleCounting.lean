/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: tuple counting

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TupleCounting.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5

noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

open Finset

/-- Every value occurring in the tuple occurs at least twice. -/
def TupleNoSingleton {Z : Type uDepth1} [DecidableEq Z] {n : ℕ}
    (a : Fin n → Z) : Prop :=
  ∀ z, (univ.filter (fun i => a i = z)).card ≠ 1

theorem tuple_singleton_of_not {Z : Type uDepth2} [DecidableEq Z] {n : ℕ}
    (a : Fin n → Z) (h : ¬ TupleNoSingleton a) :
    ∃ i₀, ∀ i, a i = a i₀ → i = i₀ := by
  classical
  simp only [TupleNoSingleton, not_forall, not_not] at h
  obtain ⟨z, hz⟩ := h
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hz
  have hmem : i₀ ∈ univ.filter (fun i => a i = z) := by
    rw [hi₀]
    exact mem_singleton_self i₀
  have ha₀ : a i₀ = z := (mem_filter.mp hmem).2
  refine ⟨i₀, fun i hi => ?_⟩
  have himem : i ∈ univ.filter (fun j => a j = z) :=
    mem_filter.mpr ⟨mem_univ i, hi.trans ha₀⟩
  rw [hi₀] at himem
  exact mem_singleton.mp himem

theorem tuple_support_card_le_half {Z : Type uDepth3} [DecidableEq Z]
    (h : ℕ) (a : Fin (2 * h) → Z) (hns : TupleNoSingleton a) :
    (univ.image a).card ≤ h := by
  classical
  have hfiber : ∀ z ∈ (univ : Finset (Fin (2 * h))).image a,
      2 ≤ (univ.filter (fun i => a i = z)).card := by
    intro z hz
    obtain ⟨i, hi, hiz⟩ := mem_image.mp hz
    have hpos : 0 < (univ.filter (fun j => a j = z)).card :=
      card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hiz⟩⟩
    have hne := hns z
    omega
  have htwice : 2 * (univ.image a).card ≤ 2 * h := by
    simpa only [card_univ, Fintype.card_fin] using
      (Finset.mul_card_image_le_card (f := a)
        (univ : Finset (Fin (2 * h))) 2 hfiber)
  omega

theorem tuple_factor_through {Z : Type uDepth4} [Nonempty Z] [DecidableEq Z]
    {n h : ℕ} (a : Fin n → Z) (hcard : (univ.image a).card ≤ h) :
    ∃ (f : Fin h → Z) (g : Fin n → Fin h), (fun i => f (g i)) = a := by
  classical
  let s : Finset Z := univ.image a
  have hsize : Fintype.card ↥s ≤ Fintype.card (Fin h) := by
    simpa [s] using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hsize
  let f : Fin h → Z := Function.extend e Subtype.val
    (fun _ => Classical.choice (inferInstance : Nonempty Z))
  let g : Fin n → Fin h := fun i =>
    e ⟨a i, Finset.mem_image_of_mem a (mem_univ i)⟩
  refine ⟨f, g, funext fun i => ?_⟩
  exact e.injective.extend_apply Subtype.val
    (fun _ => Classical.choice (inferInstance : Nonempty Z))
    ⟨a i, Finset.mem_image_of_mem a (mem_univ i)⟩

theorem card_noSingleton_tuples_le {Z : Type uDepth5} [Fintype Z] [Nonempty Z]
    [DecidableEq Z] (h : ℕ) :
    (univ.filter (fun a : Fin (2 * h) → Z => TupleNoSingleton a)).card ≤
      (Fintype.card Z) ^ h * h ^ (2 * h) := by
  classical
  let encode : (Fin h → Z) × (Fin (2 * h) → Fin h) → (Fin (2 * h) → Z) :=
    fun p i => p.1 (p.2 i)
  have hsub : univ.filter (fun a : Fin (2 * h) → Z => TupleNoSingleton a) ⊆
      univ.image encode := by
    intro a ha
    have hns := (mem_filter.mp ha).2
    obtain ⟨f, g, hfg⟩ := tuple_factor_through a (tuple_support_card_le_half h a hns)
    exact mem_image.mpr ⟨(f, g), mem_univ _, hfg⟩
  calc
    _ ≤ (univ.image encode).card := card_le_card hsub
    _ ≤ (univ : Finset ((Fin h → Z) × (Fin (2 * h) → Fin h))).card :=
      card_image_le
    _ = (Fintype.card Z) ^ h * h ^ (2 * h) := by simp

end DepthThreeLowerBound

end

end Complexity

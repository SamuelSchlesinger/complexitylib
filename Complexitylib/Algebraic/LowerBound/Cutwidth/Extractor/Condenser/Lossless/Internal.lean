/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Defs
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Completing the original seeded map to injections

For each seed, retain one original source point per reached output and extend
these assignments to an injection. The resulting witness changes exactly the
number of source and seed pairs lost when forming the full neighbor set.
Test discrepancy is bounded by these changed pairs. The choices construct a
distributional witness, not an algorithm for computing the condenser.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem embedding_agree_on_range {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (capacity : Fintype.card α ≤ Fintype.card β) :
    ∃ g : α ↪ β, ∀ b ∈ Set.range f, ∃ x, f x = b ∧ g x = b := by
  let e : α ↪ β := (Function.Embedding.nonempty_of_card_le capacity).some
  let r : Set.range f → α := Function.surjInv (Set.codRestrict_range_surjective f)
  have hr (b : Set.range f) : f (r b) = b.val :=
    congrArg Subtype.val (Function.rightInverse_surjInv
      (Set.codRestrict_range_surjective f) b)
  have hinj : Function.Injective r :=
    Function.injective_surjInv (Set.codRestrict_range_surjective f)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun b => e (r b)) (fun b : Set.range f => b.val)
    (e.injective.comp hinj) Subtype.val_injective
  refine ⟨e.trans σ.toEmbedding, ?_⟩
  intro b hb
  exact ⟨r ⟨b, hb⟩, hr _, hσ _⟩

theorem exists_seedwise_injection {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (C : α → Seed → Ω) (P : Finset α) (capacity : P.card ≤ Fintype.card Ω) :
    ∃ g : Seed → (P ↪ Ω),
      ((Finset.univ : Finset (P × Seed)).filter
        fun xy => C xy.1.val xy.2 = g xy.2 xy.1).card = (seededNeighborSet C P).card := by
  have cap : Fintype.card P ≤ Fintype.card Ω := by simpa using capacity
  choose g hg using fun y => embedding_agree_on_range (fun x : P => C x.val y) cap
  refine ⟨g, ?_⟩
  let a := (Finset.univ : Finset (P × Seed)).filter
    fun xy => C xy.1.val xy.2 = g xy.2 xy.1
  have image_eq : a.image (fun xy => (xy.2, C xy.1.val xy.2)) =
      seededNeighborSet C P := by
    ext q
    constructor
    · intro hq
      obtain ⟨⟨x, y⟩, _, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_biUnion.mpr ⟨x.val, x.property,
        Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩⟩
    · intro hq
      obtain ⟨x, hx, hq⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨x', hc, hg'⟩ := hg y (C x y) ⟨⟨x, hx⟩, rfl⟩
      refine Finset.mem_image.mpr ⟨(x', y), ?_, Prod.ext rfl hc⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.trans hg'.symm⟩
  have injective : Set.InjOn (fun xy : P × Seed => (xy.2, C xy.1.val xy.2)) a := by
    intro ⟨x, y⟩ hx ⟨x', y'⟩ hx' equal
    have hy : y = y' := congrArg Prod.fst equal
    subst y'
    have xx : x = x' := (g y).injective <|
      (Finset.mem_filter.mp hx).2.symm.trans
        ((congrArg Prod.snd equal).trans (Finset.mem_filter.mp hx').2)
    exact congrArg (fun z : P => (z, y)) xx
  exact (Finset.card_image_of_injOn injective).symm.trans (congrArg Finset.card image_eq)

theorem card_test_sub_le_disagreement {α β : Type*} [Fintype α]
    (f g : α → β) (T : Finset β) :
    |(((Finset.univ : Finset α).filter fun x => f x ∈ T).card : ℝ) -
      ((Finset.univ.filter fun x => g x ∈ T).card : ℝ)| ≤
        ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) := by
  have step (f g : α → β) :
      (Finset.univ.filter fun x => f x ∈ T).card ≤
        (Finset.univ.filter fun x => g x ∈ T).card +
          (Finset.univ.filter fun x => f x ≠ g x).card := by
    apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro x hx
    by_cases h : f x = g x
    · exact Finset.mem_union_left _ <| Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h ▸ (Finset.mem_filter.mp hx).2⟩
    · exact Finset.mem_union_right _ <|
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have upper : (((Finset.univ : Finset α).filter fun x => f x ∈ T).card : ℝ) ≤
      ((Finset.univ.filter fun x => g x ∈ T).card : ℝ) +
        ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) := by
    exact_mod_cast step f g
  have lower : (((Finset.univ : Finset α).filter fun x => g x ∈ T).card : ℝ) ≤
      ((Finset.univ.filter fun x => f x ∈ T).card : ℝ) +
        ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) := by
    exact_mod_cast (by simpa only [ne_comm] using step g f)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem seededTestProb_sub_le_disagreement {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (C G : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    |seededTestProb C T - seededTestProb G T| ≤
      (((Finset.univ : Finset (α × Seed)).filter
        fun xy => C xy.1 xy.2 ≠ G xy.1 xy.2).card : ℝ) /
          ((Fintype.card α : ℝ) * Fintype.card Seed) := by
  unfold seededTestProb
  rw [← sub_div, abs_div, abs_of_nonneg
    (show 0 ≤ (Fintype.card α : ℝ) * Fintype.card Seed by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have result := card_test_sub_le_disagreement
    (fun xy : α × Seed => (xy.2, C xy.1 xy.2))
    (fun xy => (xy.2, G xy.1 xy.2)) T
  convert result using 1
  · congr 2 <;> congr 2 <;> ext xy <;> simp
  · congr 2
    ext xy
    simp

theorem exists_seedwise_injection_of_expansion {α Seed Ω : Type*}
    [Fintype Seed] [Nonempty Seed] [Fintype Ω]
    (C : α → Seed → Ω) (P : Finset α) (nonempty : P.Nonempty)
    (capacity : P.card ≤ Fintype.card Ω) {ε : ℝ}
    (expansion : (1 - ε) * P.card * Fintype.card Seed ≤ (seededNeighborSet C P).card) :
    ∃ g : Seed → (P ↪ Ω), ∀ T : Finset (Seed × Ω),
      |seededTestProb (fun x : P => C x.val) T -
        seededTestProb (fun x y => g y x) T| ≤ ε := by
  obtain ⟨g, hagree⟩ := exists_seedwise_injection C P capacity
  have total := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun xy : P × Seed => C xy.1.val xy.2 = g xy.2 xy.1)
  rw [hagree] at total
  have total_real : ((seededNeighborSet C P).card : ℝ) +
      (((Finset.univ : Finset (P × Seed)).filter
        fun xy => C xy.1.val xy.2 ≠ g xy.2 xy.1).card : ℝ) =
          (P.card : ℝ) * Fintype.card Seed := by
    exact_mod_cast (by simpa only [Finset.card_univ, Fintype.card_prod,
      Fintype.card_coe] using total)
  have disagreement :
      (((Finset.univ : Finset (P × Seed)).filter
        fun xy => C xy.1.val xy.2 ≠ g xy.2 xy.1).card : ℝ) ≤
          ε * P.card * Fintype.card Seed := by
    nlinarith [expansion]
  have source_pos : 0 < Fintype.card P := by simpa using nonempty.card_pos
  have denominator_pos : 0 < (Fintype.card P : ℝ) * Fintype.card Seed := by positivity
  refine ⟨g, fun T => ?_⟩
  apply (seededTestProb_sub_le_disagreement (fun x : P => C x.val)
    (fun x y => g y x) T).trans
  rw [div_le_iff₀ denominator_pos]
  simpa only [Fintype.card_coe, mul_assoc] using disagreement

end Algebraic.Cutwidth.Extractor.Internal

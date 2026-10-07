/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: sunflower

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Sunflower.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

open scoped BigOperators

variable {α : Type uDepth1} [DecidableEq α]

/-- A finite family whose pairwise intersections are its common core. -/
def Sunflower (family : Finset (Finset α)) (core : Finset α) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ≠ B → A ∩ B = core

namespace Sunflower

variable {family : Finset (Finset α)} {core A B : Finset α} {i : ℕ}

theorem mono (h : Sunflower family core) {sub : Finset (Finset α)}
    (hsub : sub ⊆ family) : Sunflower sub core := by
  intro A hA B hB hne
  exact h A (hsub hA) B (hsub hB) hne

theorem core_subset (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (hA : A ∈ family) : core ⊆ A := by
  obtain ⟨B, hB, hBA⟩ : ∃ B ∈ family, B ≠ A := by
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp (by omega : 1 < family.card)
    by_cases hBA : B = A
    · exact ⟨C, hC, fun hCA => hBC (hBA.trans hCA.symm)⟩
    · exact ⟨B, hB, hBA⟩
  rw [← h A hA B hB hBA.symm]
  exact Finset.inter_subset_left

theorem core_card_lt (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) : core.card < i := by
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < family.card)
  by_contra hn
  have hCA : core = A := Finset.eq_of_subset_of_card_le (h.core_subset hcard hA)
    (by rw [uniform A hA]; omega)
  have hCB : core = B := Finset.eq_of_subset_of_card_le (h.core_subset hcard hB)
    (by rw [uniform B hB]; omega)
  exact hAB (hCA.symm.trans hCB)

theorem petal_card (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) (hA : A ∈ family) :
    (A \ core).card = i - core.card := by
  have hcore_inter : core ∩ A = core := by
    ext x
    exact ⟨fun hx => (Finset.mem_inter.mp hx).1,
      fun hx => Finset.mem_inter.mpr ⟨hx, h.core_subset hcard hA hx⟩⟩
  rw [Finset.card_sdiff, hcore_inter, uniform A hA]

theorem petal_nonempty (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) (hA : A ∈ family) :
    (A \ core).Nonempty := by
  apply Finset.card_pos.mp
  rw [h.petal_card hcard uniform hA]
  exact Nat.sub_pos_of_lt (h.core_card_lt hcard uniform)

theorem petal_card_lt (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) (hc : core.Nonempty)
    (hA : A ∈ family) : (A \ core).card < i := by
  rw [h.petal_card hcard uniform hA]
  have hcpos := Finset.card_pos.mpr hc
  have hclt := h.core_card_lt hcard uniform
  omega

theorem petals_disjoint (h : Sunflower family core) (hA : A ∈ family)
    (hB : B ∈ family) (hne : A ≠ B) : Disjoint (A \ core) (B \ core) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨hxA, hxc⟩ := Finset.mem_sdiff.mp hxA
  obtain ⟨hxB, _⟩ := Finset.mem_sdiff.mp hxB
  apply hxc
  rw [← h A hA B hB hne]
  exact Finset.mem_inter.mpr ⟨hxA, hxB⟩

theorem petal_injective (h : Sunflower family core) (hcard : 2 ≤ family.card) :
    Set.InjOn (fun A => A \ core) (↑family : Set (Finset α)) := by
  intro A hA B hB heq
  calc
    A = (A \ core) ∪ core := (Finset.sdiff_union_of_subset (h.core_subset hcard hA)).symm
    _ = (B \ core) ∪ core := congrArg (fun D => D ∪ core) heq
    _ = B := Finset.sdiff_union_of_subset (h.core_subset hcard hB)

theorem card_petals (h : Sunflower family core) (hcard : 2 ≤ family.card) :
    (family.image (fun A => A \ core)).card = family.card :=
  Finset.card_image_of_injOn (h.petal_injective hcard)

end Sunflower

/-- Remove a selected element from the sets that contain it. -/
def eraseContaining (family : Finset (Finset α)) (x : α) :
    Finset (Finset α) :=
  (family.filter (fun A => x ∈ A)).image (fun A => A.erase x)

private theorem eraseContaining_card (family : Finset (Finset α)) (x : α) :
    (eraseContaining family x).card = (family.filter (fun A => x ∈ A)).card := by
  apply Finset.card_image_of_injOn
  intro A hA B hB heq
  have hxA := (Finset.mem_filter.mp hA).2
  have hxB := (Finset.mem_filter.mp hB).2
  calc
    A = insert x (A.erase x) := (Finset.insert_erase hxA).symm
    _ = insert x (B.erase x) := congrArg (insert x) heq
    _ = B := Finset.insert_erase hxB

private theorem eraseContaining_uniform (family : Finset (Finset α)) (x : α)
    (i : ℕ) (uniform : ∀ A ∈ family, A.card = i + 1) :
    ∀ B ∈ eraseContaining family x, B.card = i := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨hA, hxA⟩ := Finset.mem_filter.mp hA
  rw [Finset.card_erase_of_mem hxA, uniform A hA]
  omega

private theorem lift_erased_sunflower (family : Finset (Finset α)) (x : α)
    {sub : Finset (Finset α)} {core : Finset α}
    (hsub : sub ⊆ eraseContaining family x) (hs : Sunflower sub core) :
    ∃ lifted ⊆ family, lifted.card = sub.card ∧ Sunflower lifted (insert x core) := by
  have hrestore : ∀ B ∈ sub, insert x B ∈ family ∧ x ∉ B := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (hsub hB)
    obtain ⟨hA, hxA⟩ := Finset.mem_filter.mp hA
    exact ⟨by simpa only [Finset.insert_erase hxA] using hA, by simp⟩
  refine ⟨sub.image (insert x), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact (hrestore B hB).1
  · apply Finset.card_image_of_injOn
    intro A hA B hB heq
    have he := congrArg (fun D : Finset α => D.erase x) heq
    simpa only [Finset.erase_insert (hrestore A hA).2,
      Finset.erase_insert (hrestore B hB).2] using he
  · intro A hA B hB hne
    obtain ⟨A₁, hA₁, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hB
    have hAB : A₁ ≠ B₁ := fun heq => hne (congrArg (insert x) heq)
    rw [← Finset.insert_inter_distrib, hs A₁ hA₁ B₁ hB₁ hAB]

theorem finite_uniform_sunflower (family : Finset (Finset α)) (s r : ℕ)
    (hr : 2 ≤ r) (uniform : ∀ A ∈ family, A.card = s)
    (large : s.factorial * (r - 1) ^ s < family.card) :
    ∃ sub ⊆ family, sub.card = r ∧ ∃ core, Sunflower sub core := by
  classical
  induction s generalizing family with
  | zero =>
      have hsub : family ⊆ {∅} := by
        intro A hA
        have hzero : A = ∅ := Finset.card_eq_zero.mp (uniform A hA)
        simp only [Finset.mem_singleton, hzero]
      have hsmall : family.card ≤ 1 := by simpa using Finset.card_le_card hsub
      simp only [Nat.factorial_zero, pow_zero, mul_one] at large
      omega
  | succ s ih =>
      let candidates := family.powerset.filter (fun M => Sunflower M (∅ : Finset α))
      have hcandidates : candidates.Nonempty := by
        refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
        intro A hA
        simp at hA
      obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image candidates Finset.card hcandidates
      obtain ⟨hMpow, hMs⟩ := Finset.mem_filter.mp hM
      have hMsub : M ⊆ family := Finset.mem_powerset.mp hMpow
      by_cases hrM : r ≤ M.card
      · obtain ⟨sub, hsub, hcard⟩ := Finset.exists_subset_card_eq hrM
        exact ⟨sub, hsub.trans hMsub, hcard, ∅, hMs.mono hsub⟩
      · have hMcard : M.card ≤ r - 1 := by omega
        let U : Finset α := M.biUnion id
        have hUcard : U.card ≤ (s + 1) * (r - 1) := by
          calc
            U.card ≤ ∑ A ∈ M, A.card := Finset.card_biUnion_le
            _ = ∑ _A ∈ M, (s + 1) := by
              apply Finset.sum_congr rfl
              intro A hA
              exact uniform A (hMsub hA)
            _ = M.card * (s + 1) := by simp
            _ ≤ (r - 1) * (s + 1) := Nat.mul_le_mul_right _ hMcard
            _ = (s + 1) * (r - 1) := Nat.mul_comm _ _
        have hmeet : ∀ A ∈ family, ∃ x, x ∈ A ∧ x ∈ U := by
          intro A hA
          by_contra hnone
          have hAM : A ∉ M := by
            intro hAM
            have hpos : 0 < A.card := by rw [uniform A hA]; omega
            obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
            exact hnone ⟨x, hx, Finset.mem_biUnion.mpr ⟨A, hAM, hx⟩⟩
          have hinter : ∀ B ∈ M, A ∩ B = ∅ := by
            intro B hB
            ext x
            constructor
            · intro hx
              obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
              exact (hnone ⟨x, hxA, Finset.mem_biUnion.mpr ⟨B, hB, hxB⟩⟩).elim
            · simp
          have hinsert : Sunflower (insert A M) (∅ : Finset α) := by
            intro B hB C hC hBC
            rcases Finset.mem_insert.mp hB with rfl | hBM
            · rcases Finset.mem_insert.mp hC with rfl | hCM
              · exact (hBC rfl).elim
              · exact hinter C hCM
            · rcases Finset.mem_insert.mp hC with rfl | hCM
              · simpa only [Finset.inter_comm] using hinter B hBM
              · exact hMs B hBM C hCM hBC
          have hinsertmem : insert A M ∈ candidates := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_powerset.mpr ?_, hinsert⟩
            intro B hB
            rcases Finset.mem_insert.mp hB with rfl | hB
            · exact hA
            · exact hMsub hB
          have hbad := hmax (insert A M) hinsertmem
          simp [hAM] at hbad
        obtain ⟨A₀, hA₀⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) large)
        have hA₀pos : 0 < A₀.card := by rw [uniform A₀ hA₀]; omega
        obtain ⟨x₀, _hx₀⟩ := Finset.card_pos.mp hA₀pos
        let f : Finset α → α := fun A =>
          if h : ∃ x, x ∈ A ∧ x ∈ U then h.choose else x₀
        have hf : ∀ A ∈ family, f A ∈ A ∧ f A ∈ U := by
          intro A hA
          dsimp only [f]
          rw [dite_eq_left (hmeet A hA)]
          exact (hmeet A hA).choose_spec
        have hprod : U.card * (s.factorial * (r - 1) ^ s) < family.card := by
          calc
            U.card * (s.factorial * (r - 1) ^ s) ≤
                ((s + 1) * (r - 1)) * (s.factorial * (r - 1) ^ s) :=
              Nat.mul_le_mul_right _ hUcard
            _ = (s + 1).factorial * (r - 1) ^ (s + 1) := by
              rw [Nat.factorial_succ, pow_succ]
              ring
            _ < family.card := large
        obtain ⟨x, _hxU, hxmany⟩ :=
          Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
            (fun A hA => (hf A hA).2) hprod
        have hfiber : (family.filter (fun A => f A = x)) ⊆
            family.filter (fun A => x ∈ A) := by
          intro A hA
          obtain ⟨hA, hfx⟩ := Finset.mem_filter.mp hA
          exact Finset.mem_filter.mpr ⟨hA, hfx ▸ (hf A hA).1⟩
        have herasedlarge : s.factorial * (r - 1) ^ s < (eraseContaining family x).card := by
          rw [eraseContaining_card]
          exact hxmany.trans_le (Finset.card_le_card hfiber)
        obtain ⟨sub, hsub, hsubcard, core, hs⟩ :=
          ih (eraseContaining family x) (eraseContaining_uniform family x s uniform) herasedlarge
        obtain ⟨lifted, hlifted, hcard, hlifts⟩ := lift_erased_sunflower family x hsub hs
        exact ⟨lifted, hlifted, hcard.trans hsubcard, insert x core, hlifts⟩

theorem no_nonempty_core_sunflower_occurrence_le (family : Finset (Finset α))
    (i r : ℕ) (hr : 2 ≤ r) (uniform : ∀ A ∈ family, A.card = i + 1)
    (hno : ∀ sub ⊆ family, sub.card = r →
      ∀ core, core.Nonempty → ¬ Sunflower sub core) (x : α) :
    (family.filter (fun A => x ∈ A)).card ≤ i.factorial * (r - 1) ^ i := by
  classical
  by_contra hn
  have hlarge : i.factorial * (r - 1) ^ i < (eraseContaining family x).card := by
    rw [eraseContaining_card]
    omega
  obtain ⟨sub, hsub, hcard, core, hs⟩ :=
    finite_uniform_sunflower (eraseContaining family x) i r hr
      (eraseContaining_uniform family x i uniform) hlarge
  obtain ⟨lifted, hlifted, hliftedcard, hlifts⟩ := lift_erased_sunflower family x hsub hs
  exact hno lifted hlifted (hliftedcard.trans hcard) (insert x core)
    (Finset.insert_nonempty x core) hlifts

end DepthThreeLowerBound

end Complexity

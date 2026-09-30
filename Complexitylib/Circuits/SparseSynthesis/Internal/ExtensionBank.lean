/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.Cover
public import Mathlib.Data.Fintype.BigOperators

/-!
# Small banks extending every short partial Boolean specification

A bank of at most `(4 * length + 1) * 2 ^ specified` total bit strings
contains an extension of every assignment on at most `specified` positions.
This is the finite covering step in the classical partial-function synthesis
construction; see Chashkin (2024), Section 2.2.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

theorem card_extensions (length specified : ℕ) (domain : Finset (Fin length))
    (small : domain.card ≤ specified) (values : Fin length → Bool) :
    2 ^ length ≤ 2 ^ specified *
      (Finset.univ.filter fun extension : Fin length → Bool =>
        ∀ i ∈ domain, extension i = values i).card := by
  classical
  let extend : ({i : Fin length // i ∉ domain} → Bool) →
      {extension : Fin length → Bool // ∀ i ∈ domain, extension i = values i} :=
    fun free => ⟨fun i => if h : i ∈ domain then values i else free ⟨i, h⟩,
      fun i hi => by simp [hi]⟩
  have injective : Function.Injective extend := by
    intro left right equal
    funext i
    have hi := congrFun (congrArg Subtype.val equal) i.val
    simpa [extend, i.property] using hi
  have count : 2 ^ Fintype.card {i : Fin length // i ∉ domain} ≤
      (Finset.univ.filter fun extension : Fin length → Bool =>
        ∀ i ∈ domain, extension i = values i).card := by
    simpa [Fintype.card_fun, Fintype.card_subtype] using
      Fintype.card_le_of_injective extend injective
  have cardDomain : domain.card ≤ length := by
    simpa using domain.card_le_univ
  have split : domain.card + Fintype.card {i : Fin length // i ∉ domain} = length := by
    simp only [Fintype.card_subtype_compl, Fintype.card_fin]
    have : Fintype.card {i : Fin length // i ∈ domain} = domain.card :=
      Fintype.card_coe domain
    rw [this]
    omega
  calc
    2 ^ length = 2 ^ domain.card * 2 ^ Fintype.card {i : Fin length // i ∉ domain} := by
      rw [← pow_add, split]
    _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) small) count

theorem exists_extension_bank (length specified : ℕ) :
    ∃ bank : Finset (Fin length → Bool), bank.card ≤ (4 * length + 1) * 2 ^ specified ∧
      ∀ (domain : Finset (Fin length)), domain.card ≤ specified →
        ∀ values : Fin length → Bool, ∃ extension ∈ bank,
          ∀ i ∈ domain, extension i = values i := by
  classical
  let targets : Finset (Finset (Fin length) × (Fin length → Bool)) :=
    Finset.univ.filter fun target => target.1.card ≤ specified
  let covers (extension : Fin length → Bool)
      (target : Finset (Fin length) × (Fin length → Bool)) : Prop :=
    ∀ i ∈ target.1, extension i = target.2 i
  have bound : targets.card ≤ 4 ^ length := by
    calc
      targets.card ≤ Fintype.card (Finset (Fin length) × (Fin length → Bool)) :=
        targets.card_le_univ
      _ = 4 ^ length := by simp [← mul_pow]
  have dense (target) (ht : target ∈ targets) :
      Fintype.card (Fin length → Bool) ≤ 2 ^ specified *
        (Finset.univ.filter fun extension => covers extension target).card := by
    simpa [covers] using card_extensions length specified target.1
      (Finset.mem_filter.mp ht).2 target.2
  obtain ⟨bank, hcard, covered⟩ := exists_cover targets covers (2 ^ specified) length
    (by positivity) bound dense
  refine ⟨bank, hcard, fun domain small values => ?_⟩
  exact covered (domain, values) (by simp [targets, small])

end Complexity.CircuitSparseSynthesis.Internal

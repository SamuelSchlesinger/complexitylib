/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.RandomRestriction.Defs
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite random restrictions -- proof internals
-/


public section

namespace Complexity
namespace RandomRestriction

theorem card_seed_internal (N q : ℕ) :
    Fintype.card (Seed N q) = (2 * q + 1) ^ N := by
  simp [Seed, Symbol]
  congr 1
  omega

theorem card_decodeSymbol_none_internal (q : ℕ) :
    (Finset.univ.filter fun symbol : Symbol q =>
      decodeSymbol symbol = none).card = 1 := by
  have hset :
      Finset.univ.filter (fun symbol : Symbol q =>
        decodeSymbol symbol = none) = {Sum.inl ()} := by
    ext symbol
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    cases symbol with
    | inl freeValue =>
        cases freeValue
        simp [decodeSymbol]
    | inr pair =>
        rcases pair with ⟨copy, value⟩
        simp [decodeSymbol]
  rw [hset]
  simp

private noncomputable def coordinateFreeEquiv (index : Fin N) :
    {seed : Seed N q // decode seed index = none} ≃
      {symbol : Symbol q // decodeSymbol symbol = none} ×
        ({other : Fin N // other ≠ index} → Symbol q) where
  toFun seed :=
    (⟨seed.1 index, seed.2⟩, fun other => seed.1 other)
  invFun data :=
    ⟨(Equiv.piSplitAt index (fun _ : Fin N => Symbol q)).symm
        (data.1.1, data.2), by
      simpa [decode] using data.1.2⟩
  left_inv seed := by
    apply Subtype.ext
    apply (Equiv.piSplitAt index
      (fun _ : Fin N => Symbol q)).injective
    simp
  right_inv data := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · funext other
      simp [other.property]

/-- Exactly `(2q + 1)^(N - 1)` seeds leave one prescribed coordinate
free. -/
theorem eventCount_coordinate_free_internal (q : ℕ)
    (index : Fin N) :
    eventCount (q := q) (fun restriction =>
      restriction index = none) =
      (2 * q + 1) ^ (N - 1) := by
  unfold eventCount
  calc
    (Finset.univ.filter fun seed : Seed N q =>
        decode seed index = none).card =
      Fintype.card {seed : Seed N q //
        decode seed index = none} := by
          rw [Fintype.card_subtype]
    _ = Fintype.card
        ({symbol : Symbol q // decodeSymbol symbol = none} ×
          ({other : Fin N // other ≠ index} → Symbol q)) :=
      Fintype.card_congr (coordinateFreeEquiv index)
    _ = Fintype.card
          {symbol : Symbol q // decodeSymbol symbol = none} *
        Fintype.card
          ({other : Fin N // other ≠ index} → Symbol q) := by
            rw [Fintype.card_prod]
    _ = 1 * (2 * q + 1) ^ (N - 1) := by
      congr 1
      · rw [Fintype.card_subtype]
        exact card_decodeSymbol_none_internal q
      · rw [Fintype.card_fun]
        congr 1
        · simp only [Fintype.card_sum, Fintype.card_unit,
            Fintype.card_prod, Fintype.card_fin,
            Fintype.card_bool]
          omega
        · have hcard := Fintype.card_subtype_compl
              (fun other : Fin N => other = index)
          simpa only [Fintype.card_fin,
            Fintype.card_subtype_eq] using hcard
    _ = _ := by simp

theorem card_decodeSymbol_some_internal (q : ℕ) (value : Bool) :
    (Finset.univ.filter fun symbol : Symbol q =>
      decodeSymbol symbol = some value).card = q := by
  let embed : Fin q → Symbol q :=
    fun copy => Sum.inr (copy, value)
  have hinjective : Function.Injective embed := by
    intro left right equality
    simpa [embed] using equality
  have hset :
      Finset.univ.filter (fun symbol : Symbol q =>
        decodeSymbol symbol = some value) =
        Finset.univ.image embed := by
    ext symbol
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    cases symbol with
    | inl freeValue =>
        cases freeValue
        simp [decodeSymbol, embed]
    | inr pair =>
        rcases pair with ⟨copy, actual⟩
        cases actual <;> cases value <;>
          simp [decodeSymbol, embed]
  rw [hset, Finset.card_image_of_injective Finset.univ hinjective]
  simp

theorem decodeSymbol_eq_none_iff_internal (symbol : Symbol q) :
    decodeSymbol symbol = none ↔ symbol = .inl () := by
  cases symbol with
  | inl free =>
      cases free
      simp [decodeSymbol]
  | inr fixed =>
      rcases fixed with ⟨copy, value⟩
      simp [decodeSymbol]

theorem eventCount_le_internal
    (event : Restriction.On N → Prop) [DecidablePred event] :
    eventCount (q := q) event ≤ (2 * q + 1) ^ N := by
  rw [← card_seed_internal N q]
  exact Finset.card_le_univ _

theorem eventCount_true_internal (N q : ℕ) :
    eventCount (N := N) (q := q) (fun _ => True) =
      (2 * q + 1) ^ N := by
  simp only [eventCount, Finset.filter_true, Finset.card_univ]
  exact card_seed_internal N q

theorem eventCount_congr_internal
    (left right : Restriction.On N → Prop)
    [DecidablePred left] [DecidablePred right]
    (hiff :
      ∀ restriction, left restriction ↔ right restriction) :
    eventCount (q := q) left =
      eventCount (q := q) right := by
  unfold eventCount
  congr 1
  ext seed
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hiff (decode seed)

theorem eventCount_mono_internal
    (left right : Restriction.On N → Prop)
    [DecidablePred left] [DecidablePred right]
    (himp :
      ∀ restriction, left restriction → right restriction) :
    eventCount (q := q) left ≤
      eventCount (q := q) right := by
  unfold eventCount
  apply Finset.card_le_card
  intro seed hseed
  simp only [Finset.mem_filter, Finset.mem_univ,
    true_and] at hseed ⊢
  exact himp (decode seed) hseed

theorem eventCount_or_le_add_internal
    (left right : Restriction.On N → Prop)
    [DecidablePred left] [DecidablePred right] :
    eventCount (q := q) (fun restriction =>
        left restriction ∨ right restriction) ≤
      eventCount (q := q) left +
        eventCount (q := q) right := by
  unfold eventCount
  let allSeeds : Finset (Seed N q) := Finset.univ
  let leftSeeds :=
    allSeeds.filter fun seed => left (decode seed)
  let rightSeeds :=
    allSeeds.filter fun seed => right (decode seed)
  have heq :
      allSeeds.filter (fun seed =>
        left (decode seed) ∨ right (decode seed)) =
        leftSeeds ∪ rightSeeds := by
    ext seed
    simp [leftSeeds, rightSeeds, allSeeds]
  rw [heq]
  exact Finset.card_union_le leftSeeds rightSeeds

theorem eventCount_exists_le_sum_internal
    {ι : Type} [Fintype ι]
    (event : ι → Restriction.On N → Prop)
    [∀ index, DecidablePred (event index)] :
    eventCount (q := q) (fun restriction =>
        ∃ index, event index restriction) ≤
      ∑ index, eventCount (q := q) (event index) := by
  classical
  unfold eventCount
  let allSeeds : Finset (Seed N q) := Finset.univ
  let eventSeeds (index : ι) :=
    allSeeds.filter fun seed => event index (decode seed)
  have heq :
      allSeeds.filter (fun seed =>
        ∃ index, event index (decode seed)) =
        Finset.univ.biUnion eventSeeds := by
    ext seed
    simp [eventSeeds, allSeeds]
  rw [heq]
  simpa [eventSeeds, allSeeds] using
    (Finset.card_biUnion_le
      (s := (Finset.univ : Finset ι))
      (t := eventSeeds))

theorem card_eventSeed_internal
    (event : Restriction.On N → Prop) [DecidablePred event] :
    Fintype.card (EventSeed N q event) =
      eventCount (q := q) event := by
  exact Fintype.card_subtype _

private def fixedSymbolEquiv (q : ℕ) :
    {symbol : Symbol q // decodeSymbol symbol ≠ none} ≃
      (Fin q × Bool) where
  toFun symbol :=
    match h : symbol.1 with
    | .inl free =>
        False.elim
          (symbol.2 (by cases free; simp [h, decodeSymbol]))
    | .inr fixed => fixed
  invFun fixed :=
    ⟨.inr fixed, by simp [decodeSymbol]⟩
  left_inv symbol := by
    rcases symbol with ⟨symbol, hfixed⟩
    cases symbol with
    | inl free =>
        exact False.elim
          (hfixed (by cases free; rfl))
    | inr fixed => rfl
  right_inv fixed := rfl

private def fixedSeedEquiv (N q : ℕ) :
    {seed : Seed N q //
      ∀ index, decodeSymbol (seed index) ≠ none} ≃
      (Fin N → Fin q × Bool) :=
  Equiv.subtypePiEquivPi.trans
    (Equiv.piCongrRight fun _ => fixedSymbolEquiv q)

private def emptyFreeSeedEquiv (N q : ℕ) :
    EventSeed N q (fun restriction =>
      restriction.freeVariables = ∅) ≃
      {seed : Seed N q //
        ∀ index, decodeSymbol (seed index) ≠ none} :=
  Equiv.subtypeEquiv (Equiv.refl _) fun seed => by
    change (decode seed).freeVariables = ∅ ↔
      ∀ index, decodeSymbol (seed index) ≠ none
    constructor
    · intro hempty index hnone
      have hmem :
          index ∈ (decode seed).freeVariables := by
        rw [Restriction.On.mem_freeVariables]
        exact hnone
      rw [hempty] at hmem
      simp at hmem
    · intro hfixed
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨index, hmem⟩
      exact hfixed index
        ((Restriction.On.mem_freeVariables _ _).mp hmem)

private theorem card_fixedSeed_internal (N q : ℕ) :
    Fintype.card {seed : Seed N q //
      ∀ index, decodeSymbol (seed index) ≠ none} =
      (2 * q) ^ N := by
  rw [Fintype.card_congr (fixedSeedEquiv N q)]
  simp
  congr 1
  omega

theorem eventCount_freeVariables_empty_internal (N q : ℕ) :
    eventCount (N := N) (q := q) (fun restriction =>
      restriction.freeVariables = ∅) =
      (2 * q) ^ N := by
  rw [← card_eventSeed_internal]
  exact
    (Fintype.card_congr (emptyFreeSeedEquiv N q)).trans
      (card_fixedSeed_internal N q)

theorem eventCount_freeVariables_nonempty_internal (N q : ℕ) :
    eventCount (N := N) (q := q) (fun restriction =>
      restriction.freeVariables.Nonempty) =
      (2 * q + 1) ^ N - (2 * q) ^ N := by
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Seed N q)))
      (fun seed => (decode seed).freeVariables.Nonempty)
  have hneg :
      eventCount (N := N) (q := q) (fun restriction =>
        ¬restriction.freeVariables.Nonempty) =
        (2 * q) ^ N := by
    rw [eventCount_congr_internal
      (fun restriction : Restriction.On N =>
        ¬restriction.freeVariables.Nonempty)
      (fun restriction => restriction.freeVariables = ∅)
      (by intro restriction; simp),
      eventCount_freeVariables_empty_internal]
  change
    eventCount (N := N) (q := q) (fun restriction =>
        restriction.freeVariables.Nonempty) +
      eventCount (N := N) (q := q) (fun restriction =>
        ¬restriction.freeVariables.Nonempty) =
      Fintype.card (Seed N q) at hpartition
  rw [hneg, card_seed_internal] at hpartition
  exact Nat.eq_sub_of_add_eq hpartition

theorem eventCount_one_le_freeVariables_internal (N q : ℕ) :
    eventCount (N := N) (q := q) (fun restriction =>
      1 ≤ restriction.freeVariables.card) =
      (2 * q + 1) ^ N - (2 * q) ^ N := by
  rw [eventCount_congr_internal
    (fun restriction : Restriction.On N =>
      1 ≤ restriction.freeVariables.card)
    (fun restriction =>
      restriction.freeVariables.Nonempty)
    (by intro restriction; exact Finset.one_le_card),
    eventCount_freeVariables_nonempty_internal]

theorem eventCount_mul_pow_le_of_encoding_internal
    (event : Restriction.On N → Prop) [DecidablePred event]
    (queryCount : ℕ) (Code : Type) [Fintype Code]
    (encode :
      EventSeed N q event × (Fin queryCount → Fin q) →
        Seed N q × Code)
    (injective : Function.Injective encode) :
    eventCount (q := q) event * q ^ queryCount ≤
      (2 * q + 1) ^ N * Fintype.card Code := by
  have hcard := Fintype.card_le_of_injective encode injective
  have hsymbol : Fintype.card (Symbol q) = 2 * q + 1 := by
    simp [Symbol]
    omega
  simpa only [Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, card_eventSeed_internal,
    hsymbol] using hcard

theorem positionOf_apply_internal
    (queries : Fin s ↪ Fin N) (position : Fin s) :
    positionOf queries (queries position) = some position := by
  unfold positionOf
  split
  · rename_i hexists
    congr 1
    apply queries.injective
    exact Classical.choose_spec hexists
  · rename_i hmissing
    exact False.elim (hmissing ⟨position, rfl⟩)

theorem positionOf_eq_some_internal
    (queries : Fin s ↪ Fin N) (index : Fin N)
    (position : Fin s)
    (hposition : positionOf queries index = some position) :
    queries position = index := by
  unfold positionOf at hposition
  split at hposition
  · rename_i hexists
    have hchosen := Classical.choose_spec hexists
    have heq : Classical.choose hexists = position :=
      Option.some.inj hposition
    rw [← heq]
    exact hchosen
  · simp at hposition

theorem assignmentAlong_disjoint_internal
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (values : Fin s → Bool)
    (free :
      ∀ position, decode seed (queries position) = none) :
    ∀ index,
      assignmentAlong queries values index = none ∨
        decode seed index = none := by
  intro index
  unfold assignmentAlong
  cases hposition : positionOf queries index with
  | none => simp
  | some position =>
      right
      rw [← positionOf_eq_some_internal
        queries index position hposition]
      exact free position

theorem assignmentAlong_apply_internal
    (queries : Fin s ↪ Fin N) (values : Fin s → Bool)
    (position : Fin s) :
    assignmentAlong queries values (queries position) =
      some (values position) := by
  simp [assignmentAlong, positionOf_apply_internal]

theorem decode_fixAlong_internal
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (copies : Fin s → Fin q) (values : Fin s → Bool) :
    decode (fixAlong seed queries copies values) =
      Restriction.On.comp (assignmentAlong queries values)
        (decode seed) := by
  funext index
  unfold decode fixAlong assignmentAlong
  cases hposition : positionOf queries index with
  | none =>
      simp [Restriction.On.comp, hposition]
  | some position =>
      simp [Restriction.On.comp, hposition, decodeSymbol]

theorem fixAlong_apply_internal
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (copies : Fin s → Fin q) (values : Fin s → Bool)
    (position : Fin s) :
    fixAlong seed queries copies values (queries position) =
      .inr (copies position, values position) := by
  simp [fixAlong, positionOf_apply_internal]

theorem freeAlong_apply_internal
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (position : Fin s) :
    freeAlong seed queries (queries position) = .inl () := by
  simp [freeAlong, positionOf_apply_internal]

theorem freeAlong_fixAlong_internal
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (copies : Fin s → Fin q) (values : Fin s → Bool)
    (free : ∀ position, seed (queries position) = .inl ()) :
    freeAlong (fixAlong seed queries copies values) queries =
      seed := by
  funext index
  cases hposition : positionOf queries index with
  | none =>
      simp [freeAlong, fixAlong, hposition]
  | some position =>
      simp only [freeAlong, hposition]
      have hquery := positionOf_eq_some_internal
        queries index position hposition
      rw [← hquery]
      exact (free position).symm

theorem fixAlong_seed_copies_injective_internal
    (queries : Fin s ↪ Fin N) (values : Fin s → Bool) :
    Function.Injective fun pair :
        {seed : Seed N q //
          ∀ position, seed (queries position) = .inl ()} ×
          (Fin s → Fin q) =>
      fixAlong pair.1.1 queries pair.2 values := by
  intro left right hequal
  rcases left with ⟨⟨leftSeed, leftFree⟩, leftCopies⟩
  rcases right with ⟨⟨rightSeed, rightFree⟩, rightCopies⟩
  change fixAlong leftSeed queries leftCopies values =
    fixAlong rightSeed queries rightCopies values at hequal
  have hseed : leftSeed = rightSeed := by
    simpa only [
      freeAlong_fixAlong_internal leftSeed queries leftCopies values leftFree,
      freeAlong_fixAlong_internal rightSeed queries rightCopies values rightFree
    ] using congrArg (fun target => freeAlong target queries) hequal
  subst rightSeed
  have hcopies : leftCopies = rightCopies := by
    funext position
    have happly := congrArg (fun target => target (queries position)) hequal
    simp only [fixAlong_apply_internal] at happly
    exact congrArg Prod.fst (Sum.inr.inj happly)
  subst rightCopies
  rfl

theorem mem_freeVariables_internal (seed : Seed N q)
    (index : Fin N) :
    index ∈ freeVariables seed ↔ decode seed index = none := by
  simp [freeVariables]

end RandomRestriction
end Complexity

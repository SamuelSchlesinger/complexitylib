/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.RandomRestriction.Defs
public import Complexitylib.Circuits.RandomRestriction.Internal

/-!
# Finite random restrictions

`RandomRestriction.Seed N q` is an exact finite product distribution. Each
coordinate has one free symbol and `q` copies of each fixed Boolean value, so:

* the sample space has `(2 * q + 1) ^ N` equiprobable seeds;
* exactly one coordinate symbol decodes to `none`; and
* exactly `q` symbols decode to each fixed value.

Thus the free-coordinate probability is exactly `1 / (2 * q + 1)`. The API is
stated in cardinality form so later switching arguments do not depend on
rounding or division conventions.
-/

@[expose] public section

namespace Complexity
namespace RandomRestriction

/-- The exact cardinality of the sparse-restriction sample space. -/
theorem card_seed (N q : ℕ) :
    Fintype.card (Seed N q) = (2 * q + 1) ^ N :=
  card_seed_internal N q

/-- There is exactly one free symbol at each coordinate. -/
theorem card_decodeSymbol_none (q : ℕ) :
    (Finset.univ.filter fun symbol : Symbol q =>
      decodeSymbol symbol = none).card = 1 :=
  card_decodeSymbol_none_internal q

/-- Exactly `(2q + 1)^(N - 1)` seeds leave one prescribed input coordinate
free. -/
theorem eventCount_coordinate_free (q : ℕ) (index : Fin N) :
    eventCount (q := q) (fun restriction =>
      restriction index = none) =
      (2 * q + 1) ^ (N - 1) :=
  eventCount_coordinate_free_internal q index

/-- Each fixed Boolean value has exactly `q` equiprobable symbols. -/
theorem card_decodeSymbol_some (q : ℕ) (value : Bool) :
    (Finset.univ.filter fun symbol : Symbol q =>
      decodeSymbol symbol = some value).card = q :=
  card_decodeSymbol_some_internal q value

/-- A coordinate is free exactly when its seed symbol is the distinguished
left-summand value. -/
theorem decodeSymbol_eq_none_iff (symbol : Symbol q) :
    decodeSymbol symbol = none ↔ symbol = .inl () :=
  decodeSymbol_eq_none_iff_internal symbol

/-- Every event count is bounded by the total number of seeds. -/
theorem eventCount_le
    (event : Restriction.On N → Prop) [DecidablePred event] :
    eventCount (q := q) event ≤ (2 * q + 1) ^ N :=
  eventCount_le_internal event

/-- The certain event has the full sample-space cardinality. -/
theorem eventCount_true (N q : ℕ) :
    eventCount (N := N) (q := q) (fun _ => True) =
      (2 * q + 1) ^ N :=
  eventCount_true_internal N q

/-- Extensionally equal restriction events have equal counts. -/
theorem eventCount_congr
    (left right : Restriction.On N → Prop)
    [DecidablePred left] [DecidablePred right]
    (hiff :
      ∀ restriction, left restriction ↔ right restriction) :
    eventCount (q := q) left =
      eventCount (q := q) right :=
  eventCount_congr_internal left right hiff

/-- Inclusion of finite restriction events implies monotonicity of their
counts. -/
theorem eventCount_mono
    (left right : Restriction.On N → Prop)
    [DecidablePred left] [DecidablePred right]
    (himp :
      ∀ restriction, left restriction → right restriction) :
    eventCount (q := q) left ≤
      eventCount (q := q) right :=
  eventCount_mono_internal left right himp

/-- The count of a union of two restriction events is at most the sum of
their counts. -/
theorem eventCount_or_le_add
    (left right : Restriction.On N → Prop)
    [DecidablePred left] [DecidablePred right] :
    eventCount (q := q) (fun restriction =>
        left restriction ∨ right restriction) ≤
      eventCount (q := q) left +
        eventCount (q := q) right :=
  eventCount_or_le_add_internal left right

/-- Finite union bound for restriction events, stated directly in exact
cardinality form. -/
theorem eventCount_exists_le_sum
    {ι : Type} [Fintype ι]
    (event : ι → Restriction.On N → Prop)
    [∀ index, DecidablePred (event index)] :
    eventCount (q := q) (fun restriction =>
        ∃ index, event index restriction) ≤
      ∑ index, eventCount (q := q) (event index) :=
  eventCount_exists_le_sum_internal event

/-- The event-seed subtype has exactly the event count as its cardinality. -/
theorem card_eventSeed
    (event : Restriction.On N → Prop) [DecidablePred event] :
    Fintype.card (EventSeed N q event) =
      eventCount (q := q) event :=
  card_eventSeed_internal event

/-- Exactly `(2 * q) ^ N` seeds fix every input coordinate. -/
theorem eventCount_freeVariables_empty (N q : ℕ) :
    eventCount (N := N) (q := q) (fun restriction =>
      restriction.freeVariables = ∅) =
      (2 * q) ^ N :=
  eventCount_freeVariables_empty_internal N q

/-- The number of seeds leaving at least one coordinate free is the total
sample-space size minus the number of all-fixed seeds. -/
theorem eventCount_freeVariables_nonempty (N q : ℕ) :
    eventCount (N := N) (q := q) (fun restriction =>
      restriction.freeVariables.Nonempty) =
      (2 * q + 1) ^ N - (2 * q) ^ N :=
  eventCount_freeVariables_nonempty_internal N q

/-- Cardinality form of the exact probability that at least one coordinate
survives the sparse restriction. -/
theorem eventCount_one_le_freeVariables (N q : ℕ) :
    eventCount (N := N) (q := q) (fun restriction =>
      1 ≤ restriction.freeVariables.card) =
      (2 * q + 1) ^ N - (2 * q) ^ N :=
  eventCount_one_le_freeVariables_internal N q

/-- Generic finite encoding bound used by switching arguments.

An injection that assigns every bad seed and every `queryCount`-tuple of
`q` copy labels to an arbitrary seed plus a finite auxiliary code proves the
displayed amplified counting inequality. No probability division or
positivity side condition is hidden in the statement. -/
theorem eventCount_mul_pow_le_of_encoding
    (event : Restriction.On N → Prop) [DecidablePred event]
    (queryCount : ℕ) (Code : Type) [Fintype Code]
    (encode :
      EventSeed N q event × (Fin queryCount → Fin q) →
        Seed N q × Code)
    (injective : Function.Injective encode) :
    eventCount (q := q) event * q ^ queryCount ≤
      (2 * q + 1) ^ N * Fintype.card Code :=
  eventCount_mul_pow_le_of_encoding_internal
    event queryCount Code encode injective

/-- Looking up an embedded coordinate recovers its unique position. -/
theorem positionOf_apply
    (queries : Fin s ↪ Fin N) (position : Fin s) :
    positionOf queries (queries position) = some position :=
  positionOf_apply_internal queries position

/-- The assignment supported on `queries` is disjoint from any restriction
under which every queried coordinate is free. -/
theorem assignmentAlong_disjoint
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (values : Fin s → Bool)
    (free :
      ∀ position, decode seed (queries position) = none) :
    ∀ index,
      assignmentAlong queries values index = none ∨
        decode seed index = none :=
  assignmentAlong_disjoint_internal seed queries values free

/-- The partial assignment supported on `queries` has the prescribed value
at every selected coordinate. -/
@[simp] theorem assignmentAlong_apply
    (queries : Fin s ↪ Fin N) (values : Fin s → Bool)
    (position : Fin s) :
    assignmentAlong queries values (queries position) =
      some (values position) :=
  assignmentAlong_apply_internal queries values position

/-- Fixing selected seed coordinates composes the decoded restriction with
the corresponding finite partial assignment. -/
theorem decode_fixAlong
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (copies : Fin s → Fin q) (values : Fin s → Bool) :
    decode (fixAlong seed queries copies values) =
      Restriction.On.comp (assignmentAlong queries values)
        (decode seed) :=
  decode_fixAlong_internal seed queries copies values

@[simp] theorem fixAlong_apply
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (copies : Fin s → Fin q) (values : Fin s → Bool)
    (position : Fin s) :
    fixAlong seed queries copies values (queries position) =
      .inr (copies position, values position) :=
  fixAlong_apply_internal seed queries copies values position

@[simp] theorem freeAlong_apply
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (position : Fin s) :
    freeAlong seed queries (queries position) = .inl () :=
  freeAlong_apply_internal seed queries position

/-- Fixing formerly-free embedded coordinates and then freeing them recovers
the original seed. -/
theorem freeAlong_fixAlong
    (seed : Seed N q) (queries : Fin s ↪ Fin N)
    (copies : Fin s → Fin q) (values : Fin s → Bool)
    (free : ∀ position, seed (queries position) = .inl ()) :
    freeAlong (fixAlong seed queries copies values) queries =
      seed :=
  freeAlong_fixAlong_internal seed queries copies values free

@[simp] theorem mem_freeVariables (seed : Seed N q)
    (index : Fin N) :
    index ∈ freeVariables seed ↔ decode seed index = none :=
  mem_freeVariables_internal seed index

end RandomRestriction
end Complexity

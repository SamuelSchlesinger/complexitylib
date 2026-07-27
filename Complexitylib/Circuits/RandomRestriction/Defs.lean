/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Restriction
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

/-!
# Finite random restrictions

This file defines a completely finite sample space for sparse restrictions on
exactly `N` variables. A symbol is either:

* one distinguished free symbol; or
* a Boolean value together with one of `q` copies.

Uniform sampling from `Symbol q` therefore leaves a coordinate free with
probability `1 / (2 * q + 1)` and fixes it to either Boolean value with
probability `q / (2 * q + 1)`. Retaining the copy label makes the distribution
uniform on an honest finite type; no measure-theoretic or rational-probability
convention is hidden in later counting arguments.
-/

@[expose] public section

namespace Complexity
namespace RandomRestriction

/-- One coordinate of the sparse-restriction sample space.

The left summand is the unique free symbol. The right summand fixes the
coordinate and records one of `q` equiprobable copies of the chosen bit. -/
abbrev Symbol (q : ℕ) := Unit ⊕ (Fin q × Bool)

/-- An independent sparse-restriction seed on exactly `N` variables. -/
abbrev Seed (N q : ℕ) := Fin N → Symbol q

/-- Forget the multiplicity label and interpret a sample symbol as a partial
Boolean assignment. -/
def decodeSymbol : Symbol q → Option Bool
  | .inl _ => none
  | .inr (_, value) => some value

/-- Decode a finite seed to the corresponding finite-arity restriction. -/
def decode (seed : Seed N q) : Restriction.On N :=
  fun index => decodeSymbol (seed index)

/-- The set of coordinates left free by a seed. -/
def freeVariables (seed : Seed N q) : Finset (Fin N) :=
  (decode seed).freeVariables

/-- The exact number of seeds whose decoded restriction satisfies `event`. -/
def eventCount (q : ℕ) (event : Restriction.On N → Prop)
    [DecidablePred event] : ℕ :=
  (Finset.univ.filter fun seed : Seed N q => event (decode seed)).card

/-- Seeds whose decoded restriction satisfies `event`. This subtype is the
domain used by injective finite-encoding arguments. -/
abbrev EventSeed (N q : ℕ)
    (event : Restriction.On N → Prop) :=
  {seed : Seed N q // event (decode seed)}

/-- Locate an input coordinate in the range of an embedding. -/
noncomputable def positionOf (queries : Fin s ↪ Fin N)
    (index : Fin N) : Option (Fin s) :=
  if h : ∃ position, queries position = index then
    some (Classical.choose h)
  else
    none

/-- The finite partial assignment induced by embedded coordinates and their
Boolean values. -/
noncomputable def assignmentAlong (queries : Fin s ↪ Fin N)
    (values : Fin s → Bool) : Restriction.On N :=
  fun index => (positionOf queries index).map values

/-- Replace the coordinates selected by `queries` by fixed symbols carrying
the supplied copy labels and branch values. -/
noncomputable def fixAlong (seed : Seed N q)
    (queries : Fin s ↪ Fin N) (copies : Fin s → Fin q)
    (values : Fin s → Bool) : Seed N q :=
  fun index =>
    match positionOf queries index with
    | none => seed index
    | some position => .inr (copies position, values position)

/-- Restore every coordinate selected by `queries` to the unique free
symbol. -/
noncomputable def freeAlong (seed : Seed N q)
    (queries : Fin s ↪ Fin N) : Seed N q :=
  fun index =>
    match positionOf queries index with
    | none => seed index
    | some _ => .inl ()

end RandomRestriction
end Complexity

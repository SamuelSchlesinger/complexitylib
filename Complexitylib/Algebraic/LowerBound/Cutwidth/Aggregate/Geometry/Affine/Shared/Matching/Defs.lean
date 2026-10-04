/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Defs
public import Mathlib.Data.Finset.Union

/-!
# Disjoint pairs of conjunction gates sharing primary inputs

Pairs refer to actual program indices. Both endpoints have exactly two distinct
primary inputs, and different pairs have disjoint gate endpoints.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Shared

/-- Actual conjunction gates with exactly two distinct direct primary inputs. -/
def exactTwo {n g : ℕ} (p : Program signature n g) : Finset (Fin g) :=
  Finset.univ.filter fun i => (p.lines i).op.isConjunction = true ∧
    (primaryInputs (p.lines i)).card = 2

/-- Gate-disjoint ordered pairs sharing a primary input. -/
structure PrimaryPairing {n g : ℕ} (p : Program signature n g) where
  /-- The selected pairs of actual gate indices. -/
  pairs : Finset (Fin g × Fin g)
  /-- Each endpoint is an actual exact-two conjunction gate. -/
  eligible : ∀ e ∈ pairs, e.1 ∈ exactTwo p ∧ e.2 ∈ exactTwo p
  /-- A pair contains two different gates. -/
  distinct : ∀ e ∈ pairs, e.1 ≠ e.2
  /-- The two gates have a common primary variable. -/
  overlap : ∀ e ∈ pairs, ∃ j, j ∈ primaryInputs (p.lines e.1) ∧
    j ∈ primaryInputs (p.lines e.2)
  /-- No gate occurs in two selected pairs. -/
  disjoint : (pairs : Set (Fin g × Fin g)).Pairwise fun e f =>
    Disjoint ({e.1, e.2} : Finset (Fin g)) {f.1, f.2}

/-- Gate indices belonging to a selected pair. -/
def PrimaryPairing.used {n g : ℕ} {p : Program signature n g}
    (P : PrimaryPairing p) : Finset (Fin g) :=
  P.pairs.biUnion fun e => {e.1, e.2}

/-- Exact-two conjunction gates not selected in any pair. -/
def PrimaryPairing.remaining {n g : ℕ} {p : Program signature n g}
    (P : PrimaryPairing p) : Finset (Fin g) := exactTwo p \ P.used

end Algebraic.Aggregate.Geometry.Shared

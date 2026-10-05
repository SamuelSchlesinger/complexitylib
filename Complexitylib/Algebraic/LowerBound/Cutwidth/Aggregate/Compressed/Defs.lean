/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Observation

/-!
# Jointly compressed aggregate registers

A single finite monoid can encode the simultaneous contributions to every special
gate. Guessing its final state determines all special outputs; checking the same
state checks every special equation. This charges joint states rather than gates.
-/

@[expose] public section

namespace Algebraic.Aggregate.Compressed

variable {J : Type} {State : J → Type} [∀ j, CommMonoid (State j)] {n g : ℕ}

/-- A local factorization of all special registers through one commutative monoid. -/
structure Factorization (p : Program (signature State) n g) (M : Type) [CommMonoid M] where
  /-- The compressed contribution emitted once by each signal. -/
  contribution : Wire n g → Bool → M
  /-- Decoding recovers all original special registers. -/
  decode : M →* Registers p
  /-- Decoding commutes with each local contribution, including repeated slots. -/
  factor : ∀ wire value, decode (contribution wire value) = wireContribution p wire value

variable {p : Program (signature State) n g} {M : Type} [CommMonoid M]

/-- The compressed state emitted by a set of signals. -/
def Factorization.aggregate (c : Factorization p M) (S : Finset (Wire n g))
    (values : Wire n g → Bool) : M := ∏ wire ∈ S, c.contribution wire (values wire)

/-- A joint state determines every Boolean special-gate output. -/
def Factorization.guess (c : Factorization p M) (state : M) : Guess p :=
  fun gate => (p.lines gate).op.readout (c.decode state gate)

/-- The joint state of the true circuit evaluation. -/
def Factorization.actual (c : Factorization p M) (input : Fin n → Bool) : M :=
  c.aggregate Finset.univ (p.trace interpretation input)

/-- One final-state guess and one partial aggregate form the component mixing key. -/
def Factorization.componentKey (c : Factorization p M) (S : Finset (Wire n g))
    (input : Fin n → Bool) : M × M :=
  (c.actual input, c.aggregate S (p.trace interpretation input))

/-- The budget counts the guessed joint state and its independent accumulator. -/
def budget (M : Type) [Fintype M] : ℕ := 2 * Nat.clog 2 (Fintype.card M)

end Algebraic.Aggregate.Compressed

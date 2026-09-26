/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.ModelChecking.Defs
public import Complexitylib.DescriptiveComplexity.Encoding
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Binary certificates for relation environments

List each relation's truth table in context order, using the same tuple order as
the structure encoder. The universe size and arities are supplied externally,
so the certificate needs no header or delimiters. Its length is exactly the sum
of `card ^ arity`. Every string of that length represents one environment.

These are the guessed relation tables in Immerman's *Descriptive Complexity*,
Section 7.1, Proposition 7.6. The functions are computable; their machine time
bounds are a separate obligation.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.DecREnv

/-- A cell in one of the relation-variable truth tables. -/
abbrev EncodingSite (card : Nat) (rctx : List Nat) :=
  Σ r : Fin rctx.length, Fin (rctx.get r) → Fin card

/-- Certificate cells in relation-context order, then canonical tuple order. -/
def encodingSites (card : Nat) (rctx : List Nat) : List (EncodingSite card rctx) :=
  (List.finRange rctx.length).flatMap fun r =>
    (allTuples card (rctx.get r)).map fun args => ⟨r, args⟩

/-- Exact number of bits required to describe all supplied relations. -/
def encodingLength (card : Nat) (rctx : List Nat) : Nat :=
  (rctx.map fun k => card ^ k).sum

/-- The certificate-length polynomial for a fixed list of relation arities. -/
noncomputable def encodingPolynomial (rctx : List Nat) : Polynomial Nat :=
  (rctx.map fun k => Polynomial.X ^ k).sum

/-- Concatenate the supplied relation truth tables without headers or padding. -/
def encode {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) : List Bool :=
  (encodingSites card rctx).map fun site => ρ site.1 site.2

/-- Read a relation environment, defaulting missing entries to false. -/
def read (card : Nat) (rctx : List Nat) (bits : List Bool) : DecREnv card rctx :=
  fun r args => bits[(encodingSites card rctx).idxOf ⟨r, args⟩]?.getD false

/-- Decode a certificate, rejecting precisely the strings of the wrong length. -/
def decode (card : Nat) (rctx : List Nat) (bits : List Bool) :
    Option (DecREnv card rctx) :=
  if bits.length = encodingLength card rctx then some (read card rctx bits) else none

end Complexity.DescriptiveComplexity.DecREnv

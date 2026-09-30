/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
public import Cslib.Computability.Circuit.Basic
public import Mathlib.Data.Finset.Basic

/-!
# Evaluating a circuit with guessed values at a cut

`Program.evalCut` replaces the values of a selected set of gates by guesses,
and evaluates every other gate normally. `Program.CutConsistent` checks the
equation of each selected gate against this evaluation. Only selected gates
need guesses; no values for the other gates are part of the certificate.

The construction works for any signature and interpretation, not just Boolean
circuits. It provides the semantic part of cutting shared gates. Turning the
pieces into formulas and bounding their leaf counts requires further work.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ} {U : Type*}

/-- Evaluate a program, using the guessed value whenever a selected gate is read. -/
def Program.evalCut (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) (guess : cut → U) (j : Fin g) : U :=
  if h : j ∈ cut then guess ⟨j, h⟩
  else I (p.lines j).op fun a =>
    match _hw : (p.lines j).wires a with
    | .input i => x i
    | .gate k => p.evalCut cut I x guess k
termination_by j.val
decreasing_by
  have hlt := p.lines_wires_lt j a
  rw [_hw] at hlt
  simpa using hlt

/-- A guess is consistent if every cut gate's own equation produces its guessed value. -/
def Program.CutConsistent (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) (guess : cut → U) : Prop :=
  ∀ j : cut, (p.lines j).eval I x (p.evalCut cut I x guess) = guess j

end Cslib.Circuits

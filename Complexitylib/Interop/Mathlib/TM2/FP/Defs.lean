/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.Defs
public import Complexitylib.Interop.Mathlib.TM0.Marked.Defs
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Defs

/-!
# Input and output alphabets for the compiled stack machine

The adapter reads bits in stack-bottom order. Its input is therefore reversed
before interpreting it as a TM2 stack, and its output is emitted in reverse
stack order. Canonical string reversal accounts for both conventions. The
finite-alphabet adapter keeps input and output alphabets independent; explicit
binary coding is supplied by the endpoint simulator.
-/

@[expose] public section

namespace Complexity.MathlibTM2

open Turing

/-- Give a compiled stack machine an explicit marked-input and decoded-output interface. -/
abbrev binaryAdapter (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]
    (input : tm.Γ tm.k₀ ≃ Bool) (output : tm.Γ tm.k₁ ≃ Bool)
    {Q : Type} [Fintype Q] [Inhabited Q]
    (G : TM0.Machine (TM2to1.Γ' tm.K tm.Γ) Q) : MathlibTM0.MarkedMachine where
  Alphabet := TM2to1.Γ' tm.K tm.Γ
  alphabetFinite := by
    let : Fintype tm.K := tm.kFin
    infer_instance
  alphabetInhabited := ⟨(false, fun _ => none)⟩
  State := Q
  bit first b := (first, Function.update (fun _ => none) tm.k₀ (some (input.symm b)))
  empty := (true, fun _ => none)
  readBit a := (a.2 tm.k₁).map output
  readBit_blank := rfl
  code := G

/-- Marked input and decoded output for independent finite source alphabets. -/
abbrev alphabetAdapter {α β : Type} (tm : FinTM2) [∀ k, Fintype (tm.Γ k)]
    (input : tm.Γ tm.k₀ ≃ α) (output : tm.Γ tm.k₁ ≃ β)
    {Q : Type} [Fintype Q] [Inhabited Q]
    (G : TM0.Machine (TM2to1.Γ' tm.K tm.Γ) Q) : MathlibTM0.AlphabetMachine α β where
  Alphabet := TM2to1.Γ' tm.K tm.Γ
  alphabetFinite := by
    let : Fintype tm.K := tm.kFin
    infer_instance
  alphabetInhabited := ⟨(false, fun _ => none)⟩
  State := Q
  inputSymbol first a := (first, Function.update (fun _ => none) tm.k₀ (some (input.symm a)))
  empty := (true, fun _ => none)
  readSymbol a := (a.2 tm.k₁).map output
  readSymbol_blank := rfl
  code := G

end Complexity.MathlibTM2

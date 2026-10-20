/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2
public import Complexitylib.Interop.Mathlib.TM2.FP.Defs
public import Complexitylib.Classes.P.Defs
public import Mathlib.Computability.DFA
public import Complexitylib.Encoding.FiniteAlphabet
import Complexitylib.Interop.Mathlib.TM2.FP.Internal.Compiler
import Complexitylib.Interop.Mathlib.TM2.FP.Internal.Guard
import Complexitylib.Interop.Mathlib.TM2.FP.Internal.AlphabetCompiler

/-!
# Mathlib TM2 string computations belong to canonical FP

A polynomial-time Mathlib certificate for a total binary-string function yields
membership in Complexitylib's canonical machine-based FP. All working stack
alphabets are explicitly required to be finite; Mathlib's FinTM2 bundle itself
only includes input-alphabet finiteness. Marked input copying, complete output
decoding, and string reversal account for the stack representation.

The total-function theorem uses the identity encoding on all binary strings.
For a regular domain, `mem_FP_on_dfa` checks the input format and returns empty
output outside the domain; the source time bound is required only inside it.
`mem_FP_encoded` supports independent finite input and output alphabets through
explicit binary symbol codes, including empty alphabets. Invalid symbol codes
return empty output before the source starts. `mem_FP_encoded_on_dfa` additionally
validates a regular binary input domain. Typed problem encodings still need
their own validity and encoding-correspondence arguments.
-/

public section

namespace Complexity.MathlibTM2

/-- Total Mathlib TM2 binary-string computations with finite working alphabets
transfer to the canonical FP class, with no separate output-length assumption. -/
theorem mem_FP {f : List Bool → List Bool}
    (computer : Turing.TM2ComputableInPolyTime id id f)
    [∀ k, Fintype (computer.tm.Γ k)] : f ∈ FP :=
  mem_FP_proof computer

/-- Validate a regular input domain and return empty output on malformed strings.
Only valid inputs need a source time bound; output length is bounded automatically. -/
theorem mem_FP_on_dfa {f : List Bool → List Bool}
    (computer : Turing.TM2ComputableAux Bool Bool)
    [∀ k, Fintype (computer.tm.Γ k)]
    {σ : Type} [Fintype σ] (D : DFA Bool σ) [DecidablePred (· ∈ D.accepts)]
    {p : Polynomial ℕ}
    (h : ∀ w ∈ D.accepts,
      Turing.TM2OutputsInTime computer.tm (w.map computer.inputAlphabet.symm)
        (some ((f w).map computer.outputAlphabet.symm)) (p.eval w.length)) :
    (fun w => if w ∈ D.accepts then f w else []) ∈ FP :=
  mem_FP_on_dfa_proof computer D h

/-- Polynomial-time word functions over independent finite alphabets give canonical FP functions
under explicit binary codes. Invalid codewords return empty output;
no output-size bound is needed. -/
theorem mem_FP_encoded {α β : Type} {f : List α → List β}
    (ci : FiniteAlphabetCode α) (co : FiniteAlphabetCode β)
    (computer : Turing.TM2ComputableInPolyTime id id f)
    [∀ k, Fintype (computer.tm.Γ k)] : ci.map co f ∈ FP :=
  mem_FP_encoded_proof ci co computer

/-- Validate a regular binary domain as well as finite-alphabet symbol codes. Source bounds are
required only for source words whose binary encodings lie in the domain. -/
theorem mem_FP_encoded_on_dfa {α β : Type} {f : List α → List β}
    (ci : FiniteAlphabetCode α) (co : FiniteAlphabetCode β)
    (computer : Turing.TM2ComputableAux α β) [∀ k, Fintype (computer.tm.Γ k)]
    {σ : Type} [Fintype σ] (D : DFA Bool σ) [DecidablePred (· ∈ D.accepts)]
    {p : Polynomial ℕ}
    (h : ∀ xs, ci.encode xs ∈ D.accepts →
      Turing.TM2OutputsInTime computer.tm (xs.map computer.inputAlphabet.symm)
        (some ((f xs).map computer.outputAlphabet.symm)) (p.eval xs.length)) :
    (fun bits => if bits ∈ D.accepts then ci.map co f bits else []) ∈ FP :=
  mem_FP_encoded_on_dfa_proof ci co computer D h

end Complexity.MathlibTM2

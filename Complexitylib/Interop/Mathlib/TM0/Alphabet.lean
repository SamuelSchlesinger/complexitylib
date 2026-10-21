/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Defs
public import Complexitylib.Encoding.FiniteAlphabet
public import Complexitylib.Interop.Cslib.FromMultiTape
public import Complexitylib.Interop.Cslib.Guard
import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Output

/-!
# Finite input and output alphabets transfer to canonical FP

Explicit finite-alphabet codes supply a total binary interface: the machine
rejects malformed codewords with empty output before running the source.
Input and output alphabets can differ and may be empty. Marked input and
complete decoded output add only linear encoding and parsing overhead.
-/

public section

namespace Complexity.MathlibTM0.AlphabetMachine

variable {Input Output : Type}

/-- Parse input codes, preserve the complete source output, and emit its exact binary encoding. -/
theorem computes_cslib (M : AlphabetMachine Input Output)
    (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)
    {input : List Input} {output : List Output} {time : ℕ}
    (h : M.OutputsWithin input output time) :
    (machine M ci co).ComputesInTimeAndSpace (ci.encode input) (co.encode output)
      (2 * (ci.encode input).length + time + (co.size + 1) * output.length + 4)
      ((machine M ci co).spaceUsed ((machine M ci co).initCfg (ci.encode input))
        (2 * (ci.encode input).length + time + (co.size + 1) * output.length + 4)) :=
  computes_proof M ci co h

/-- Polynomial-time source word computations give total binary FP functions under explicit codes. -/
theorem mem_FP {M : AlphabetMachine Input Output}
    (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)
    {f : List Input → List Output} {p q : Polynomial ℕ}
    (h : ∀ xs, M.OutputsWithin xs (f xs) (p.eval xs.length))
    (hlen : ∀ xs, (f xs).length ≤ q.eval xs.length) : ci.map co f ∈ FP := by
  let r := Polynomial.C 2 * Polynomial.X + p + Polynomial.C (co.size + 1) * q + 4
  refine mem_FP_of_computableInTimeAndSpace (p := r)
    (s := fun w => (machine M ci co).spaceUsed ((machine M ci co).initCfg w) (r.eval w.length))
    ⟨_, Phase ci.size co.size M.State, inferInstance, machine M ci co, ?_⟩
  intro w
  refine ⟨r.eval w.length, le_rfl, _, le_rfl, ?_⟩
  simpa [r] using computes_with_bounds M ci co (P := fun _ => True)
    (fun xs _ => h xs) (fun xs _ => hlen xs) w trivial

/-- Source bounds restricted to a regular binary input domain suffice after DFA validation. -/
theorem mem_FP_on_dfa {M : AlphabetMachine Input Output}
    (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)
    {σ : Type} [Fintype σ] (D : DFA Bool σ) [DecidablePred (· ∈ D.accepts)]
    {f : List Input → List Output} {p q : Polynomial ℕ}
    (h : ∀ xs, ci.encode xs ∈ D.accepts → M.OutputsWithin xs (f xs) (p.eval xs.length))
    (hlen : ∀ xs, ci.encode xs ∈ D.accepts → (f xs).length ≤ q.eval xs.length) :
    (fun bits => if bits ∈ D.accepts then ci.map co f bits else []) ∈ FP := by
  let r := Polynomial.C 2 * Polynomial.X + p + Polynomial.C (co.size + 1) * q + 4
  apply CslibGuard.mem_FP_on_dfa (machine M ci co) D (p := r)
  intro w hw
  refine ⟨r.eval w.length, le_rfl,
    (machine M ci co).spaceUsed ((machine M ci co).initCfg w) (r.eval w.length), ?_⟩
  simpa [r] using computes_with_bounds M ci co h hlen w hw

end Complexity.MathlibTM0.AlphabetMachine

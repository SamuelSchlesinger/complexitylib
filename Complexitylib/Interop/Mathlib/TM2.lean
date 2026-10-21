/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.Defs
import Complexitylib.Interop.Mathlib.TM2.Internal.Compiler

/-!
# Mathlib's stack-to-tape compiler has polynomial overhead

Mathlib already compiles `TM2 → TM1 → TM0`. This module proves that its compiler
is efficient: a fixed finitely supported stack program has one finite-state
tape simulator running in `C * (input.length + sourceTime + 1)^2` transitions.
The constant depends only on the program. The stack-track alphabet is finite
whenever there are finitely many stacks and each stack alphabet is finite.

`exists_tm0_computer` applies directly to Mathlib's bundled `FinTM2` and
`TM2OutputsInTime`. Both the input and the complete output tape are exactly
`TM2to1.trInit` of the corresponding stack word, including its bottom marker.
This format stores stacks bottom first. The separate
`Complexitylib.Interop.Mathlib.TM2.FP` interface supplies the binary input/output
adapters and canonical `FP` transfer for finite working alphabets.

The timing proofs are reused from the rational hitting-list development
and remain in their original modules and namespaces.
-/

public section

namespace Complexity.MathlibTM2

open Turing

/-- Every output stack has length at most the initial input length plus a fixed
multiple of the source transition count. -/
theorem exists_output_length_bound (tm : FinTM2) :
    ∃ C : ℕ, 0 < C ∧ ∀ (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : ℕ),
      TM2OutputsInTime tm input (some output) time →
      output.length ≤ input.length + C * time :=
  output_length_bound tm

/-- Mathlib's existing stack compiler simulates every terminating source run
with quadratic transition overhead, retaining the entire represented stack state. -/
theorem exists_tm0_simulator {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K] [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM2.Stmt Γ Λ σ) (F : Finset Λ) (hF : TM2.Supports M F) :
    ∃ (m : ℕ) (G : TM0.Machine (TM2to1.Γ' K Γ) (Fin (m + 1))) (C : ℕ),
      0 < C ∧ ∀ (k : K) (w : List (Γ k)) (b : TM2.Cfg Γ Λ σ) (t : ℕ),
        exec (TM2.step M) t (TM2.init k w) = some b → TM2.step M b = none →
        ∃ u ≤ C * (w.length + t + 1) ^ 2, ∃ a,
          exec (TM0.step G) u (TM0.init (TM2to1.trInit k w)) = some a ∧
          TM0.step G a = none ∧
          ∃ c : TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ,
            TM2to1.TrCfg b c ∧ a.Tape = c.Tape :=
  compile_source M F hF

/-- A bundled Mathlib TM2 has a fixed finite-state tape computer with quadratic
overhead and exact input/output stack-track tapes, including empty words. -/
theorem exists_tm0_computer (tm : FinTM2) :
    ∃ (m : ℕ) (G : TM0.Machine (TM2to1.Γ' tm.K tm.Γ) (Fin (m + 1))) (C : ℕ),
      0 < C ∧ ∀ (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (time : ℕ),
        TM2OutputsInTime tm input (some output) time →
        ∃ u ≤ C * (input.length + time + 1) ^ 2, ∃ a,
          exec (TM0.step G) u (TM0.init (TM2to1.trInit tm.k₀ input)) = some a ∧
          TM0.step G a = none ∧ a.Tape = Tape.mk₁ (TM2to1.trInit tm.k₁ output) :=
  compile_bundled tm

/-- A Mathlib polynomial-time certificate yields one finite-state TM0 and a
polynomial time bound, with its encoded input and complete output tapes explicit. -/
theorem exists_tm0_polynomial_computer {α β Γ Δ : Type}
    {input : α → List Γ} {output : β → List Δ} {f : α → β}
    (computer : TM2ComputableInPolyTime input output f) :
    ∃ (m : ℕ)
      (G : TM0.Machine (TM2to1.Γ' computer.tm.K computer.tm.Γ) (Fin (m + 1)))
      (p : Polynomial ℕ), ∀ a,
        ∃ u ≤ p.eval (input a).length, ∃ c,
          exec (TM0.step G) u
            (TM0.init (TM2to1.trInit computer.tm.k₀
              ((input a).map computer.inputAlphabet.symm))) = some c ∧
          TM0.step G c = none ∧
          c.Tape = Tape.mk₁ (TM2to1.trInit computer.tm.k₁
            ((output (f a)).map computer.outputAlphabet.symm)) := by
  obtain ⟨m, G, C, _, hG⟩ := exists_tm0_computer computer.tm
  refine ⟨m, G, Polynomial.C C * (Polynomial.X + computer.time + 1) ^ 2, ?_⟩
  intro a
  simpa using hG _ _ _ (computer.outputsFun a)

end Complexity.MathlibTM2

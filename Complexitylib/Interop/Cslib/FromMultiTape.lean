/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.FromMultiTape.Defs
public import Complexitylib.Classes.Time
public import Complexitylib.Classes.P.NormalForm
import Complexitylib.Interop.Cslib.FromMultiTape.Internal

/-!
# CSLib multi-tape computations run on Complexitylib machines

CSLib measures the complexity of a language through its multi-tape machines
(`Turing.MultiTapeTM`): `MultiTapeTM.DecidableInTimeAndSpace L enc t s` says
that some machine over the binary alphabet with finitely many states decides
`L` within time `t x` and space `s x` on every input `x`, emitting the single
bit `true` on inputs in `L` and `false` otherwise.

This file proves the converse of `Complexitylib.Interop.Cslib.MultiTape`: a
CSLib computation runs on our machines with a constant-factor time overhead. The
simulator `FromMultiTape.toTM`
(`Complexitylib.Interop.Cslib.FromMultiTape.Defs`) folds each two-way CSLib
work tape onto one of our one-sided work tapes and spends three of its steps
on each CSLib step. It preserves the entire output string and its terminating
blank, so the same simulation covers string functions, including empty outputs.

## Main results

- `Complexity.decidesInTime_of_decidableInTimeAndSpace` — a CSLib
  decider within time `t` yields one of our deciders within time `3 t`
- `Complexity.mem_DTIME_of_decidableInTimeAndSpace` — CSLib-decidable within
  time `t` implies `DTIME(t)`
- `Complexity.mem_P_of_decidableInTimeAndSpace` — CSLib-decidable within
  polynomial time implies `P`
- `Complexity.computesInTime_of_computableInTimeAndSpace` — a CSLib string
  computation within time `t` yields a canonical computation within time `3 t`
- `Complexity.mem_FP_of_computableInTimeAndSpace` — CSLib-computable string
  functions within polynomial time belong to `FP`
-/


public section

namespace Complexity

open Turing

/-- A fixed CSLib machine computes the same complete string on the canonical simulator. -/
theorem FromMultiTape.toTM_computesInTime {k : ℕ} {S : Type} [DecidableEq S] [Fintype S]
    (M : Turing.MultiTapeTM k Bool S) {f : List Bool → List Bool} {t : ℕ → ℕ}
    {s : List Bool → ℕ}
    (h : M.ComputesFunInTimeAndSpace (Function.Embedding.refl _)
      (Function.Embedding.refl _) f (fun x => t x.length) s) :
    (FromMultiTape.toTM M).ComputesInTime f (fun n => 3 * t n) := by
  intro x
  obtain ⟨t', ht', s', _, hc⟩ := h x
  obtain ⟨c', T, hT, hr, hh, hout⟩ := FromMultiTape.toTM_computes_output M hc
  exact ⟨c', T, hT.trans (Nat.mul_le_mul_left 3 ht'), hr, hh, hout⟩

/-- CSLib string computations transfer to the canonical machine model with time factor three. -/
theorem computesInTime_of_computableInTimeAndSpace {f : List Bool → List Bool}
    {t : ℕ → ℕ} {s : List Bool → ℕ}
    (h : Turing.MultiTapeTM.ComputableInTimeAndSpace f (Function.Embedding.refl _)
      (Function.Embedding.refl _) (fun x => t x.length) s) :
    ∃ (k : ℕ) (tm : TM k), tm.ComputesInTime f (fun n => 3 * t n) := by
  obtain ⟨k, S, hS, M, hM⟩ := h
  have := Fintype.ofFinite S
  classical
  exact ⟨k, FromMultiTape.toTM M, FromMultiTape.toTM_computesInTime M hM⟩

/-- Every polynomial-time CSLib string function belongs to canonical `FP`. -/
theorem mem_FP_of_computableInTimeAndSpace {f : List Bool → List Bool}
    {p : Polynomial ℕ} {s : List Bool → ℕ}
    (h : Turing.MultiTapeTM.ComputableInTimeAndSpace f (Function.Embedding.refl _)
      (Function.Embedding.refl _) (fun x => p.eval x.length) s) :
    f ∈ FP := by
  obtain ⟨k, tm, htm⟩ := computesInTime_of_computableInTimeAndSpace (t := p.eval) h
  refine mem_FP_iff_computesInTime_polynomial.mpr ⟨k, tm, Polynomial.C 3 * p, ?_⟩
  simpa using htm

/-- **A CSLib decider runs on Complexitylib.** If a CSLib multi-tape machine
decides `L` within time `t` in the input length (and any space), one of our
machines decides `L` within time `3 t`. -/
theorem decidesInTime_of_decidableInTimeAndSpace {L : Language} {t : ℕ → ℕ}
    {s : List Bool → ℕ}
    (h : Turing.MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
      (fun x => t x.length) s) :
    ∃ (k : ℕ) (tm : TM k), tm.DecidesInTime L (fun n => 3 * t n) := by
  obtain ⟨k, S, hS, M, hM⟩ := h
  have := Fintype.ofFinite S
  classical
  exact ⟨k, FromMultiTape.toTM M, FromMultiTape.toTM_decides M hM⟩

/-- **CSLib time transfers to `DTIME`.** A language decided by a CSLib
multi-tape machine within time `t` in the input length lies in `DTIME(t)`. -/
theorem mem_DTIME_of_decidableInTimeAndSpace {L : Language} {t : ℕ → ℕ}
    {s : List Bool → ℕ}
    (h : Turing.MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
      (fun x => t x.length) s) :
    L ∈ DTIME t := by
  obtain ⟨k, tm, htm⟩ := decidesInTime_of_decidableInTimeAndSpace h
  exact ⟨k, tm, _, htm, BigO.const_mul_left 3 (BigO.refl t)⟩

/-- **CSLib polynomial time transfers to `P`.** A language decided by a CSLib
multi-tape machine within polynomial time in the input length lies in `P`. -/
theorem mem_P_of_decidableInTimeAndSpace {L : Language} {p : Polynomial ℕ}
    {s : List Bool → ℕ}
    (h : Turing.MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _)
      (fun x => p.eval x.length) s) :
    L ∈ P := by
  obtain ⟨k, tm, htm⟩ := decidesInTime_of_decidableInTimeAndSpace (t := p.eval) h
  refine mem_P_iff_decidesInTime_polynomial.mpr ⟨k, tm, Polynomial.C 3 * p, ?_⟩
  simpa using htm

end Complexity

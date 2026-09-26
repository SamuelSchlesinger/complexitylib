/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# Small polynomial-time string functions

A few string functions that polynomial-time constructions throughout the library
build on: a ruler of polynomial length, an emptiness flag, and dropping the
leading bit. Each is one application of the `FP` closure rules of
`Complexitylib.Classes.Containments.Internal.FPBridge`, which this module
re-exports.

## Main definitions

- `Complexity.polyRuler` — a ruler whose length is a polynomial in the input
  length
- `Complexity.emptyFlag` — whether a string is empty, as a one-bit flag
- `Complexity.dropOne` — a string without its leading bit

## Main results

- `Complexity.polyRulerFn_mem_FP`, `Complexity.emptyFlagFn_mem_FP`,
  `Complexity.dropOneFn_mem_FP` — all three are polynomial-time
-/

@[expose] public section

namespace Complexity

/-! ## Rulers of polynomial length -/

/-- A ruler whose length is a polynomial in the input length. -/
def polyRuler (q : Polynomial ℕ) (x : List Bool) : List Bool :=
  List.replicate (q.eval x.length) false

@[simp] theorem polyRuler_length (q : Polynomial ℕ) (x : List Bool) :
    (polyRuler q x).length = q.eval x.length := by
  rw [polyRuler, List.length_replicate]

theorem polyRulerFn_mem_FP (q : Polynomial ℕ) {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => polyRuler q (a z)) ∈ FP := by
  have h : Cobham fun v : Fin 1 → List Bool =>
      List.replicate (Cobham.polyLen q (v 0)).length false :=
    Cobham.zeroBlockFn (Cobham.polyLen_mem q (Cobham.proj 0))
  refine unFn_mem_FP (g := polyRuler q) ?_ ha
  refine h.of_eq fun v => ?_
  rw [polyRuler, Cobham.polyLen_length]

/-! ## Emptiness and the leading bit -/

/-- Is the string empty, as a flag. -/
def emptyFlag (y : List Bool) : List Bool := Cobham.lenLeFlag [] y

@[simp] theorem emptyFlag_nil : emptyFlag [] = [true] := rfl

theorem emptyFlag_cons (b : Bool) (y : List Bool) : emptyFlag (b :: y) = [false] := by
  rw [emptyFlag, Cobham.lenLeFlag]
  simp [nonemptyFlag, notBit]

theorem emptyFlag_pair (a b : List Bool) : emptyFlag (pair a b) = [false] := by
  cases a with
  | nil => rw [pair]; rfl
  | cons c a => rw [pair_cons_eq]; exact emptyFlag_cons _ _

theorem emptyFlagFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => emptyFlag (a z)) ∈ FP :=
  lenLeFlagFn_mem_FP (constFn_mem_FP []) ha

/-- Drop the leading bit. -/
def dropOne (y : List Bool) : List Bool := y.drop 1

theorem dropOneFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => dropOne (a z)) ∈ FP := by
  have := dropLenFn_mem_FP (constFn_mem_FP [false]) ha
  simpa [dropOne] using this

end Complexity

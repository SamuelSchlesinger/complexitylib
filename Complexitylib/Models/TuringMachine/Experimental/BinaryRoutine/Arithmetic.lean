/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic.Internal

/-!
# Arithmetic leaves for proof-carrying binary routines

This module exposes sound proof-carrying adapters for canonical binary
arithmetic, fixed-polynomial evaluation, natural-code emission, and raw-gate
emission. Each theorem connects the adapter's pure value effect, exact emitted
word, time bound, and all-prefix space bound to its concrete Turing machine.

## Main results

- `clear_sound`, `addConst_sound`, `set_sound`, `add_sound`, and `mulAdd_sound`
  cover basic arithmetic leaves.
- `evalPolynomial_sound` covers fixed natural-polynomial evaluation.
- `emitNatCode_sound` and `emitRawGate_sound` cover the two encoding leaves.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

variable {n : ℕ}

/-- Clearing one canonical binary value is a sound routine leaf. -/
theorem clear_sound (idx : Fin n) :
    (clear idx).Sound :=
  clear_sound_internal idx

/-- Adding a hardwired natural to one canonical value is sound. -/
theorem addConst_sound (idx : Fin n) (constant : ℕ) :
    (addConst idx constant).Sound :=
  addConst_sound_internal idx constant

/-- Replacing one canonical binary value by a hardwired natural is sound. -/
theorem set_sound (idx : Fin n) (value : ℕ) :
    (set idx value).Sound :=
  set_sound_internal idx value

/-- Preserved-source binary addition is sound on its explicit distinct-index
and zero-counter domain. -/
theorem add_sound (srcIdx dstIdx counterIdx : Fin n) :
    (add srcIdx dstIdx counterIdx).Sound :=
  add_sound_internal srcIdx dstIdx counterIdx

/-- Binary multiply-add is sound on its explicit distinct-index and
zero-counter domain. -/
theorem mulAdd_sound
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) :
    (mulAdd leftIdx rightIdx accIdx mulCounterIdx addCounterIdx).Sound :=
  mulAdd_sound_internal leftIdx rightIdx accIdx mulCounterIdx addCounterIdx

/-- Evaluation of a fixed natural polynomial is sound on its explicit
distinct-index and zero-scratch domain. -/
theorem evalPolynomial_sound
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) :
    (evalPolynomial inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx
      p).Sound :=
  evalPolynomial_sound_internal inputIdx resultIdx scratchIdx mulCounterIdx
    addCounterIdx p

/-- Terminated-unary natural-code emission is sound, preserves every pure
value, and restores its zero scratch counter. -/
theorem emitNatCode_sound (counterIdx valueIdx : Fin n) :
    (emitNatCode counterIdx valueIdx).Sound :=
  emitNatCode_sound_internal counterIdx valueIdx

/-- Raw-gate emission is sound, preserves every pure value, and emits exactly
the encoded gate assembled from its two referenced values. -/
theorem emitRawGate_sound
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGate op negated₀ negated₁ emitCounterIdx input₀Idx
      input₁Idx).Sound :=
  emitRawGate_sound_internal op negated₀ negated₁ emitCounterIdx
    input₀Idx input₁Idx

end BinaryRoutine

end Complexity

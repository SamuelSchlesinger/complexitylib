/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.FromMultiTape
public import Complexitylib.Interop.Cslib.MultiTape

/-!
# `P` is CSLib polynomial time

Combining both directions of the multi-tape bridge: a language is in `P`
exactly when a CSLib multi-tape machine decides it within polynomial time and
space in the input length.

## Main results

- `Complexity.mem_P_iff_decidableInTimeAndSpace`
-/


public section

namespace Complexity

open Turing

/-- **`P` is exactly CSLib polynomial time.** A language is in `P` if and only
if some CSLib multi-tape machine decides it within polynomial time and space
in the input length. -/
theorem mem_P_iff_decidableInTimeAndSpace {L : Language} :
    L ∈ P ↔ ∃ p : Polynomial ℕ, MultiTapeTM.DecidableInTimeAndSpace L
      (Function.Embedding.refl _) (fun x => p.eval x.length) (fun x => p.eval x.length) :=
  ⟨decidableInTimeAndSpace_of_mem_P, fun ⟨_, h⟩ => mem_P_of_decidableInTimeAndSpace h⟩

end Complexity

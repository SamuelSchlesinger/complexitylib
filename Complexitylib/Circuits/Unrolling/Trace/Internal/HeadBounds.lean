/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Defs
public import Complexitylib.Models.TuringMachine.Internal

/-!
# Head bounds for prefixes of bounded traces

This internal module adapts the general head-growth estimates for NTM traces
to the strict bound required by the one-step circuit formulas. At every
proper prefix `i < T` of a trace from `initCfg`, all named heads are strictly
below `T`. It also identifies one `choiceStep` from prefix `i` with prefix
`i + 1` of the same full choice sequence.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Every named head in a proper prefix of an initialized length-`T` trace is
strictly below the circuit horizon. -/
theorem headsLt_trace_prefix_internal
    (tm : NTM k) (T i : ℕ) (choices : Fin T → Bool) (x : List Bool)
    (hi : i < T) :
    HeadsLt T
      (tm.trace i (fun j => choices ⟨j.val, by omega⟩) (tm.initCfg x)) := by
  intro tape
  cases tape with
  | input =>
      have hbound :
          (tm.trace i (fun j => choices ⟨j.val, by omega⟩)
            (tm.initCfg x)).input.head ≤ i := by
        simpa using tm.input_head_trace_le i
          (fun j => choices ⟨j.val, by omega⟩) (tm.initCfg x)
      exact lt_of_le_of_lt hbound hi
  | work tapeIndex =>
      have hbound :
          ((tm.trace i (fun j => choices ⟨j.val, by omega⟩)
            (tm.initCfg x)).work tapeIndex).head ≤ i := by
        simpa using tm.work_head_trace_le i
          (fun j => choices ⟨j.val, by omega⟩) (tm.initCfg x) tapeIndex
      exact lt_of_le_of_lt hbound hi
  | output =>
      have hbound :
          (tm.trace i (fun j => choices ⟨j.val, by omega⟩)
            (tm.initCfg x)).output.head ≤ i := by
        simpa using tm.output_head_trace_le i
          (fun j => choices ⟨j.val, by omega⟩) (tm.initCfg x)
      exact lt_of_le_of_lt hbound hi

/-- Taking one `choiceStep` from prefix `i` gives prefix `i + 1` of the same
full bounded choice sequence. -/
theorem choiceStep_trace_prefix_internal
    (tm : NTM k) (T i : ℕ) (choices : Fin T → Bool) (x : List Bool)
    (hi : i < T) :
    choiceStep tm (choices ⟨i, hi⟩)
        (tm.trace i (fun j => choices ⟨j.val, by omega⟩) (tm.initCfg x)) =
      tm.trace (i + 1) (fun j => choices ⟨j.val, by omega⟩) (tm.initCfg x) := by
  simpa [choiceStep, Fin.castLE, Fin.natAdd] using
    (tm.trace_add i 1 (fun j : Fin (i + 1) => choices ⟨j.val, by omega⟩)
      (tm.initCfg x)).symm

end CircuitUnrolling

end Complexity

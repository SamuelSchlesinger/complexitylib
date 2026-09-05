/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Unrolling.Trace.Internal.HeadBounds
public import Complexitylib.Circuits.Unrolling.Trace.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.ArrayEvaluation

/-!
# Evaluation of tiled bounded-trace circuits

This internal module proves a concrete-array invariant for every canonical
prefix of a tiled trace. The invariant starts with the initialization
fragment, appends one array-native transition fragment at a time, and keeps
the current packed block synchronized with the corresponding NTM trace
prefix. The complete-trace theorem is the horizon specialization.
-/


public section

namespace Complexity

namespace CircuitUnrolling

/-- Evaluating the first `i` layers succeeds and encodes the corresponding
initialized trace prefix. -/
theorem evalAux?_prefixTraceBuild_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j, wires[(layout.choice j).val]? = some (choices j))
    (i : ℕ) (hi : i ≤ T) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (prefixTraceBuild tm T n available i layout).circuit wires = some result ∧
        result.size = (prefixTraceBuild tm T n available i layout).available ∧
        (∀ j < wires.size, result[j]? = wires[j]?) ∧
        EncodesConfig tm T
          (prefixTraceBuild tm T n available i layout).configBase result
          (tm.trace i (fun j => choices ⟨j.val, by omega⟩)
            (tm.initCfg x.toList)) := by
  induction i with
  | zero =>
      obtain ⟨result, heval, hresultSize, hprefix, hencodes⟩ :=
        evalAux?_initFragment_internal tm T n available layout hsize x hdata
      refine ⟨result, ?_, ?_, hprefix, ?_⟩
      · rw [prefixTraceBuild_zero_internal]
        exact heval
      · rw [prefixTraceBuild_zero_internal]
        simpa [initialTraceBuild, hsize] using hresultSize
      · rw [prefixTraceBuild_zero_internal]
        simpa [initialTraceBuild, NTM.trace] using hencodes
  | succ i ih =>
      have hiT : i < T := by omega
      obtain ⟨middle, hevalMiddle, hmiddleSize, hprimaryPreserved,
          hmiddleEncodes⟩ := ih (Nat.le_of_lt hiT)
      let build := prefixTraceBuild tm T n available i layout
      have hbuildAvailable : build.available = available + build.size := by
        simpa [build] using
          prefixTraceBuild_available_internal tm T n available i layout
      have hbuildNonzero : build.available ≠ 0 := by
        have havailable := NeZero.ne available
        omega
      let : NeZero build.available := ⟨hbuildNonzero⟩
      let index : Fin T := ⟨i, hiT⟩
      have hchoiceMiddle :
          middle[(layout.choice index).val]? = some (choices index) := by
        rw [hprimaryPreserved]
        · exact hchoices index
        · rw [hsize]
          exact (layout.choice index).isLt
      have hchoiceBound : (layout.choice index).val < build.available := by
        have hindex := (layout.choice index).isLt
        omega
      have hconfigBound : build.configBase + configWidth tm T ≤ build.available := by
        have hend :=
          prefixTraceBuild_outputEnd_internal tm T n available i layout
        simpa [build] using hend.le
      have hheads :
          HeadsLt T
            (tm.trace i (fun j => choices ⟨j.val, by omega⟩)
              (tm.initCfg x.toList)) :=
        headsLt_trace_prefix_internal tm T i choices x.toList hiT
      obtain ⟨result, hevalStep, hresultSize, hmiddlePreserved,
          hresultEncodes⟩ :=
        evalAux?_stepFragment_of_encodes_internal tm T build.configBase
          (layout.choice index).val build.available (choices index) middle
          (tm.trace i (fun j => choices ⟨j.val, by omega⟩)
            (tm.initCfg x.toList))
          hmiddleSize hchoiceMiddle (by simpa [build] using hmiddleEncodes)
          hchoiceBound hconfigBound hheads
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · rw [prefixTraceBuild_succ_circuit_internal tm T n available i layout hiT,
          CircuitCode.RawCircuit.evalAux?_append, hevalMiddle]
        simpa [build, index] using hevalStep
      · rw [prefixTraceBuild_succ_available_internal tm T n available i layout hiT]
        simpa [build, index, hmiddleSize] using hresultSize
      · intro j hj
        have hjMiddle : j < middle.size := by
          rw [hmiddleSize, hbuildAvailable, ← hsize]
          omega
        rw [hmiddlePreserved j hjMiddle]
        exact hprimaryPreserved j hj
      · rw [prefixTraceBuild_succ_configBase_internal tm T n available i layout hiT,
          ← choiceStep_trace_prefix_internal tm T i choices x.toList hiT]
        simpa [build, index] using hresultEncodes

/-- Evaluating the complete tiled trace appends its exact gate count, preserves
the primary prefix, and encodes the final bounded NTM trace. -/
theorem evalAux?_traceFragment_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j, wires[(layout.choice j).val]? = some (choices j)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (traceFragment tm T n available layout) wires = some result ∧
        result.size = wires.size + traceFragmentSize tm T n available layout ∧
        (∀ j < wires.size, result[j]? = wires[j]?) ∧
        EncodesConfig tm T (traceOutputBase tm T n available layout) result
          (tm.trace T choices (tm.initCfg x.toList)) := by
  obtain ⟨result, heval, hresultSize, hprefix, hencodes⟩ :=
    evalAux?_prefixTraceBuild_internal tm T n available layout x choices wires
      hsize hdata hchoices T le_rfl
  rw [prefixTraceBuild_eq_traceBuild_internal tm T n available layout] at heval
  rw [prefixTraceBuild_eq_traceBuild_internal tm T n available layout] at hresultSize
  rw [prefixTraceBuild_eq_traceBuild_internal tm T n available layout] at hencodes
  have hchoiceFunction :
      (fun j : Fin T => choices ⟨j.val, by omega⟩) = choices := by
    funext j
    congr 1
  rw [hchoiceFunction] at hencodes
  refine ⟨result, ?_, ?_, hprefix, ?_⟩
  · simpa [traceFragment] using heval
  · calc
      result.size = (traceBuild tm T n available layout).available := hresultSize
      _ = available + (traceBuild tm T n available layout).size :=
        traceBuild_available_internal tm T n available layout
      _ = wires.size + traceFragmentSize tm T n available layout := by
        rw [hsize]
        rfl
  · simpa [traceOutputBase] using hencodes

end CircuitUnrolling

end Complexity

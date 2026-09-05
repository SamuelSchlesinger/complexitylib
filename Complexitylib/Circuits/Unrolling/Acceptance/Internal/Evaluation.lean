/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Unrolling.Acceptance.Defs
public import Complexitylib.Circuits.Unrolling.Acceptance.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Trace.Internal.Evaluation

/-!
# Evaluation of bounded-trace acceptance circuits

This internal module composes the complete trace evaluator with the final
halt-and-output AND gate. The resulting raw circuit's last wire is exactly the
Boolean acceptance predicate used by `NTM.acceptCount`.
-/


public section

namespace Complexity

namespace CircuitUnrolling

/-- Evaluating the acceptance circuit appends the Boolean acceptance predicate
to the successfully evaluated trace array. -/
theorem evalAux?_acceptanceRawCircuit_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j, wires[(layout.choice j).val]? = some (choices j)) :
    ∃ traceResult,
      CircuitCode.RawCircuit.evalAux?
          (acceptanceRawCircuit tm T n available layout) wires =
        some (traceResult.push (decide (
          (tm.trace T choices (tm.initCfg x.toList)).state = tm.qhalt ∧
            (tm.trace T choices (tm.initCfg x.toList)).output.cells 1 = Γ.one))) ∧
      traceResult.size =
        wires.size + traceFragmentSize tm T n available layout ∧
      (∀ i < wires.size, traceResult[i]? = wires[i]?) ∧
      EncodesConfig tm T (traceOutputBase tm T n available layout) traceResult
        (tm.trace T choices (tm.initCfg x.toList)) := by
  obtain ⟨traceResult, htrace, htraceSize, hprefix, hencodes⟩ :=
    evalAux?_traceFragment_internal tm T n available layout x choices wires
      hsize hdata hchoices
  let c := tm.trace T choices (tm.initCfg x.toList)
  have hstate :
      traceResult[configWire tm T (traceOutputBase tm T n available layout)
        (.state tm.qhalt)]? = some (decide (c.state = tm.qhalt)) := by
    simpa [c, ConfigAtom.value] using hencodes (.state tm.qhalt)
  have houtput :
      traceResult[configWire tm T (traceOutputBase tm T n available layout)
        (.cell .output ⟨1, by omega⟩ Γ.one)]? =
        some (decide (c.output.cells 1 = Γ.one)) := by
    simp only [c]
    exact hencodes (.cell .output ⟨1, by omega⟩ Γ.one)
  have hacceptance :
      (decide (c.state = tm.qhalt) && decide (c.output.cells 1 = Γ.one)) =
        decide (c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one) := by
    by_cases hhalt : c.state = tm.qhalt <;>
      by_cases hone : c.output.cells 1 = Γ.one <;>
        simp [hhalt, hone]
  refine ⟨traceResult, ?_, htraceSize, hprefix, hencodes⟩
  rw [acceptanceRawCircuit, CircuitCode.RawCircuit.evalAux?_append, htrace]
  simp only [Option.bind_some]
  simp only [CircuitCode.RawCircuit.evalAux?, acceptanceGate,
    CircuitCode.RawGate.eval]
  rw [hstate, houtput]
  simp only [Option.bind_eq_bind, Option.bind_some, Bool.false_xor]
  change some (traceResult.push
    (decide (c.state = tm.qhalt) && decide (c.output.cells 1 = Γ.one))) =
      some (traceResult.push
        (decide (c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one)))
  exact congrArg (fun value => some (traceResult.push value)) hacceptance

/-- On a fixed-length primary input, raw single-output evaluation returns the
acceptance predicate of the represented bounded trace. -/
theorem eval?_acceptanceRawCircuit_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (input : BitString available)
    (hdata : ∀ j, input (layout.data j) = x j)
    (hchoices : ∀ j, input (layout.choice j) = choices j) :
    CircuitCode.RawCircuit.eval?
        (acceptanceRawCircuit tm T n available layout) input.toList =
      some (decide (
        (tm.trace T choices (tm.initCfg x.toList)).state = tm.qhalt ∧
          (tm.trace T choices (tm.initCfg x.toList)).output.cells 1 = Γ.one)) := by
  let wires := input.toList.toArray
  have hwiresSize : wires.size = available := by
    simp [wires]
  have hwiresInput : ∀ i : Fin available,
      wires[i.val]? = some (input i) := by
    intro i
    simp [wires, BitString.toList, i.isLt]
  have hwiresData : ∀ j, wires[(layout.data j).val]? = some (x j) := by
    intro j
    rw [hwiresInput (layout.data j), hdata j]
  have hwiresChoices :
      ∀ j, wires[(layout.choice j).val]? = some (choices j) := by
    intro j
    rw [hwiresInput (layout.choice j), hchoices j]
  obtain ⟨traceResult, heval, htraceSize, _hprefix, _hencodes⟩ :=
    evalAux?_acceptanceRawCircuit_internal tm T n available layout x choices
      wires hwiresSize hwiresData hwiresChoices
  have htraceResultSize :
      traceResult.size = available + traceFragmentSize tm T n available layout := by
    simpa [hwiresSize] using htraceSize
  have hcircuitLength :
      (acceptanceRawCircuit tm T n available layout).length =
        traceFragmentSize tm T n available layout + 1 := by
    exact length_acceptanceRawCircuit_internal tm T n available layout
  have houtputIndex :
      input.toList.length +
          (acceptanceRawCircuit tm T n available layout).length - 1 =
        traceResult.size := by
    rw [BitString.length_toList, hcircuitLength, htraceResultSize]
    omega
  have hnonempty :
      (acceptanceRawCircuit tm T n available layout).isEmpty = false := by
    simp [acceptanceRawCircuit]
  rw [CircuitCode.RawCircuit.eval?]
  simp only [hnonempty, Bool.false_eq_true, ite_false, wires, heval]
  rw [houtputIndex]
  exact Array.getElem?_push_size

end CircuitUnrolling

end Complexity

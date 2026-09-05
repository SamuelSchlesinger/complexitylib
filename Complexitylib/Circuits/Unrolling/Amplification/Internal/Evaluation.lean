/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Unrolling.Acceptance.Internal.Evaluation
public import Complexitylib.Circuits.Unrolling.Amplification.Internal.Structure

/-!
# Evaluation internals for parallel amplification circuits

This module evaluates the canonical prefixes of the independent-copy builder.
Every completed copy records its bounded acceptance bit at the corresponding
verdict wire, while later fragments preserve both the primary input prefix and
all earlier verdicts. The complete copy bank then feeds those bits directly to
the unary threshold compiler.

The final result intentionally remains in the dependency-light form
`Fin.countP`: its interpretation as a block-event majority belongs above the
circuit layer.
-/


public section

namespace Complexity

namespace CircuitUnrolling

/-- Evaluating the first `i` acceptance copies succeeds, preserves every
primary input, and records the exact bounded acceptance bit for each completed
run. -/
theorem evalAux?_prefixAcceptanceCopiesBuild_internal
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (x : BitString n) (choices : Fin runs → BitString T)
    (wires : Array Bool) (hsize : wires.size = primaryAvailable)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j t, wires[(layout.choice j t).val]? = some (choices j t))
    (i : ℕ) (hi : i ≤ runs) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
            layout).circuit wires = some result ∧
        result.size =
          (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
            layout).available primaryAvailable ∧
        (∀ j < wires.size, result[j]? = wires[j]?) ∧
        ∀ j : Fin runs, j.val < i →
          result[(prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
            layout).verdictWires j]? =
              some (parallelAcceptanceBits tm T x choices j) := by
  induction i with
  | zero =>
      refine ⟨wires, ?_, ?_, ?_, ?_⟩
      · rw [prefixAcceptanceCopiesBuild_zero_internal]
        rfl
      · rw [prefixAcceptanceCopiesBuild_zero_internal]
        simpa [initialAcceptanceCopiesBuild,
          AcceptanceCopiesBuild.available] using hsize
      · intro j _hj
        rfl
      · intro j hj
        omega
  | succ i ih =>
      have hiruns : i < runs := by omega
      obtain ⟨middle, hevalMiddle, hmiddleSize, hprimaryPreserved,
          hmiddleVerdicts⟩ := ih (Nat.le_of_lt hiruns)
      let previous :=
        prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i layout
      let runLayout :=
        (layout.run ⟨i, hiruns⟩).weaken previous.circuit.length
      let fragment :=
        acceptanceRawCircuit tm T n (previous.available primaryAvailable)
          runLayout
      have hmiddleSize' :
          middle.size = previous.available primaryAvailable := by
        simpa [previous] using hmiddleSize
      have hmiddleVerdicts' : ∀ j : Fin runs, j.val < i →
          middle[previous.verdictWires j]? =
            some (parallelAcceptanceBits tm T x choices j) := by
        simpa [previous] using hmiddleVerdicts
      have hpreviousNonzero :
          previous.available primaryAvailable ≠ 0 := by
        have hprimaryNonzero := NeZero.ne primaryAvailable
        change primaryAvailable + previous.circuit.length ≠ 0
        omega
      let : NeZero (previous.available primaryAvailable) :=
        ⟨hpreviousNonzero⟩
      have hdataMiddle : ∀ j,
          middle[(runLayout.data j).val]? = some (x j) := by
        intro j
        have hrunData :
            (runLayout.data j).val = (layout.data j).val := by
          simp [runLayout]
        calc
          middle[(runLayout.data j).val]? =
              middle[(layout.data j).val]? := by rw [hrunData]
          _ = wires[(layout.data j).val]? :=
            hprimaryPreserved _ (by
              rw [hsize]
              exact (layout.data j).isLt)
          _ = some (x j) := hdata j
      have hchoicesMiddle : ∀ t,
          middle[(runLayout.choice t).val]? =
            some (choices ⟨i, hiruns⟩ t) := by
        intro t
        have hrunChoice :
            (runLayout.choice t).val =
              (layout.choice ⟨i, hiruns⟩ t).val := by
          simp [runLayout]
        calc
          middle[(runLayout.choice t).val]? =
              middle[(layout.choice ⟨i, hiruns⟩ t).val]? := by
            rw [hrunChoice]
          _ = wires[(layout.choice ⟨i, hiruns⟩ t).val]? :=
            hprimaryPreserved _ (by
              rw [hsize]
              exact (layout.choice ⟨i, hiruns⟩ t).isLt)
          _ = some (choices ⟨i, hiruns⟩ t) := hchoices ⟨i, hiruns⟩ t
      obtain ⟨traceResult, hevalFragment, htraceSize, _htracePrefix,
          _hencodes⟩ :=
        evalAux?_acceptanceRawCircuit_internal tm T n
          (previous.available primaryAvailable) runLayout x
          (choices ⟨i, hiruns⟩) middle hmiddleSize' hdataMiddle
          hchoicesMiddle
      let value := parallelAcceptanceBits tm T x choices ⟨i, hiruns⟩
      let result := traceResult.push value
      have hevalFragment' :
          CircuitCode.RawCircuit.evalAux? fragment middle = some result := by
        simpa [fragment, result, value, parallelAcceptanceBits,
          boundedAcceptanceBit] using hevalFragment
      have hfragmentLength :
          fragment.length =
            traceFragmentSize tm T n (previous.available primaryAvailable)
                runLayout + 1 := by
        exact length_acceptanceRawCircuit_internal tm T n
          (previous.available primaryAvailable) runLayout
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · rw [prefixAcceptanceCopiesBuild_succ_circuit_internal tm runs T n
          primaryAvailable i layout hiruns,
          CircuitCode.RawCircuit.evalAux?_append, hevalMiddle]
        simpa [previous, runLayout, fragment] using hevalFragment'
      · rw [prefixAcceptanceCopiesBuild_succ_available_internal tm runs T n
          primaryAvailable i layout hiruns]
        change result.size =
          previous.available primaryAvailable + fragment.length
        simp only [result, Array.size_push]
        rw [htraceSize, hmiddleSize', hfragmentLength]
        omega
      · intro j hj
        have hjMiddle : j < middle.size := by
          rw [hmiddleSize']
          change j < primaryAvailable + previous.circuit.length
          rw [← hsize]
          omega
        exact
          (CircuitCode.RawCircuit.evalAux?_preserves_prefix
              hevalFragment' hjMiddle).trans
            (hprimaryPreserved j hj)
      · intro j hj
        by_cases hji : j = (⟨i, hiruns⟩ : Fin runs)
        · subst j
          rw [prefixAcceptanceCopiesBuild_succ_verdict_internal tm runs T n
            primaryAvailable i layout hiruns]
          change result[
              previous.available primaryAvailable + fragment.length - 1]? =
            some value
          have houtputIndex :
              previous.available primaryAvailable + fragment.length - 1 =
                traceResult.size := by
            rw [hfragmentLength, htraceSize, hmiddleSize']
            omega
          rw [houtputIndex]
          exact Array.getElem?_push_size
        · have hjne : j.val ≠ i := by
            intro hval
            apply hji
            apply Fin.ext
            exact hval
          have hjlt : j.val < i := by omega
          have hbound :=
            prefixAcceptanceCopiesBuild_verdict_bounds_internal tm runs T n
              primaryAvailable i layout (Nat.le_of_lt hiruns) j hjlt
          have hjMiddle : previous.verdictWires j < middle.size := by
            rw [hmiddleSize']
            simpa [previous] using hbound.2
          rw [prefixAcceptanceCopiesBuild_succ_verdict_of_ne_internal tm
            runs T n primaryAvailable i layout hiruns j hji]
          change result[previous.verdictWires j]? =
            some (parallelAcceptanceBits tm T x choices j)
          exact
            (CircuitCode.RawCircuit.evalAux?_preserves_prefix
                hevalFragment' hjMiddle).trans
              (hmiddleVerdicts' j hjlt)

/-- Evaluating all independent acceptance copies appends their exact gate
count and populates every recorded verdict wire. -/
theorem evalAux?_acceptanceCopiesFragment_internal
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (x : BitString n) (choices : Fin runs → BitString T)
    (wires : Array Bool) (hsize : wires.size = primaryAvailable)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j t, wires[(layout.choice j t).val]? = some (choices j t)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (acceptanceCopiesFragment tm runs T n primaryAvailable layout)
          wires = some result ∧
        result.size = wires.size +
          acceptanceCopiesSize tm runs T n primaryAvailable layout ∧
        (∀ j < wires.size, result[j]? = wires[j]?) ∧
        ∀ j : Fin runs,
          result[(acceptanceCopiesVerdictWires tm runs T n primaryAvailable
            layout) j]? = some (parallelAcceptanceBits tm T x choices j) := by
  obtain ⟨result, heval, hresultSize, hprefix, hverdicts⟩ :=
    evalAux?_prefixAcceptanceCopiesBuild_internal tm runs T n
      primaryAvailable layout x choices wires hsize hdata hchoices runs
      (Nat.le_refl runs)
  rw [prefixAcceptanceCopiesBuild_all_internal tm runs T n primaryAvailable
    layout] at heval hresultSize hverdicts
  refine ⟨result, ?_, ?_, hprefix, ?_⟩
  · simpa [acceptanceCopiesFragment] using heval
  · simpa [AcceptanceCopiesBuild.available, acceptanceCopiesSize, hsize]
      using hresultSize
  · intro j
    simpa [acceptanceCopiesVerdictWires] using hverdicts j j.isLt

/-- Evaluating the complete amplified circuit feeds the independent bounded
acceptance bits to the strict-majority threshold fragment. -/
theorem evalAux?_amplifiedAcceptanceRawCircuit_internal
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (x : BitString n) (choices : Fin runs → BitString T)
    (wires : Array Bool) (hsize : wires.size = primaryAvailable)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j t, wires[(layout.choice j t).val]? = some (choices j t)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout)
          wires = some result ∧
        result.size = wires.size +
          (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
            layout).length ∧
        (∀ j < wires.size, result[j]? = wires[j]?) ∧
        result[(amplifiedAcceptanceOutputWire tm runs T n primaryAvailable
          layout)]? = some (decide (strictMajorityThreshold runs ≤
            Fin.countP (parallelAcceptanceBits tm T x choices))) := by
  obtain ⟨middle, hevalCopies, hmiddleSize, hprimaryPreserved,
      hmiddleVerdicts⟩ :=
    evalAux?_acceptanceCopiesFragment_internal tm runs T n primaryAvailable
      layout x choices wires hsize hdata hchoices
  let built :=
    acceptanceCopiesBuild tm runs T n primaryAvailable layout
  let thresholdAvailable := primaryAvailable + built.circuit.length
  let threshold := strictMajorityThreshold runs
  let bits := parallelAcceptanceBits tm T x choices
  have hevalCopies' :
      CircuitCode.RawCircuit.evalAux? built.circuit wires = some middle := by
    simpa [built, acceptanceCopiesFragment] using hevalCopies
  have hmiddleSize' : middle.size = thresholdAvailable := by
    simpa [thresholdAvailable, built, acceptanceCopiesSize, hsize] using
      hmiddleSize
  have hrefs : ∀ j, built.verdictWires j < thresholdAvailable := by
    intro j
    have hbound :=
      (acceptanceCopiesVerdictWires_bounds_internal tm runs T n
        primaryAvailable layout j).2
    simpa [built, thresholdAvailable, acceptanceCopiesVerdictWires,
      acceptanceCopiesSize] using hbound
  have hinputs : ∀ j,
      middle[built.verdictWires j]? = some (bits j) := by
    intro j
    simpa [built, bits, acceptanceCopiesVerdictWires] using
      hmiddleVerdicts j
  have hthresholdAvailableNonzero : thresholdAvailable ≠ 0 := by
    have hprimaryNonzero := NeZero.ne primaryAvailable
    change primaryAvailable + built.circuit.length ≠ 0
    omega
  let : NeZero thresholdAvailable := ⟨hthresholdAvailableNonzero⟩
  obtain ⟨result, hevalThreshold, hresultSize, hmiddlePreserved,
      houtput⟩ :=
    CircuitCode.Threshold.evalAux?_compileRaw_internal thresholdAvailable
      threshold built.verdictWires bits middle hmiddleSize' hrefs hinputs
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · rw [amplifiedAcceptanceRawCircuit,
      CircuitCode.RawCircuit.evalAux?_append, hevalCopies']
    simpa [built, thresholdAvailable, threshold] using hevalThreshold
  · rw [length_amplifiedAcceptanceRawCircuit_internal]
    simp only [threshold] at hresultSize
    omega
  · intro j hj
    have hjMiddle : j < middle.size := by
      rw [hmiddleSize]
      omega
    exact (hmiddlePreserved j hjMiddle).trans (hprimaryPreserved j hj)
  · simpa [amplifiedAcceptanceOutputWire, built, thresholdAvailable,
      threshold, bits] using houtput

/-- Raw single-output evaluation returns the threshold predicate over all
independent bounded acceptance bits. -/
theorem eval?_amplifiedAcceptanceRawCircuit_internal
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (x : BitString n) (choices : Fin runs → BitString T)
    (input : BitString primaryAvailable)
    (hdata : ∀ j, input (layout.data j) = x j)
    (hchoices : ∀ j t, input (layout.choice j t) = choices j t) :
    CircuitCode.RawCircuit.eval?
        (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout)
        input.toList = some (decide (strictMajorityThreshold runs ≤
          Fin.countP (parallelAcceptanceBits tm T x choices))) := by
  let wires := input.toList.toArray
  have hwiresSize : wires.size = primaryAvailable := by
    simp [wires]
  have hwiresInput : ∀ i : Fin primaryAvailable,
      wires[i.val]? = some (input i) := by
    intro i
    simp [wires, BitString.toList, i.isLt]
  have hwiresData : ∀ j,
      wires[(layout.data j).val]? = some (x j) := by
    intro j
    rw [hwiresInput (layout.data j), hdata j]
  have hwiresChoices : ∀ j t,
      wires[(layout.choice j t).val]? = some (choices j t) := by
    intro j t
    rw [hwiresInput (layout.choice j t), hchoices j t]
  obtain ⟨result, heval, _hresultSize, _hprefix, houtput⟩ :=
    evalAux?_amplifiedAcceptanceRawCircuit_internal tm runs T n
      primaryAvailable layout x choices wires hwiresSize hwiresData
      hwiresChoices
  let built :=
    acceptanceCopiesBuild tm runs T n primaryAvailable layout
  let thresholdFragment :=
    CircuitCode.Threshold.compileRaw
      (primaryAvailable + built.circuit.length)
      (strictMajorityThreshold runs) built.verdictWires
  have hcircuitLength :
      (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
        layout).length = built.circuit.length + thresholdFragment.length := by
    simp [amplifiedAcceptanceRawCircuit, built, thresholdFragment]
  have houtputWire :
      amplifiedAcceptanceOutputWire tm runs T n primaryAvailable layout =
        primaryAvailable + built.circuit.length + thresholdFragment.length - 1 := by
    simpa [amplifiedAcceptanceOutputWire, built, thresholdFragment] using
      (CircuitCode.Threshold.outputWire_eq_internal
        (primaryAvailable + built.circuit.length)
        (strictMajorityThreshold runs) built.verdictWires)
  have houtputIndex :
      input.toList.length +
          (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
            layout).length - 1 =
        amplifiedAcceptanceOutputWire tm runs T n primaryAvailable layout := by
    rw [BitString.length_toList, hcircuitLength, houtputWire]
    omega
  have hnonempty :
      (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
        layout).isEmpty = false := by
    simp [amplifiedAcceptanceRawCircuit, CircuitCode.Threshold.compileRaw]
  rw [CircuitCode.RawCircuit.eval?]
  simp only [hnonempty, Bool.false_eq_true, ite_false, wires, heval]
  rw [houtputIndex]
  exact houtput

/-- Under the canonical flattened-seed layout, raw evaluation returns the
threshold predicate over the named canonical acceptance-bit vector. -/
theorem eval?_canonicalAmplifiedAcceptanceRawCircuit_internal
    (tm : NTM k) (runs T n : ℕ) [NeZero (runs * T + n)]
    (seed : BitString (runs * T)) (x : BitString n) :
    CircuitCode.RawCircuit.eval?
        (canonicalAmplifiedAcceptanceRawCircuit tm runs T n)
        (BitString.toList (Fin.append seed x)) =
      some (decide (strictMajorityThreshold runs ≤
        Fin.countP (canonicalAcceptanceBits tm runs T x seed))) := by
  have hdata : ∀ j,
      (Fin.append seed x) ((prefixParallelInputWires runs T n).data j) =
        x j := by
    intro j
    have hwire :
        (prefixParallelInputWires runs T n).data j =
          Fin.natAdd (runs * T) j := by
      apply Fin.ext
      simp
    rw [hwire, Fin.append_right]
  have hchoices : ∀ j t,
      (Fin.append seed x)
          ((prefixParallelInputWires runs T n).choice j t) =
        parallelChoiceBlocks runs T seed j t := by
    intro j t
    have hwire :
        (prefixParallelInputWires runs T n).choice j t =
          Fin.castAdd n (finProdFinEquiv (j, t)) := by
      apply Fin.ext
      rfl
    rw [hwire, Fin.append_left]
    rfl
  simpa [canonicalAmplifiedAcceptanceRawCircuit, canonicalAcceptanceBits]
    using
      (eval?_amplifiedAcceptanceRawCircuit_internal tm runs T n
        (runs * T + n) (prefixParallelInputWires runs T n) x
        (parallelChoiceBlocks runs T seed) (Fin.append seed x) hdata hchoices)

end CircuitUnrolling

end Complexity

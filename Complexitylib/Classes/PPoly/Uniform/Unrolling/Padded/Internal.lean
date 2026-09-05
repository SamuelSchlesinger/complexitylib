/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded.Defs

/-!
# Regularly padded deterministic unrolling families -- proof internals

The padding proof separates three facts: the direct tableau fits its closed
cubic budget, constant gates remain topological at every later frontier, and
the terminal copy reads the original acceptance wire through the dead padding.
-/


public section

namespace Complexity

namespace TM

theorem directUnrollingRawCircuit_length_le_gateBound_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.directUnrollingRawCircuit f n).length ≤
      tm.directUnrollingGateBound f n := by
  exact CircuitUnrolling.length_acceptanceRawCircuit_le tm.toNTM (f n) n n
    (CircuitUnrolling.deterministicInputWires (f n) n)

theorem paddedDirectUnrollingRawCircuit_length_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.paddedDirectUnrollingRawCircuit f n).length =
      tm.directUnrollingGateBound f n + 1 := by
  have hbound := directUnrollingRawCircuit_length_le_gateBound_internal tm f n
  simp only [paddedDirectUnrollingRawCircuit, List.length_append,
    List.length_replicate, List.length_singleton]
  omega

private theorem replicate_constant_false_topologicallyWellFormed
    (available count : ℕ) (havailable : 0 < available) :
    CircuitCode.RawCircuit.TopologicallyWellFormed available
      (List.replicate count
        (CircuitCode.RawGate.constant 0 false)) := by
  intro i
  simp only [List.get_eq_getElem, List.getElem_replicate]
  simp [CircuitCode.RawGate.constant, CircuitCode.RawGate.WellFormedAt]
  omega

theorem paddedDirectUnrollingRawCircuit_wellFormed_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.paddedDirectUnrollingRawCircuit f n).WellFormed n := by
  let raw := tm.directUnrollingRawCircuit f n
  let bound := tm.directUnrollingGateBound f n
  let padding := List.replicate (bound - raw.length)
    (CircuitCode.RawGate.constant 0 false)
  have hraw : raw.WellFormed n := by
    exact CircuitUnrolling.acceptanceRawCircuit_wellFormed tm.toNTM
      (f n) n n (CircuitUnrolling.deterministicInputWires (f n) n)
  have hn : 0 < n := NeZero.pos n
  have hpadding : CircuitCode.RawCircuit.TopologicallyWellFormed
      (n + raw.length) padding := by
    exact replicate_constant_false_topologicallyWellFormed
      (n + raw.length) (bound - raw.length) (by omega)
  have hcopy :
      CircuitCode.RawCircuit.TopologicallyWellFormed
        (n + (raw ++ padding).length)
        [CircuitCode.RawGate.copy (n + raw.length - 1)] := by
    have hrawLength : 0 < raw.length := by
      have hne : raw.length ≠ 0 := by
        intro hzero
        exact hraw.1 (List.eq_nil_of_length_eq_zero hzero)
      omega
    simp only [CircuitCode.RawCircuit.TopologicallyWellFormed,
      List.length_singleton, List.get_eq_getElem, List.length_append,
      padding, List.length_replicate]
    simp [CircuitCode.RawGate.copy, CircuitCode.RawGate.WellFormedAt]
    omega
  constructor
  · simp [paddedDirectUnrollingRawCircuit]
  · change (raw ++ padding ++
      [CircuitCode.RawGate.copy (n + raw.length - 1)])
        |>.TopologicallyWellFormed n
    rw [CircuitCode.RawCircuit.topologicallyWellFormed_append]
    constructor
    · rw [CircuitCode.RawCircuit.topologicallyWellFormed_append]
      exact ⟨hraw.2, hpadding⟩
    · exact hcopy

private theorem eval?_append_dead_padding_copy
    (raw : CircuitCode.RawCircuit) (input : List Bool) (count : ℕ)
    (value : Bool) (hinput : 0 < input.length)
    (hraw : raw.WellFormed input.length)
    (heval : raw.eval? input = some value) :
    CircuitCode.RawCircuit.eval?
      (raw ++ List.replicate count
          (CircuitCode.RawGate.constant 0 false) ++
        [CircuitCode.RawGate.copy (input.length + raw.length - 1)]) input =
      some value := by
  have hrawNonempty : raw.isEmpty = false := by
    simpa [List.isEmpty_iff] using hraw.1
  cases hevalRaw : raw.evalAux? input.toArray with
  | none =>
      simp [CircuitCode.RawCircuit.eval?, hrawNonempty, hevalRaw] at heval
  | some rawWires =>
      have hrawSize : rawWires.size = input.length + raw.length :=
        CircuitCode.RawCircuit.evalAux?_size hevalRaw
      have houtputIndex : input.length + raw.length - 1 < rawWires.size := by
        rw [hrawSize]
        have hrawLength : 0 < raw.length := by
          have hne : raw.length ≠ 0 := by
            intro hzero
            exact hraw.1 (List.eq_nil_of_length_eq_zero hzero)
          omega
        omega
      have hrawOutput :
          rawWires[input.length + raw.length - 1]? = some value := by
        simpa [CircuitCode.RawCircuit.eval?, hrawNonempty, hevalRaw] using heval
      let padding := List.replicate count
        (CircuitCode.RawGate.constant 0 false)
      have hpaddingTopo :
          CircuitCode.RawCircuit.TopologicallyWellFormed rawWires.size
            padding := by
        exact replicate_constant_false_topologicallyWellFormed
          rawWires.size count (by omega)
      have hpaddingSome :
          (CircuitCode.RawCircuit.evalAux? padding rawWires).isSome :=
        (CircuitCode.RawCircuit.evalAux?_isSome_iff padding rawWires).2
          hpaddingTopo
      obtain ⟨paddedWires, hpaddingEval⟩ :=
        Option.isSome_iff_exists.mp hpaddingSome
      have hpaddedSize :
          paddedWires.size = rawWires.size + padding.length :=
        CircuitCode.RawCircuit.evalAux?_size hpaddingEval
      have hpaddedOutput :
          paddedWires[input.length + raw.length - 1]? = some value := by
        rw [CircuitCode.RawCircuit.evalAux?_preserves_prefix hpaddingEval
          houtputIndex]
        exact hrawOutput
      have hfullEval :
          CircuitCode.RawCircuit.evalAux?
              (raw ++ padding ++
                [CircuitCode.RawGate.copy
                  (input.length + raw.length - 1)]) input.toArray =
            some (paddedWires.push value) := by
        rw [CircuitCode.RawCircuit.evalAux?_append,
          CircuitCode.RawCircuit.evalAux?_append]
        simp only [hevalRaw, Option.bind_some, hpaddingEval]
        simp [CircuitCode.RawCircuit.evalAux?, CircuitCode.RawGate.copy,
          CircuitCode.RawGate.eval, hpaddedOutput]
      have hfullNonempty :
          (raw ++ padding ++
            [CircuitCode.RawGate.copy
              (input.length + raw.length - 1)]).isEmpty = false := by
        simp
      rw [CircuitCode.RawCircuit.eval?]
      rw [hfullNonempty]
      simp only [Bool.false_eq_true, ite_false]
      rw [hfullEval]
      have hlast :
          input.length +
              (raw ++ padding ++
                [CircuitCode.RawGate.copy
                  (input.length + raw.length - 1)]).length - 1 =
            paddedWires.size := by
        rw [List.length_append, List.length_append, List.length_singleton,
          hpaddedSize, hrawSize]
        omega
      rw [hlast]
      exact Array.getElem?_push_size

theorem paddedDirectUnrollingRawCircuit_eval?_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n]
    (x : BitString n) :
    (tm.paddedDirectUnrollingRawCircuit f n).eval? x.toList =
      some (CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false)) := by
  let choiceValue := x ⟨0, NeZero.pos n⟩
  let choices : BitString (f n) := fun _ => choiceValue
  have hrawEval := CircuitUnrolling.eval?_acceptanceRawCircuit tm.toNTM
    (f n) n n (CircuitUnrolling.deterministicInputWires (f n) n) x
    choices x (by intro i; rfl) (by intro i; rfl)
  have hirrel := tm.toNTM_trace_choice_irrel (f n)
    (tm.toNTM.initCfg x.toList) choices (fun _ => false)
  have hrawEval' :
      (tm.directUnrollingRawCircuit f n).eval? x.toList =
        some (CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
          (fun _ => false)) := by
    unfold CircuitUnrolling.boundedAcceptanceBit
    rw [hirrel] at hrawEval
    exact hrawEval
  have hrawWell :
      (tm.directUnrollingRawCircuit f n).WellFormed n :=
    CircuitUnrolling.acceptanceRawCircuit_wellFormed tm.toNTM (f n)
      n n (CircuitUnrolling.deterministicInputWires (f n) n)
  simpa [paddedDirectUnrollingRawCircuit] using
    eval?_append_dead_padding_copy (tm.directUnrollingRawCircuit f n)
      x.toList
      (tm.directUnrollingGateBound f n -
        (tm.directUnrollingRawCircuit f n).length)
      (CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false)) (by simpa using NeZero.pos n)
      (by simpa using hrawWell) hrawEval'

end TM

end Complexity

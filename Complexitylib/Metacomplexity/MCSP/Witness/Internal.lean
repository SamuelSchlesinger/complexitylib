/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Witness.Defs
import Complexitylib.Circuits.Encoding
import Complexitylib.Metacomplexity.MCSP.Internal

/-!
# Executable raw-circuit witnesses for MCSP -- proof internals

This module proves exact equivalence between finite raw-circuit witnesses and
the typed existential circuit semantics of MCSP.
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

theorem verifyRawCircuit_eq_true_iff_internal (inst : Instance) (code : List Bool) :
    inst.verifyRawCircuit code = true ↔ inst.IsRawCircuitWitness code := by
  simp [verifyRawCircuit]

theorem isRawCircuitWitness_encodeCircuit_internal (inst : Instance)
    [NeZero inst.arity] {internalGates : ℕ}
    (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates)
    (hsize : circuit.size ≤ inst.threshold)
    (hcomputes : circuit.Computes inst.function) :
    inst.IsRawCircuitWitness (CircuitCode.encodeCircuit circuit) := by
  simp only [IsRawCircuitWitness, NeZero.ne inst.arity, ite_false]
  change
    match CircuitCode.RawCircuit.decode?
        (CircuitCode.RawCircuit.ofCircuit circuit).encode with
    | none => False
    | some rawCircuit =>
        rawCircuit.WellFormed inst.arity ∧
          rawCircuit.length ≤ inst.threshold ∧
            ∀ index : Fin (2 ^ inst.arity),
              rawCircuit.eval? (inputOfIndex index).toList = some (inst.table index)
  rw [CircuitCode.RawCircuit.decode?_encode]
  refine ⟨CircuitCode.RawCircuit.ofCircuit_wellFormed circuit, ?_, ?_⟩
  · simpa [Circuit.size] using hsize
  · intro index
    rw [CircuitCode.RawCircuit.eval?_ofCircuit circuit (inputOfIndex index)]
    congr 1
    calc
      (circuit.eval (inputOfIndex index)) 0 = inst.function (inputOfIndex index) :=
        congrFun hcomputes (inputOfIndex index)
      _ = inst.table index := function_inputOfIndex_internal inst index

theorem hasCircuitAtMost_of_isRawCircuitWitness_internal (inst : Instance)
    [NeZero inst.arity] {code : List Bool}
    (hwitness : inst.IsRawCircuitWitness code) : inst.HasCircuitAtMost := by
  simp only [IsRawCircuitWitness, NeZero.ne inst.arity, ite_false] at hwitness
  cases hdecode : CircuitCode.RawCircuit.decode? code with
  | none => simp [hdecode] at hwitness
  | some rawCircuit =>
      simp only [hdecode] at hwitness
      obtain ⟨hwell, hsize, hsemantics⟩ := hwitness
      simp only [HasCircuitAtMost, NeZero.ne inst.arity, dite_false]
      refine
        ⟨rawCircuit.length - 1, rawCircuit.toCircuit inst.arity hwell, ?_, ?_⟩
      · rw [CircuitCode.RawCircuit.size_toCircuit]
        exact hsize
      · funext input
        have hwitnessInput := hsemantics (inputIndex input)
        rw [inputOfIndex_inputIndex_internal input] at hwitnessInput
        have heval := CircuitCode.RawCircuit.eval?_toCircuit
          inst.arity rawCircuit hwell input
        rw [hwitnessInput] at heval
        change
          ((rawCircuit.toCircuit inst.arity hwell).eval input) 0 =
            inst.table (inputIndex input)
        exact (Option.some.inj heval).symm

theorem exists_isRawCircuitWitness_iff_internal (inst : Instance) :
    (∃ code, inst.IsRawCircuitWitness code) ↔ inst.HasCircuitAtMost := by
  by_cases harity : inst.arity = 0
  · simp [IsRawCircuitWitness, HasCircuitAtMost, harity]
  · let : NeZero inst.arity := ⟨harity⟩
    constructor
    · rintro ⟨code, hwitness⟩
      exact hasCircuitAtMost_of_isRawCircuitWitness_internal inst hwitness
    · intro hsmall
      simp only [HasCircuitAtMost, harity, dite_false] at hsmall
      obtain ⟨internalGates, circuit, hsize, hcomputes⟩ := hsmall
      exact ⟨CircuitCode.encodeCircuit circuit,
        isRawCircuitWitness_encodeCircuit_internal inst circuit hsize hcomputes⟩

theorem isRawCircuitWitness_withThreshold_mono_internal (inst : Instance)
    {first second : ℕ} (hthreshold : first ≤ second) {code : List Bool}
    (hwitness : (inst.withThreshold first).IsRawCircuitWitness code) :
    (inst.withThreshold second).IsRawCircuitWitness code := by
  by_cases harity : inst.arity = 0
  · simpa [withThreshold, IsRawCircuitWitness, harity] using hwitness
  · simp only [withThreshold, IsRawCircuitWitness, harity, ite_false] at hwitness ⊢
    cases hdecode : CircuitCode.RawCircuit.decode? code with
    | none => simp [hdecode] at hwitness
    | some circuit =>
        simp only [hdecode] at hwitness ⊢
        exact ⟨hwitness.1, hwitness.2.1.trans hthreshold, hwitness.2.2⟩

theorem isRawCircuitWitness_length_le_internal (inst : Instance) {code : List Bool}
    (hwitness : inst.IsRawCircuitWitness code) :
    code.length ≤ inst.rawWitnessCodeLengthBound := by
  by_cases harity : inst.arity = 0
  · simp [IsRawCircuitWitness, harity] at hwitness
    simp [hwitness, rawWitnessCodeLengthBound]
  · simp only [IsRawCircuitWitness, harity, ite_false] at hwitness
    cases hdecode : CircuitCode.RawCircuit.decode? code with
    | none => simp [hdecode] at hwitness
    | some circuit =>
        simp only [hdecode] at hwitness
        obtain ⟨hwell, hsize, _⟩ := hwitness
        have hcode :=
          (CircuitCode.RawCircuit.decode?_eq_some_iff code circuit).mp hdecode
        rw [hcode]
        apply (CircuitCode.RawCircuit.encode_length_le inst.arity circuit.length
          circuit rfl hwell.2).trans
        unfold rawWitnessCodeLengthBound
        have hfactor :
            2 * (inst.arity + circuit.length) + 6 ≤
              2 * (inst.arity + inst.threshold) + 6 := by
          omega
        calc
          circuit.length + 1 +
                circuit.length * (2 * (inst.arity + circuit.length) + 5) =
              1 + circuit.length * (2 * (inst.arity + circuit.length) + 6) := by
            ring
          _ ≤ 1 + inst.threshold * (2 * (inst.arity + inst.threshold) + 6) :=
            Nat.add_le_add_left (Nat.mul_le_mul hsize hfactor) 1

theorem exists_isRawCircuitWitness_length_le_internal (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.IsRawCircuitWitness code ∧ code.length ≤ inst.rawWitnessCodeLengthBound := by
  by_cases harity : inst.arity = 0
  · refine ⟨[], ?_, ?_⟩
    · simp [IsRawCircuitWitness, harity]
    · simp [rawWitnessCodeLengthBound]
  · let : NeZero inst.arity := ⟨harity⟩
    simp only [HasCircuitAtMost, harity, dite_false] at hsmall
    obtain ⟨internalGates, circuit, hsize, hcomputes⟩ := hsmall
    refine ⟨CircuitCode.encodeCircuit circuit,
      isRawCircuitWitness_encodeCircuit_internal inst circuit hsize hcomputes, ?_⟩
    apply (CircuitCode.encodeCircuit_length_le_size circuit).trans
    unfold rawWitnessCodeLengthBound
    have hfactor :
        2 * (inst.arity + circuit.size) + 6 ≤
          2 * (inst.arity + inst.threshold) + 6 := by
      omega
    exact Nat.add_le_add_left (Nat.mul_le_mul hsize hfactor) 1

end Instance

end MCSP

end Complexity

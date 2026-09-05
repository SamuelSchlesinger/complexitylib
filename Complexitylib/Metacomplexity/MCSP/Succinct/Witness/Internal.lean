/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.Witness.Defs
import Complexitylib.Circuits.Encoding
import Complexitylib.Metacomplexity.MCSP.Succinct.Internal

/-!
# Executable raw-circuit witnesses for SuccinctMCSP -- proof internals

This module proves exact equivalence between the executable raw witness
relation and the typed sampled-circuit semantics.
-/


public section

namespace Complexity

namespace SuccinctMCSP

namespace Instance

theorem verifyRawCircuit_eq_true_iff_internal (inst : Instance)
    (code : List Bool) :
    inst.verifyRawCircuit code = true ↔ inst.IsRawCircuitWitness code := by
  simp [verifyRawCircuit]

theorem isRawCircuitWitness_encodeCircuit_internal (inst : Instance)
    [NeZero inst.arity] {internalGates : ℕ}
    (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates)
    (hsize : circuit.size ≤ inst.threshold)
    (hsamples : inst.SamplesFunction (fun input => circuit.eval input 0)) :
    inst.IsRawCircuitWitness (CircuitCode.encodeCircuit circuit) := by
  simp only [IsRawCircuitWitness, NeZero.ne inst.arity, ite_false]
  change
    match CircuitCode.RawCircuit.decode?
        (CircuitCode.RawCircuit.ofCircuit circuit).encode with
    | none => False
    | some rawCircuit =>
        rawCircuit.WellFormed inst.arity ∧
          rawCircuit.length ≤ inst.threshold ∧
            inst.samples.Forall fun sample =>
              rawCircuit.eval? sample.input.toList = some sample.output
  rw [CircuitCode.RawCircuit.decode?_encode]
  refine ⟨CircuitCode.RawCircuit.ofCircuit_wellFormed circuit, ?_, ?_⟩
  · simpa [Circuit.size] using hsize
  · rw [List.forall_iff_forall_mem]
    intro sample hsample
    rw [CircuitCode.RawCircuit.eval?_ofCircuit circuit sample.input]
    exact congrArg some (hsamples sample hsample)

theorem hasCircuitAtMost_of_isRawCircuitWitness_internal (inst : Instance)
    [NeZero inst.arity] {code : List Bool}
    (hwitness : inst.IsRawCircuitWitness code) : inst.HasCircuitAtMost := by
  simp only [IsRawCircuitWitness, NeZero.ne inst.arity, ite_false] at hwitness
  cases hdecode : CircuitCode.RawCircuit.decode? code with
  | none => simp [hdecode] at hwitness
  | some rawCircuit =>
      simp only [hdecode] at hwitness
      obtain ⟨hwell, hsize, hsemantics⟩ := hwitness
      rw [hasCircuitAtMost_iff_exists_circuit_internal]
      refine ⟨rawCircuit.length - 1,
        rawCircuit.toCircuit inst.arity hwell, ?_, ?_⟩
      · rw [CircuitCode.RawCircuit.size_toCircuit]
        exact hsize
      · intro sample hsample
        have hwitnessInput :=
          (List.forall_iff_forall_mem.mp hsemantics) sample hsample
        have heval := CircuitCode.RawCircuit.eval?_toCircuit
          inst.arity rawCircuit hwell sample.input
        rw [hwitnessInput] at heval
        exact (Option.some.inj heval).symm

theorem exists_isRawCircuitWitness_iff_internal (inst : Instance) :
    (∃ code, inst.IsRawCircuitWitness code) ↔ inst.HasCircuitAtMost := by
  by_cases harity : inst.arity = 0
  · constructor
    · rintro ⟨code, hwitness⟩
      simp only [IsRawCircuitWitness, harity, ite_true] at hwitness
      cases code with
      | nil => simp at hwitness
      | cons output rest =>
          cases rest with
          | nil =>
              apply
                (hasCircuitAtMost_of_arity_eq_zero_iff_internal
                  inst harity).mpr
              refine ⟨output, ?_⟩
              simpa [SamplesFunction, Sample.MatchesFunction,
                List.forall_iff_forall_mem] using hwitness
          | cons next rest => simp at hwitness
    · intro hsmall
      obtain ⟨output, hsamples⟩ :=
        (hasCircuitAtMost_of_arity_eq_zero_iff_internal inst harity).mp hsmall
      refine ⟨[output], ?_⟩
      simp only [IsRawCircuitWitness, harity, ite_true]
      simpa [SamplesFunction, Sample.MatchesFunction,
        List.forall_iff_forall_mem] using hsamples
  · let : NeZero inst.arity := ⟨harity⟩
    constructor
    · rintro ⟨code, hwitness⟩
      exact hasCircuitAtMost_of_isRawCircuitWitness_internal inst hwitness
    · intro hsmall
      obtain ⟨internalGates, circuit, hsize, hsamples⟩ :=
        (hasCircuitAtMost_iff_exists_circuit_internal inst).mp hsmall
      exact ⟨CircuitCode.encodeCircuit circuit,
        isRawCircuitWitness_encodeCircuit_internal
          inst circuit hsize hsamples⟩

theorem isRawCircuitWitness_threshold_mono_internal (inst : Instance)
    {first second : ℕ} (hthreshold : first ≤ second) {code : List Bool}
    (hwitness :
      ({ inst with threshold := first } : Instance).IsRawCircuitWitness code) :
    ({ inst with threshold := second } : Instance).IsRawCircuitWitness code := by
  by_cases harity : inst.arity = 0
  · simpa [IsRawCircuitWitness, harity] using hwitness
  · simp only [IsRawCircuitWitness, harity, ite_false] at hwitness ⊢
    cases hdecode : CircuitCode.RawCircuit.decode? code with
    | none => simp [hdecode] at hwitness
    | some circuit =>
        simp only [hdecode] at hwitness ⊢
        exact ⟨hwitness.1, hwitness.2.1.trans hthreshold, hwitness.2.2⟩

theorem isRawCircuitWitness_length_le_internal (inst : Instance)
    {code : List Bool} (hwitness : inst.IsRawCircuitWitness code) :
    code.length ≤ inst.rawWitnessCodeLengthBound := by
  by_cases harity : inst.arity = 0
  · simp only [IsRawCircuitWitness, harity, ite_true] at hwitness
    cases code with
    | nil => simp at hwitness
    | cons output rest =>
        cases rest with
        | nil => simp [rawWitnessCodeLengthBound]
        | cons next rest => simp at hwitness
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
              1 + circuit.length *
                (2 * (inst.arity + circuit.length) + 6) := by
            ring
          _ ≤ 1 + inst.threshold *
              (2 * (inst.arity + inst.threshold) + 6) :=
            Nat.add_le_add_left (Nat.mul_le_mul hsize hfactor) 1

theorem exists_isRawCircuitWitness_length_le_internal (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.IsRawCircuitWitness code ∧
        code.length ≤ inst.rawWitnessCodeLengthBound := by
  obtain ⟨code, hwitness⟩ :=
    (exists_isRawCircuitWitness_iff_internal inst).mpr hsmall
  exact ⟨code, hwitness,
    isRawCircuitWitness_length_le_internal inst hwitness⟩

end Instance

end SuccinctMCSP

end Complexity

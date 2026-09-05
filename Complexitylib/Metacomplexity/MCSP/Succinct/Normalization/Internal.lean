/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.Normalization.Defs
import Complexitylib.Circuits.Encoding.Formula
import Complexitylib.Circuits.Encoding.Formula.Batch
import Complexitylib.Metacomplexity.MCSP.Succinct.Internal
import Complexitylib.Metacomplexity.MCSP.Succinct.Witness.Internal
import Mathlib.Data.Bool.AllAny
import Mathlib.Tactic.Ring

/-!
# Threshold normalization for SuccinctMCSP -- proof internals

The main construction is a DNF formula containing one exact-input term for
each positive sample. Consistency supplied by any existing witness ensures
that this formula also rejects every negative sample.
-/


public section

namespace Complexity

namespace SuccinctMCSP

private def Sample.inputFormula {arity : ℕ} (sample : Sample arity) :
    BoolFormula :=
  BoolFormula.conjs
    (List.ofFn fun index : Fin arity =>
      BoolFormula.literal index.val (sample.input index))

private def Instance.interpolatingFormula (inst : Instance) : BoolFormula :=
  BoolFormula.disjs
    ((inst.samples.filter fun sample => sample.output).map Sample.inputFormula)

private theorem Sample.eval_inputFormula {arity : ℕ}
    (sample : Sample arity) (input : BitString arity) :
    sample.inputFormula.eval input.toTotal = decide (input = sample.input) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [Sample.inputFormula, BoolFormula.eval_conjs, List.all_eq_true,
    List.forall_mem_ofFn_iff, BoolFormula.eval_literal, decide_eq_true_eq,
    BitString.toTotal_apply]
  constructor
  · intro h
    funext index
    exact h index
  · rintro rfl index
    rfl

private theorem Sample.size_inputFormula_le {arity : ℕ}
    (sample : Sample arity) :
    sample.inputFormula.size ≤ 1 + 3 * arity := by
  let formulas :=
    List.ofFn fun index : Fin arity =>
      BoolFormula.literal index.val (sample.input index)
  change (BoolFormula.conjs formulas).size ≤ 1 + 3 * arity
  rw [BoolFormula.size_conjs]
  have hsum :
      (formulas.map fun formula => formula.size + 1).sum ≤
        formulas.length * 3 := by
    calc
      (formulas.map fun formula => formula.size + 1).sum ≤
          (formulas.map fun _ => 3).sum := by
        apply List.sum_le_sum
        intro formula hformula
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hformula
        have hsize := BoolFormula.size_literal_le_two
          index.val (sample.input index)
        omega
      _ = formulas.length * 3 := by simp
  have hlength : formulas.length = arity := by simp [formulas]
  omega

private theorem BoolFormula.vars_conjs_lt (formulas : List BoolFormula)
    (bound : ℕ)
    (hformulas : ∀ formula ∈ formulas, ∀ index ∈ formula.vars,
      index < bound) :
    ∀ index ∈ (BoolFormula.conjs formulas).vars, index < bound := by
  induction formulas with
  | nil => simp [BoolFormula.conjs, BoolFormula.vars]
  | cons formula formulas ih =>
      intro index hindex
      simp only [BoolFormula.conjs, BoolFormula.vars,
        Finset.mem_union] at hindex
      rcases hindex with hindex | hindex
      · exact hformulas formula (by simp) index hindex
      · apply ih
        · intro found hfound
          exact hformulas found (by simp [hfound])
        · exact hindex

private theorem BoolFormula.vars_disjs_lt (formulas : List BoolFormula)
    (bound : ℕ)
    (hformulas : ∀ formula ∈ formulas, ∀ index ∈ formula.vars,
      index < bound) :
    ∀ index ∈ (BoolFormula.disjs formulas).vars, index < bound := by
  induction formulas with
  | nil => simp [BoolFormula.disjs, BoolFormula.vars]
  | cons formula formulas ih =>
      intro index hindex
      simp only [BoolFormula.disjs, BoolFormula.vars,
        Finset.mem_union] at hindex
      rcases hindex with hindex | hindex
      · exact hformulas formula (by simp) index hindex
      · apply ih
        · intro found hfound
          exact hformulas found (by simp [hfound])
        · exact hindex

private theorem Sample.vars_inputFormula_lt {arity : ℕ}
    (sample : Sample arity) :
    ∀ index ∈ sample.inputFormula.vars, index < arity := by
  apply BoolFormula.vars_conjs_lt
  intro formula hformula index hindex
  obtain ⟨position, rfl⟩ := List.mem_ofFn.mp hformula
  cases hvalue : sample.input position <;>
    simp [BoolFormula.literal, hvalue, BoolFormula.vars] at hindex
  all_goals subst index; exact position.isLt

private theorem Instance.vars_interpolatingFormula_lt (inst : Instance) :
    ∀ index ∈ inst.interpolatingFormula.vars, index < inst.arity := by
  apply BoolFormula.vars_disjs_lt
  intro formula hformula
  obtain ⟨sample, _, rfl⟩ := List.mem_map.mp hformula
  exact sample.vars_inputFormula_lt

private theorem Instance.eval_interpolatingFormula_of_samplesFunction
    (inst : Instance) (f : BitString inst.arity → Bool)
    (hsamples : inst.SamplesFunction f) {sample : Sample inst.arity}
    (hsample : sample ∈ inst.samples) :
    inst.interpolatingFormula.eval sample.input.toTotal = sample.output := by
  rw [Instance.interpolatingFormula, BoolFormula.eval_disjs]
  cases houtput : sample.output with
  | false =>
      rw [List.any_eq_false]
      intro formula hformula
      obtain ⟨positive, hpositive, rfl⟩ := List.mem_map.mp hformula
      rw [Sample.eval_inputFormula, decide_eq_true_eq]
      intro hinputs
      have hpositiveData := List.mem_filter.mp hpositive
      have hpositiveValue := hsamples positive hpositiveData.1
      have hsampleValue := hsamples sample hsample
      apply Bool.false_ne_true
      calc
        false = sample.output := houtput.symm
        _ = f sample.input := hsampleValue.symm
        _ = f positive.input := congrArg f hinputs
        _ = positive.output := hpositiveValue
        _ = true := hpositiveData.2
  | true =>
      rw [List.any_eq_true]
      refine ⟨sample.inputFormula, ?_, ?_⟩
      · exact List.mem_map.mpr
          ⟨sample, List.mem_filter.mpr ⟨hsample, houtput⟩, rfl⟩
      · rw [Sample.eval_inputFormula, decide_eq_true_eq]

private theorem Instance.size_interpolatingFormula_le (inst : Instance) :
    inst.interpolatingFormula.size ≤ inst.trivialCircuitSizeBound := by
  let positives := inst.samples.filter fun sample => sample.output
  let formulas := positives.map Sample.inputFormula
  change (BoolFormula.disjs formulas).size ≤ inst.trivialCircuitSizeBound
  rw [BoolFormula.size_disjs]
  have hsum :
      (formulas.map fun formula => formula.size + 1).sum ≤
        formulas.length * (3 * inst.arity + 2) := by
    calc
      (formulas.map fun formula => formula.size + 1).sum ≤
          (formulas.map fun _ => 3 * inst.arity + 2).sum := by
        apply List.sum_le_sum
        intro formula hformula
        obtain ⟨sample, _, rfl⟩ := List.mem_map.mp hformula
        have hsize := sample.size_inputFormula_le
        omega
      _ = formulas.length * (3 * inst.arity + 2) := by simp
  have hlength : formulas.length ≤ inst.samples.length := by
    simp only [formulas, positives, List.length_map]
    induction inst.samples with
    | nil => simp
    | cons sample samples ih =>
        cases houtput : sample.output <;>
          simp [List.filter, houtput] <;> omega
  have hmul := Nat.mul_le_mul_right (3 * inst.arity + 2) hlength
  unfold trivialCircuitSizeBound
  omega

private theorem BoolFormula.eval?_compileRaw (available : ℕ)
    [NeZero available] (formula : BoolFormula) (assignment : ℕ → Bool)
    (input : List Bool) (hinputLength : input.length = available)
    (hinput : ∀ index < available, input[index]? = some (assignment index))
    (hvars : ∀ index ∈ formula.vars, index < available) :
    (BoolFormula.compileRaw available formula).eval? input =
      some (formula.eval assignment) := by
  have harraySize : input.toArray.size = available := by
    simp [hinputLength]
  have harrayInput :
      ∀ index < available,
        input.toArray[index]? = some (assignment index) := by
    intro index hindex
    simpa only [List.getElem?_toArray] using hinput index hindex
  obtain ⟨result, heval, _, _, houtput⟩ :=
    BoolFormula.evalAux?_compileRaw available formula assignment
      input.toArray harraySize harrayInput hvars
  have hnonempty : BoolFormula.compileRaw available formula ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [BoolFormula.length_compileRaw, List.length_nil] at hlength
    have hpositive := formula.one_le_size
    omega
  unfold CircuitCode.RawCircuit.eval?
  simp only [List.isEmpty_iff, hnonempty, ↓reduceIte, heval]
  simpa [hinputLength, BoolFormula.length_compileRaw,
    BoolFormula.rawOutputWire] using houtput

namespace Instance

theorem hasCircuitAtMost_trivialCircuitSizeBound_internal (inst : Instance)
    (hsmall : inst.HasCircuitAtMost) :
    ({ inst with threshold := inst.trivialCircuitSizeBound } : Instance).HasCircuitAtMost := by
  by_cases harity : inst.arity = 0
  · unfold HasCircuitAtMost at hsmall ⊢
    rw [dite_eq_left harity] at hsmall ⊢
    exact hsmall
  · let : NeZero inst.arity := ⟨harity⟩
    obtain ⟨_, circuit, _, hsamples⟩ :=
      (hasCircuitAtMost_iff_exists_circuit_internal inst).mp hsmall
    apply (exists_isRawCircuitWitness_iff_internal
      ({ inst with threshold := inst.trivialCircuitSizeBound } : Instance)).mp
    let formula := inst.interpolatingFormula
    let rawCircuit := BoolFormula.compileRaw inst.arity formula
    refine ⟨rawCircuit.encode, ?_⟩
    simp only [IsRawCircuitWitness, harity, ite_false]
    change
      match CircuitCode.RawCircuit.decode? rawCircuit.encode with
      | none => False
      | some decoded =>
          decoded.WellFormed inst.arity ∧
            decoded.length ≤ inst.trivialCircuitSizeBound ∧
              inst.samples.Forall fun sample =>
                decoded.eval? sample.input.toList = some sample.output
    rw [CircuitCode.RawCircuit.decode?_encode]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro hempty
        have hlength := congrArg List.length hempty
        simp only [rawCircuit, BoolFormula.length_compileRaw,
          List.length_nil] at hlength
        have hpositive := formula.one_le_size
        omega
      · apply BoolFormula.topologicallyWellFormed_compileRaw
        exact inst.vars_interpolatingFormula_lt
    · simpa [rawCircuit, formula] using
        inst.size_interpolatingFormula_le
    · rw [List.forall_iff_forall_mem]
      intro sample hsample
      calc
        rawCircuit.eval? sample.input.toList =
            some (formula.eval sample.input.toTotal) := by
          apply BoolFormula.eval?_compileRaw
          · simp
          · intro index hindex
            rw [List.getElem?_eq_getElem (by simpa using hindex)]
            congr 1
            simpa [BitString.toTotal_of_lt sample.input index hindex] using
              BitString.getElem_toList sample.input ⟨index, hindex⟩
          · exact inst.vars_interpolatingFormula_lt
        _ = some sample.output := congrArg some
          (inst.eval_interpolatingFormula_of_samplesFunction
            (fun input => circuit.eval input 0) hsamples hsample)

theorem effectiveThreshold_le_threshold_internal (inst : Instance) :
    inst.effectiveThreshold ≤ inst.threshold := by
  exact min_le_left _ _

theorem effectiveThreshold_le_trivialCircuitSizeBound_internal
    (inst : Instance) :
    inst.effectiveThreshold ≤ inst.trivialCircuitSizeBound := by
  exact min_le_right _ _

theorem hasCircuitAtMost_normalizeThreshold_iff_internal (inst : Instance) :
    inst.normalizeThreshold.HasCircuitAtMost ↔ inst.HasCircuitAtMost := by
  constructor
  · intro hnormalized
    apply hasCircuitAtMost_threshold_mono_internal inst
      (effectiveThreshold_le_threshold_internal inst)
    simpa [normalizeThreshold] using hnormalized
  · intro hsmall
    by_cases hthreshold : inst.threshold ≤ inst.trivialCircuitSizeBound
    · simpa [normalizeThreshold, effectiveThreshold,
        min_eq_left hthreshold] using hsmall
    · have hbound : inst.trivialCircuitSizeBound ≤ inst.threshold := by
        omega
      have htrivial :=
        hasCircuitAtMost_trivialCircuitSizeBound_internal inst hsmall
      simpa [normalizeThreshold, effectiveThreshold,
        min_eq_right hbound] using htrivial

theorem trivialCircuitSizeBound_le_encodeLength_internal (inst : Instance) :
    inst.trivialCircuitSizeBound ≤ inst.encode.length := by
  have hfactor : 3 * inst.arity + 2 ≤ 4 * inst.arity + 8 := by
    omega
  have hproduct := Nat.mul_le_mul_left inst.samples.length hfactor
  rw [length_encode_internal]
  unfold trivialCircuitSizeBound
  omega

theorem rawWitnessLengthPolynomial_polyBound_internal :
    PolyBound rawWitnessLengthPolynomial := by
  have hfactor :
      PolyBound (fun inputLength => 4 * inputLength + 6) :=
    ((PolyBound.const 4).mul PolyBound.id).add (PolyBound.const 6)
  have htotal := (PolyBound.const 1).add (PolyBound.id.mul hfactor)
  exact htotal

theorem exists_normalizedRawWitness_length_le_encode_internal
    (inst : Instance) (hsmall : inst.HasCircuitAtMost) :
    ∃ code,
      inst.normalizeThreshold.IsRawCircuitWitness code ∧
        code.length ≤ rawWitnessLengthPolynomial inst.encode.length := by
  by_cases hsamples : inst.samples = []
  · by_cases harity : inst.arity = 0
    · refine ⟨[false], ?_, ?_⟩
      · simp [normalizeThreshold, IsRawCircuitWitness, harity, hsamples]
      · simp [rawWitnessLengthPolynomial]
    · let : NeZero inst.arity := ⟨harity⟩
      obtain ⟨_, circuit, hsize, _⟩ :=
        (hasCircuitAtMost_iff_exists_circuit_internal inst).mp hsmall
      have hthreshold : 1 ≤ inst.threshold := by
        rw [Circuit.size] at hsize
        omega
      have heffective : inst.effectiveThreshold = 1 := by
        simp [effectiveThreshold, trivialCircuitSizeBound, hsamples,
          min_eq_right hthreshold]
      let rawCircuit : CircuitCode.RawCircuit :=
        [CircuitCode.RawGate.constant 0 false]
      refine ⟨rawCircuit.encode, ?_, ?_⟩
      · simp only [IsRawCircuitWitness, normalizeThreshold, harity,
          ite_false]
        change
          match CircuitCode.RawCircuit.decode? rawCircuit.encode with
          | none => False
          | some decoded =>
              decoded.WellFormed inst.arity ∧
                decoded.length ≤ inst.effectiveThreshold ∧
                  inst.samples.Forall fun sample =>
                    decoded.eval? sample.input.toList = some sample.output
        rw [CircuitCode.RawCircuit.decode?_encode]
        refine ⟨?_, ?_, ?_⟩
        · have harityPositive : 0 < inst.arity := Nat.pos_of_ne_zero harity
          simpa [rawCircuit, CircuitCode.RawCircuit.WellFormed,
            CircuitCode.RawCircuit.TopologicallyWellFormed,
            CircuitCode.RawGate.WellFormedAt,
            CircuitCode.RawGate.constant] using harityPositive
        · simp [rawCircuit, heffective]
        · simp [hsamples]
      · have hinputLength : 1 ≤ inst.encode.length := by
          rw [length_encode_internal]
          omega
        have hcodeLength : rawCircuit.encode.length = 7 := by
          simp [rawCircuit, CircuitCode.RawCircuit.encode,
            CircuitCode.RawGate.encode, CircuitCode.RawGate.constant,
            CircuitCode.RawGate.opBit, CircuitCode.NatCode.encode]
        rw [hcodeLength]
        unfold rawWitnessLengthPolynomial
        have hfactor : 6 ≤ 4 * inst.encode.length + 6 := by omega
        have hproduct := Nat.mul_le_mul hinputLength hfactor
        omega
  · have hnormalized : inst.normalizeThreshold.HasCircuitAtMost :=
      (hasCircuitAtMost_normalizeThreshold_iff_internal inst).mpr hsmall
    obtain ⟨code, hwitness, hcode⟩ :=
      exists_isRawCircuitWitness_length_le_internal
        inst.normalizeThreshold hnormalized
    refine ⟨code, hwitness, hcode.trans ?_⟩
    have hcount : 1 ≤ inst.samples.length :=
      Nat.one_le_iff_ne_zero.mpr fun hzero =>
        hsamples (List.length_eq_zero_iff.mp hzero)
    have hfactorCount :=
      Nat.mul_le_mul_right (4 * inst.arity + 8) hcount
    have harityProduct :
        inst.arity ≤ inst.samples.length * (4 * inst.arity + 8) := by
      calc
        inst.arity ≤ 4 * inst.arity + 8 := by omega
        _ = 1 * (4 * inst.arity + 8) := by simp
        _ ≤ inst.samples.length * (4 * inst.arity + 8) := hfactorCount
    have harityLength : inst.arity ≤ inst.encode.length := by
      rw [length_encode_internal]
      omega
    have heffectiveLength :
        inst.effectiveThreshold ≤ inst.encode.length :=
      (effectiveThreshold_le_trivialCircuitSizeBound_internal inst).trans
        (trivialCircuitSizeBound_le_encodeLength_internal inst)
    have hfactor :
        2 * (inst.arity + inst.effectiveThreshold) + 6 ≤
          4 * inst.encode.length + 6 := by
      omega
    have hproduct := Nat.mul_le_mul heffectiveLength hfactor
    simpa [rawWitnessCodeLengthBound, rawWitnessLengthPolynomial,
      normalizeThreshold] using Nat.add_le_add_left hproduct 1

end Instance

theorem rawWitnessRelation_polyBalanced_internal :
    PolyBalanced RawWitnessRelation := by
  obtain ⟨polynomial, hpolynomial⟩ :=
    Instance.rawWitnessLengthPolynomial_polyBound_internal
  refine ⟨polynomial, ?_⟩
  intro bits witness hrelation
  cases hdecode : Instance.decode? bits with
  | none => simp [RawWitnessRelation, hdecode] at hrelation
  | some inst =>
      simp only [RawWitnessRelation, hdecode] at hrelation
      exact hrelation.2.trans (hpolynomial bits.length)

theorem mem_iff_exists_rawWitnessRelation_internal (bits : List Bool) :
    bits ∈ Complexity.SuccinctMCSP ↔
      ∃ witness, RawWitnessRelation bits witness := by
  cases hdecode : Instance.decode? bits with
  | none => simp [Complexity.SuccinctMCSP, RawWitnessRelation, hdecode]
  | some inst =>
      simp only [Complexity.SuccinctMCSP, RawWitnessRelation, hdecode,
      Set.mem_ofPred_eq]
      constructor
      · intro hsmall
        have hcanonical :=
          (Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
        rw [hcanonical]
        exact Instance.exists_normalizedRawWitness_length_le_encode_internal
          inst hsmall
      · rintro ⟨witness, hwitness, _⟩
        have hnormalized : inst.normalizeThreshold.HasCircuitAtMost :=
          (Instance.exists_isRawCircuitWitness_iff_internal
            inst.normalizeThreshold).mp ⟨witness, hwitness⟩
        exact
          (Instance.hasCircuitAtMost_normalizeThreshold_iff_internal inst).mp
            hnormalized

end SuccinctMCSP

end Complexity

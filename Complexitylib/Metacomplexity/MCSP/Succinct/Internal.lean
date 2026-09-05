/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.Defs

/-!
# Succinct MCSP -- proof internals

This module proves exactness of the nested sampled-instance codec and the
basic semantic facts used by the public `SuccinctMCSP` interface.
-/


public section

namespace Complexity

namespace SuccinctMCSP

namespace Sample

theorem matchesFunction_ofFunction_internal {arity : ℕ}
    (f : BitString arity → Bool) (input : BitString arity) :
    (ofFunction f input).MatchesFunction f := by
  rfl

theorem decode?_encode_internal {arity : ℕ} (sample : Sample arity) :
    decode? arity sample.encode = some sample := by
  rcases sample with ⟨input, output⟩
  simp [decode?, encode]

theorem decode?_eq_some_iff_internal {arity : ℕ}
    (bits : List Bool) (sample : Sample arity) :
    decode? arity bits = some sample ↔ bits = sample.encode := by
  constructor
  · intro hdecode
    cases hpair : unpair? bits with
    | none => simp [decode?, hpair] at hdecode
    | some components =>
        rcases components with ⟨inputBits, outputBits⟩
        by_cases hinput : inputBits.length = arity
        · cases outputBits with
          | nil => simp [decode?, hpair, hinput] at hdecode
          | cons output rest =>
              cases rest with
              | nil =>
                  have hbits := eq_pair_of_unpair?_eq_some hpair
                  simp [decode?, hpair, hinput] at hdecode
                  cases hdecode
                  simpa [encode] using hbits
              | cons next rest =>
                  simp [decode?, hpair, hinput] at hdecode
        · simp [decode?, hpair, hinput] at hdecode
  · rintro rfl
    exact decode?_encode_internal sample

theorem length_encode_internal {arity : ℕ} (sample : Sample arity) :
    sample.encode.length = 2 * arity + 3 := by
  simp [encode]

end Sample

theorem decodeSamples?_encodeSamples_internal {arity : ℕ}
    (samples : List (Sample arity)) :
    decodeSamples? arity samples.length (encodeSamples samples) = some samples := by
  induction samples with
  | nil => rfl
  | cons sample samples ih =>
      simp [decodeSamples?, encodeSamples, Sample.decode?_encode_internal, ih]

theorem decodeSamples?_eq_some_iff_internal {arity count : ℕ}
    (bits : List Bool) (samples : List (Sample arity)) :
    decodeSamples? arity count bits = some samples ↔
      samples.length = count ∧ bits = encodeSamples samples := by
  constructor
  · intro hdecode
    induction count generalizing bits samples with
    | zero =>
        cases bits with
        | nil =>
            simp [decodeSamples?] at hdecode
            cases hdecode
            simp [encodeSamples]
        | cons bit bits =>
            simp [decodeSamples?] at hdecode
    | succ count ih =>
        cases hpair : unpair? bits with
        | none => simp [decodeSamples?, hpair] at hdecode
        | some components =>
            rcases components with ⟨sampleBits, rest⟩
            cases hsample : Sample.decode? arity sampleBits with
            | none => simp [decodeSamples?, hpair, hsample] at hdecode
            | some sample =>
                cases hrest : decodeSamples? arity count rest with
                | none =>
                    simp [decodeSamples?, hpair, hsample, hrest] at hdecode
                | some decoded =>
                    have hsamples : sample :: decoded = samples := by
                      simpa [decodeSamples?, hpair, hsample, hrest] using hdecode
                    subst samples
                    have hsampleBits :=
                      (Sample.decode?_eq_some_iff_internal sampleBits sample).mp
                        hsample
                    obtain ⟨hcount, hrestBits⟩ := ih rest decoded hrest
                    constructor
                    · simp [hcount]
                    · calc
                        bits = pair sampleBits rest :=
                          eq_pair_of_unpair?_eq_some hpair
                        _ = pair sample.encode (encodeSamples decoded) := by
                          rw [hsampleBits, hrestBits]
                        _ = encodeSamples (sample :: decoded) := rfl
  · rintro ⟨hcount, rfl⟩
    subst count
    exact decodeSamples?_encodeSamples_internal samples

theorem length_encodeSamples_internal {arity : ℕ}
    (samples : List (Sample arity)) :
    (encodeSamples samples).length = samples.length * (4 * arity + 8) := by
  induction samples with
  | nil => simp [encodeSamples]
  | cons sample samples ih =>
      simp [encodeSamples, Sample.length_encode_internal, ih, Nat.add_mul]
      omega

namespace Instance

theorem samplesFunction_ofInputs_internal {arity threshold : ℕ}
    (f : BitString arity → Bool) (inputs : List (BitString arity)) :
    (ofInputs threshold f inputs).SamplesFunction f := by
  change ∀ sample ∈ inputs.map (Sample.ofFunction f),
    f sample.input = sample.output
  induction inputs with
  | nil => simp
  | cons input inputs ih =>
      intro sample hsample
      simp only [List.map_cons, List.mem_cons] at hsample
      rcases hsample with hsample | hsample
      · simp [hsample, Sample.ofFunction]
      · exact ih sample hsample

theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨arity, samples, threshold⟩
  simp [decode?, encode, decodeSamples?_encodeSamples_internal]

theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases harityPair : unpair? bits with
    | none => simp [decode?, harityPair] at hdecode
    | some arityPair =>
        rcases arityPair with ⟨arityBits, outerRest⟩
        cases hthresholdPair : unpair? outerRest with
        | none => simp [decode?, harityPair, hthresholdPair] at hdecode
        | some thresholdPair =>
            rcases thresholdPair with ⟨thresholdBits, innerRest⟩
            cases hcountPair : unpair? innerRest with
            | none =>
                simp [decode?, harityPair, hthresholdPair, hcountPair] at hdecode
            | some countPair =>
                rcases countPair with ⟨countBits, sampleBits⟩
                cases harity : BinaryNatCode.decode? arityBits with
                | none =>
                    simp [decode?, harityPair, hthresholdPair, harity] at hdecode
                | some arity =>
                    cases hthreshold : BinaryNatCode.decode? thresholdBits with
                    | none =>
                        simp [decode?, harityPair, hthresholdPair, hcountPair,
                          harity, hthreshold] at hdecode
                    | some threshold =>
                        cases hcount : BinaryNatCode.decode? countBits with
                        | none =>
                            simp [decode?, harityPair, hthresholdPair, hcountPair,
                              harity, hthreshold, hcount] at hdecode
                        | some count =>
                            cases hsamples : decodeSamples? arity count sampleBits with
                            | none =>
                                simp [decode?, harityPair, hthresholdPair,
                                  hcountPair, harity, hthreshold, hcount,
                                  hsamples] at hdecode
                            | some samples =>
                                have hbits :=
                                  eq_pair_of_unpair?_eq_some harityPair
                                have hthresholdRest :=
                                  eq_pair_of_unpair?_eq_some hthresholdPair
                                have hcountRest :=
                                  eq_pair_of_unpair?_eq_some hcountPair
                                have harityCode :=
                                  (BinaryNatCode.decode?_eq_some_iff
                                    arityBits arity).mp harity
                                have hthresholdCode :=
                                  (BinaryNatCode.decode?_eq_some_iff
                                    thresholdBits threshold).mp hthreshold
                                have hcountCode :=
                                  (BinaryNatCode.decode?_eq_some_iff
                                    countBits count).mp hcount
                                obtain ⟨hsampleCount, hsampleBits⟩ :=
                                  (decodeSamples?_eq_some_iff_internal
                                    sampleBits samples).mp hsamples
                                simp [decode?, harityPair, hthresholdPair,
                                  hcountPair, harity, hthreshold, hcount,
                                  hsamples] at hdecode
                                cases hdecode
                                calc
                                  bits = pair arityBits outerRest := hbits
                                  _ = pair arityBits
                                      (pair thresholdBits innerRest) := by
                                        rw [hthresholdRest]
                                  _ = pair arityBits
                                      (pair thresholdBits
                                        (pair countBits sampleBits)) := by
                                          rw [hcountRest]
                                  _ = pair (BinaryNatCode.encode arity)
                                      (pair (BinaryNatCode.encode threshold)
                                        (pair (BinaryNatCode.encode count)
                                          sampleBits)) := by
                                            rw [harityCode, hthresholdCode,
                                              hcountCode]
                                  _ = pair (BinaryNatCode.encode arity)
                                      (pair (BinaryNatCode.encode threshold)
                                        (pair
                                          (BinaryNatCode.encode samples.length)
                                          (encodeSamples samples))) := by
                                            rw [hsampleCount, hsampleBits]
                                  _ = encode
                                      { arity
                                        samples
                                        threshold } := rfl
  · rintro rfl
    exact decode?_encode_internal inst

theorem decode?_eq_none_iff_internal (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode := by
  constructor
  · intro hnone ⟨inst, hbits⟩
    rw [hbits, decode?_encode_internal] at hnone
    contradiction
  · intro hnoncanonical
    cases hdecode : decode? bits with
    | none => rfl
    | some inst =>
        exact (hnoncanonical
          ⟨inst, (decode?_eq_some_iff_internal bits inst).mp hdecode⟩).elim

theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

theorem length_encode_internal (inst : Instance) :
    inst.encode.length =
      inst.samples.length * (4 * inst.arity + 8) +
        2 * inst.arity.size + 2 * inst.threshold.size +
          2 * inst.samples.length.size + 6 := by
  simp [encode, BinaryNatCode.length_encode, length_encodeSamples_internal]
  omega

theorem hasCircuitAtMost_of_arity_eq_zero_iff_internal (inst : Instance)
    (harity : inst.arity = 0) :
    inst.HasCircuitAtMost ↔
      ∃ output : Bool, inst.SamplesFunction (fun _ => output) := by
  simp [HasCircuitAtMost, harity]

theorem hasCircuitAtMost_iff_exists_circuit_internal (inst : Instance)
    [NeZero inst.arity] :
    inst.HasCircuitAtMost ↔
      ∃ (internalGates : ℕ)
          (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates),
        circuit.size ≤ inst.threshold ∧
          inst.SamplesFunction (fun input => circuit.eval input 0) := by
  simp [HasCircuitAtMost, NeZero.ne inst.arity]

theorem hasCircuitAtMost_threshold_mono_internal (inst : Instance)
    {first second : ℕ} (hthreshold : first ≤ second)
    (hsmall : ({ inst with threshold := first } : Instance).HasCircuitAtMost) :
    ({ inst with threshold := second } : Instance).HasCircuitAtMost := by
  by_cases harity : inst.arity = 0
  · simpa [HasCircuitAtMost, harity, Instance.SamplesFunction] using hsmall
  · simp only [HasCircuitAtMost, harity, dite_false] at hsmall ⊢
    obtain ⟨internalGates, circuit, hsize, hsamples⟩ := hsmall
    exact ⟨internalGates, circuit, hsize.trans hthreshold, hsamples⟩

end Instance

end SuccinctMCSP

end Complexity

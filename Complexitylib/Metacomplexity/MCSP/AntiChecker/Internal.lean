/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Defs
import Complexitylib.Metacomplexity.MCSP.Succinct.Internal

/-!
# Finite anti-checkers -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem isFor_iff_forall_not_agreesOn_internal {arity : ℕ}
    [NeZero arity] (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) :
    IsFor target threshold inputs ↔
      ∀ (internalGates : ℕ)
          (circuit : Circuit Basis.andOr2 arity 1 internalGates),
        circuit.size ≤ threshold → ¬ AgreesOn circuit target inputs := by
  constructor
  · intro hanti internalGates circuit hsize hagrees
    obtain ⟨input, hinput, hdisagrees⟩ := hanti internalGates circuit hsize
    exact hdisagrees (hagrees input hinput)
  · intro hanti internalGates circuit hsize
    by_contra hmissing
    apply hanti internalGates circuit hsize
    intro input hinput
    by_contra hdisagrees
    exact hmissing ⟨input, hinput, hdisagrees⟩

theorem isFor_inputs_mono_internal {arity : ℕ} [NeZero arity]
    {target : BitString arity → Bool} {threshold : ℕ}
    {first second : List (BitString arity)}
    (hsub : ∀ input ∈ first, input ∈ second)
    (hanti : IsFor target threshold first) :
    IsFor target threshold second := by
  intro internalGates circuit hsize
  obtain ⟨input, hinput, hdisagrees⟩ :=
    hanti internalGates circuit hsize
  exact ⟨input, hsub input hinput, hdisagrees⟩

theorem isFor_threshold_anti_internal {arity : ℕ} [NeZero arity]
    {target : BitString arity → Bool} {first second : ℕ}
    {inputs : List (BitString arity)} (hthreshold : first ≤ second)
    (hanti : IsFor target second inputs) :
    IsFor target first inputs := by
  intro internalGates circuit hsize
  exact hanti internalGates circuit (hsize.trans hthreshold)

theorem isFor_perm_internal {arity : ℕ} [NeZero arity]
    {target : BitString arity → Bool} {threshold : ℕ}
    {first second : List (BitString arity)} (hperm : first.Perm second) :
    IsFor target threshold first ↔ IsFor target threshold second := by
  constructor
  · apply isFor_inputs_mono_internal
    intro input hinput
    exact hperm.mem_iff.mp hinput
  · apply isFor_inputs_mono_internal
    intro input hinput
    exact hperm.mem_iff.mpr hinput

theorem length_padInputsTo_internal {arity targetLength : ℕ}
    {inputs : List (BitString arity)} (hlength : inputs.length ≤ targetLength) :
    (padInputsTo targetLength inputs).length = targetLength := by
  simp [padInputsTo]
  omega

theorem mem_padInputsTo_of_mem_internal {arity targetLength : ℕ}
    {inputs : List (BitString arity)} {input : BitString arity}
    (hinput : input ∈ inputs) :
    input ∈ padInputsTo targetLength inputs := by
  simp [padInputsTo, hinput]

theorem IsFor.padInputsTo_internal {arity threshold targetLength : ℕ}
    [NeZero arity] {target : BitString arity → Bool}
    {inputs : List (BitString arity)} (hanti : IsFor target threshold inputs) :
    IsFor target threshold (padInputsTo targetLength inputs) := by
  apply isFor_inputs_mono_internal (hanti := hanti)
  intro input hinput
  exact mem_padInputsTo_of_mem_internal hinput

theorem samplesFunction_ofInputs_iff_agreesOn_internal {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) {internalGates : ℕ}
    (circuit : Circuit Basis.andOr2 arity 1 internalGates) :
    (SuccinctMCSP.Instance.ofInputs threshold target inputs).SamplesFunction
        (fun input => circuit.eval input 0) ↔
      AgreesOn circuit target inputs := by
  constructor
  · intro hsamples input hinput
    have hsample :
        SuccinctMCSP.Sample.ofFunction target input ∈
          (SuccinctMCSP.Instance.ofInputs threshold target inputs).samples := by
      exact List.mem_map.mpr ⟨input, hinput, rfl⟩
    exact hsamples (SuccinctMCSP.Sample.ofFunction target input) hsample
  · intro hagrees sample hsample
    change sample ∈ inputs.map (SuccinctMCSP.Sample.ofFunction target) at hsample
    obtain ⟨input, hinput, hsample⟩ := List.mem_map.mp hsample
    simp [← hsample, SuccinctMCSP.Sample.MatchesFunction,
      SuccinctMCSP.Sample.ofFunction, hagrees input hinput]

theorem isFor_iff_not_hasCircuitAtMost_internal {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    IsFor target threshold inputs ↔
      ¬ (SuccinctMCSP.Instance.ofInputs threshold target inputs).HasCircuitAtMost := by
  let : NeZero
      (SuccinctMCSP.Instance.ofInputs threshold target inputs).arity :=
    ⟨by exact NeZero.ne arity⟩
  rw [isFor_iff_forall_not_agreesOn_internal,
    SuccinctMCSP.Instance.hasCircuitAtMost_iff_exists_circuit_internal]
  constructor
  · intro hanti hsmall
    obtain ⟨internalGates, circuit, hsize, hsamples⟩ := hsmall
    exact (hanti internalGates circuit hsize)
      ((samplesFunction_ofInputs_iff_agreesOn_internal
        target inputs circuit).mp hsamples)
  · intro hnot internalGates circuit hsize hagrees
    apply hnot
    exact ⟨internalGates, circuit, hsize,
      (samplesFunction_ofInputs_iff_agreesOn_internal
        target inputs circuit).mpr hagrees⟩

theorem encode_not_mem_iff_isFor_internal {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    (SuccinctMCSP.Instance.ofInputs threshold target inputs).encode ∉
        Complexity.SuccinctMCSP ↔
      IsFor target threshold inputs := by
  rw [isFor_iff_not_hasCircuitAtMost_internal]
  simp [Complexity.SuccinctMCSP,
    SuccinctMCSP.Instance.decode?_encode_internal]

end AntiChecker

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Asymptotics
public import Complexitylib.SAT.Tseitin
public import Complexitylib.SAT.Tseitin.Machine.Internal.EmitterSpec
public import Complexitylib.SAT.Tseitin.Machine.Internal.InvalidBranchSpec
public import Complexitylib.SAT.Tseitin.Machine.Internal.ValidBranchAssembly
public import Complexitylib.SAT.Tseitin.Machine.Internal.Validation

/-!
# Polynomial-time correctness of the Tseitin reduction machine

This module combines the typed valid-input controller proof with the fixed
malformed-input fallback. The decoder decides which execution theorem applies,
and both branches fit one explicit quartic budget depending only on the input
bit length.

## Main results

- `reductionMachineTime`
- `reductionMachineTime_le_quartic_internal`
- `reductionMachineTime_bigO_quartic_internal`
- `reductionTM_computesInTime_internal`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- One uniform time allowance for validation, branching, and the streaming
Tseitin controller. -/
def reductionMachineTime (n : ℕ) : ℕ :=
  6 * n + 16384 * (n + 2) ^ 4 + 49

/-- The explicit running-time allowance is bounded pointwise by one shifted
quartic monomial. -/
theorem reductionMachineTime_le_quartic_internal (n : ℕ) :
    reductionMachineTime n ≤ 16439 * (n + 2) ^ 4 := by
  have hbase : n + 2 ≤ (n + 2) ^ 4 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ n + 2) (by omega : 1 ≤ 4)
  have hone : 1 ≤ (n + 2) ^ 4 := Nat.one_le_pow 4 (n + 2) (by omega)
  unfold reductionMachineTime
  omega

/-- In the standard asymptotic convention, the uniform allowance is
`O(n⁴)`. -/
theorem reductionMachineTime_bigO_quartic_internal :
    Complexity.BigO reductionMachineTime ((· ^ 4) : ℕ → ℕ) := by
  unfold Complexity.BigO
  apply Asymptotics.IsBigO.of_bound 1327159
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnPow : n ≤ n ^ 4 := by
    simpa using Nat.pow_le_pow_right hn (by omega : 1 ≤ 4)
  have honePow : 1 ≤ n ^ 4 := Nat.one_le_pow 4 n hn
  have hshift : n + 2 ≤ 3 * n := by omega
  have hshiftPow : (n + 2) ^ 4 ≤ 81 * n ^ 4 := by
    calc
      (n + 2) ^ 4 ≤ (3 * n) ^ 4 := Nat.pow_le_pow_left hshift 4
      _ = 81 * n ^ 4 := by ring
  have htime : reductionMachineTime n ≤ 1327159 * n ^ 4 := by
    unfold reductionMachineTime
    omega
  simpa only [Real.norm_natCast] using (show
    ((reductionMachineTime n : ℕ) : ℝ) ≤
      (1327159 : ℝ) * ((n ^ 4 : ℕ) : ℝ) by exact_mod_cast htime)

/-- The concrete machine computes the total encoded Tseitin reduction within
the uniform quartic allowance on every bit string. -/
theorem reductionTM_computesInTime_internal :
    reductionTM.ComputesInTime ThreeSAT.reduction reductionMachineTime := by
  intro z
  cases hdecode : CNF.decode? z with
  | none =>
      have hvalid : validEncoding z = false := by
        rw [validEncoding_eq_decode?_isSome_internal, hdecode]
        rfl
      obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
        reductionTMWith_invalid_reachesIn_internal validEmitterTM z hvalid
      refine ⟨c', t, ?_, ?_, ?_, ?_⟩
      · exact ht.trans (by
          unfold reductionMachineTime
          omega)
      · simpa only [reductionTM] using hreach
      · simpa only [reductionTM] using hhalt
      · simpa only [ThreeSAT.reduction, hdecode] using hout
  | some phi =>
      have hz : z = phi.encode := CNF.decode?_sound hdecode
      subst z
      have hvalid : validEncoding phi.encode = true := by
        rw [validEncoding_eq_decode?_isSome_internal]
        simp
      have hpostTransition : ∀ inp work out,
          StreamingStatePred (framedTokenInput phi.tokens [])
              (validEmitterFinalState phi) inp work out →
            StreamingStatePred (framedTokenInput phi.tokens [])
              (validEmitterFinalState phi) (TM.transitionInput inp)
              (fun i => TM.transitionTape (work i))
              (TM.transitionTape out) := by
        simpa only [StreamingStatePred, BufferPred] using
          (TM.emitPred_transition
            (framedTokenInput_parked phi.tokens [])
            (BufferValues.ofStreaming_work_parked
              (validEmitterFinalState phi))
            (encodeTokens (validEmitterFinalState phi).emitted))
      have hvalidRun :=
        reductionTMWith_valid_hoareTime_internal validEmitterTM phi.encode
          hvalid (validEmitterTM_hoareTime_quartic_internal phi)
          hpostTransition
      obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
        hvalidRun (Tape.init (phi.encode.map Γ.ofBool))
          (fun _ => Tape.init []) (Tape.init [])
          ⟨rfl, fun _ => rfl, rfl⟩
      refine ⟨c', t, ?_, ?_, ?_, ?_⟩
      · exact ht.trans (by
          unfold reductionMachineTime
          omega)
      · simpa only [reductionTM] using hreach
      · simpa only [reductionTM] using hhalt
      · simpa [validEmitterFinalState, ThreeSAT.reduction] using
          (StreamingStatePred.outAcc hpost).hasOutput

end Machine

end ThreeSAT

end SAT

end Complexity

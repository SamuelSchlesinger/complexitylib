/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Circuit.Defs
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.Majority
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Internal
import Complexitylib.Metacomplexity.MCSP.Internal

/-!
# Good-string circuit bridge -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem exists_survivorCodeCircuit_internal {arity : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (code : SurvivorCode target threshold inputs) :
    ∃ internalGates,
      ∃ circuit : Circuit Basis.andOr2 arity 1 internalGates,
        circuit.size ≤ threshold ∧
          ∀ input,
            (circuit.eval input) 0 =
              survivorCodeOutput target threshold inputs code input := by
  have hcandidate : code.1 ∈ candidateCodes arity threshold :=
    (Finset.mem_filter.mp code.2).1
  have hsmall := (mem_candidateCodes_iff_internal.mp hcandidate).2
  unfold IsSmallCircuitCode at hsmall
  cases hdecode : CircuitCode.RawCircuit.decode? code.1 with
  | none => simp [hdecode] at hsmall
  | some rawCircuit =>
      simp only [hdecode] at hsmall
      obtain ⟨hwell, hsize⟩ := hsmall
      refine
        ⟨rawCircuit.length - 1,
          rawCircuit.toCircuit arity hwell, ?_, ?_⟩
      · rw [CircuitCode.RawCircuit.size_toCircuit]
        exact hsize
      · intro input
        have hbridge := CircuitCode.RawCircuit.eval?_toCircuit
          arity rawCircuit hwell input
        have hevalCode :
            CircuitCode.evalCode arity code.1 input.toList =
              some (((rawCircuit.toCircuit arity hwell).eval input) 0) := by
          simp [CircuitCode.evalCode, BitString.length_toList, hdecode,
            hbridge]
        unfold survivorCodeOutput
        rw [hevalCode]
        simp

theorem exists_survivorTupleMajorityCircuit_internal
    {arity : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (tuple : Fin arity → SurvivorCode target threshold inputs) :
    ∃ internalGates,
      ∃ circuit : Circuit Basis.andOr2 arity 1 internalGates,
        circuit.size ≤ survivorTupleMajoritySizeBound arity threshold ∧
          ∀ input,
            (circuit.eval input) 0 =
              majority (fun i =>
                survivorCodeOutput target threshold inputs (tuple i) input) := by
  classical
  have hexists (i : Fin arity) :=
    exists_survivorCodeCircuit_internal target threshold inputs (tuple i)
  let selectedGates (i : Fin arity) : ℕ :=
    Classical.choose (hexists i)
  let selectedCircuit (i : Fin arity) :
      Circuit Basis.andOr2 arity 1 (selectedGates i) :=
    Classical.choose (Classical.choose_spec (hexists i))
  have hselected (i : Fin arity) :
      (selectedCircuit i).size ≤ threshold ∧
        ∀ input,
          ((selectedCircuit i).eval input) 0 =
            survivorCodeOutput target threshold inputs (tuple i) input :=
    Classical.choose_spec (Classical.choose_spec (hexists i))
  let circuits : Fin arity →
      Σ internalGates, Circuit Basis.andOr2 arity 1 internalGates :=
    fun i => ⟨selectedGates i, selectedCircuit i⟩
  obtain ⟨packedGates, packed, hpackedSize, hpackedEval⟩ :=
    Circuit.exists_parallelFamily circuits
  have hpackedSizeLe : packed.size ≤ arity * threshold := by
    rw [hpackedSize]
    calc
      (∑ i, ((circuits i).2).size) ≤ ∑ _i : Fin arity, threshold := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [circuits] using (hselected i).1
      _ = arity * threshold := by simp
  let majorityCircuit := Circuit.strictMajority arity
  refine
    ⟨_, majorityCircuit.compose packed, ?_, ?_⟩
  · dsimp only [majorityCircuit]
    calc
      ((Circuit.strictMajority arity).compose packed).size =
          packed.size + (Circuit.strictMajority arity).size :=
        Circuit.size_compose (Circuit.strictMajority arity) packed
      _ = packed.size +
          (3 + 2 * arity * CircuitCode.strictMajorityThreshold arity) := by
        rw [Circuit.size_strictMajority]
      _ ≤ survivorTupleMajoritySizeBound arity threshold := by
        unfold survivorTupleMajoritySizeBound
        exact Nat.add_le_add_right hpackedSizeLe _
  · intro input
    dsimp only [majorityCircuit]
    have hcompose := congrFun
      (Circuit.eval_compose (Circuit.strictMajority arity) packed input) 0
    rw [hcompose]
    change
      (majorityCircuit.eval (packed.eval input)) 0 =
        majority (fun i =>
          survivorCodeOutput target threshold inputs (tuple i) input)
    rw [Circuit.eval_strictMajority]
    have hpackedOutput :
        packed.eval input = fun i =>
          survivorCodeOutput target threshold inputs (tuple i) input := by
      funext i
      rw [hpackedEval]
      exact (hselected i).2 input
    rw [hpackedOutput, finCountP_eq_popCount]
    unfold CircuitCode.strictMajorityThreshold majority
    exact decide_eq_decide.mpr (by omega)

theorem everySurvivorTupleCaught_of_circuitHardness_internal
    {arity threshold hardnessThreshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool)
    (inputs : List (BitString arity))
    (hfits :
      survivorTupleMajoritySizeBound arity threshold ≤ hardnessThreshold)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity hardnessThreshold target).HasCircuitAtMost) :
    EverySurvivorTupleCaught target threshold inputs := by
  apply everySurvivorTupleCaught_of_no_majorityComputes_internal
  intro tuple hmajority
  obtain ⟨internalGates, circuit, hsize, heval⟩ :=
    exists_survivorTupleMajorityCircuit_internal
      target threshold inputs tuple
  apply hhard
  have harity :
      (MCSP.Instance.ofFunction arity hardnessThreshold target).arity ≠ 0 := by
    simpa [MCSP.Instance.ofFunction] using NeZero.ne arity
  unfold MCSP.Instance.HasCircuitAtMost
  rw [dite_eq_right harity]
  refine ⟨internalGates, circuit, hsize.trans hfits, ?_⟩
  unfold Circuit.Computes
  rw [MCSP.Instance.function_ofFunction_internal]
  funext input
  exact (heval input).trans (hmajority input)

end AntiChecker

end Complexity

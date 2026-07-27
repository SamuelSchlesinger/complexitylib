/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Defs
public import Complexitylib.Classes.PPoly.Unrolling
public import Complexitylib.Models.TuringMachine.Internal

/-!
# Streamable deterministic unrolling families — proof internals

This module proves that the direct raw family has the same deterministic trace
semantics and cubic size bound as the fixed-choice family, while exposing an
exact positive-length serialization theorem.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

@[simp] theorem deterministicInputWires_choice_val_internal
    (T n : ℕ) [NeZero n] (i : Fin T) :
    ((deterministicInputWires T n).choice i).val = 0 := rfl

@[simp] theorem deterministicInputWires_data_internal
    (T n : ℕ) [NeZero n] (i : Fin n) :
    (deterministicInputWires T n).data i = i := rfl

end CircuitUnrolling

namespace TM

/-- Internal semantics of the direct deterministic unrolling family. -/
theorem directUnrollingCircuitFamily_function_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) (x : BitString n) :
    (tm.directUnrollingCircuitFamily f).function n x =
      CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false) := by
  cases n with
  | zero =>
      have hx : x = fun i => Fin.elim0 i := Subsingleton.elim _ _
      subst x
      rfl
  | succ n =>
      rw [CircuitFamily.function_succ]
      change
        ((CircuitUnrolling.acceptanceCircuit tm.toNTM (f (n + 1))
          (n + 1) (n + 1)
          (CircuitUnrolling.deterministicInputWires (f (n + 1)) (n + 1))).eval x) 0 = _
      rw [CircuitUnrolling.acceptanceCircuit_eval tm.toNTM (f (n + 1))
        (n + 1) (n + 1)
        (CircuitUnrolling.deterministicInputWires (f (n + 1)) (n + 1))
        x (fun _ => x ⟨0, by omega⟩) x (by intro; rfl) (by intro; rfl)]
      unfold CircuitUnrolling.boundedAcceptanceBit
      rw [tm.toNTM_trace_choice_irrel (f (n + 1))
        (tm.toNTM.initCfg x.toList) (fun _ => x ⟨0, by omega⟩)
        (fun _ => false)]

/-- Internal exact positive-member serialization through the raw tableau. -/
theorem directUnrollingCircuitFamily_encodeAt_succ_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    (tm.directUnrollingCircuitFamily f).encodeAt (n + 1) =
      true :: (tm.directUnrollingRawCircuit f (n + 1)).encode := by
  rw [CircuitFamily.encodeAt_succ]
  change
    true :: CircuitCode.encodeCircuit
      (CircuitUnrolling.acceptanceCircuit tm.toNTM (f (n + 1))
        (n + 1) (n + 1)
        (CircuitUnrolling.deterministicInputWires (f (n + 1)) (n + 1))) = _
  congr 1
  unfold CircuitCode.encodeCircuit CircuitUnrolling.acceptanceCircuit
    directUnrollingRawCircuit
  rw [CircuitCode.RawCircuit.ofCircuit_toCircuit]

/-- Internal exact serialization theorem at every input length. -/
theorem directUnrollingCircuitFamily_encodeAt_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    (tm.directUnrollingCircuitFamily f).encodeAt n =
      tm.directUnrollingCode f n := by
  cases n with
  | zero => rfl
  | succ n =>
      exact tm.directUnrollingCircuitFamily_encodeAt_succ_internal f n

/-- Internal whole-language correctness of the direct deterministic family. -/
theorem DecidesInTime.directUnrollingCircuitFamily_decides_internal
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) :
    (tm.directUnrollingCircuitFamily f).Decides L := by
  rw [CircuitFamily.decides_iff]
  intro xs
  change
    (tm.directUnrollingCircuitFamily f).function xs.length xs.get = true ↔
      xs ∈ L
  rw [tm.directUnrollingCircuitFamily_function_internal f xs.length xs.get]
  simpa only [BitString.toList, List.ofFn_get] using
    hdec.boundedAcceptanceBit_iff xs.length xs.get (fun _ => false)

/-- Internal cubic size estimate for the direct deterministic family. -/
theorem directUnrollingCircuitFamily_size_bigO_internal
    (tm : TM k) {f : ℕ → ℕ} {d : ℕ}
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.directUnrollingCircuitFamily f).size =O
      ((· ^ (3 * d)) : ℕ → ℕ) := by
  have hshift : (fun n => f n + 2) =O ((· ^ d) : ℕ → ℕ) :=
    BigO.add hf (BigO.const_le_pow 2 d)
  have hcubeRaw := BigO.pow hshift 3
  have hcubePow : (fun n : ℕ => (n ^ d) ^ 3) =O
      ((· ^ (3 * d)) : ℕ → ℕ) := by
    apply BigO.of_le
    intro n
    apply le_of_eq
    rw [← pow_mul]
    congr 1
    omega
  have hbound :
      (fun n => CircuitUnrolling.acceptanceSizeCoeff tm.toNTM * (f n + 2) ^ 3) =O
        ((· ^ (3 * d)) : ℕ → ℕ) :=
    BigO.const_mul_left (CircuitUnrolling.acceptanceSizeCoeff tm.toNTM)
      (hcubeRaw.trans hcubePow)
  apply (CircuitFamily.SizeBoundedBy.bigO
    (F := tm.directUnrollingCircuitFamily f) ?_).trans hbound
  intro n
  cases n with
  | zero => simp
  | succ n =>
      rw [CircuitFamily.size_succ]
      change
        (CircuitUnrolling.acceptanceCircuit tm.toNTM (f (n + 1))
          (n + 1) (n + 1)
          (CircuitUnrolling.deterministicInputWires (f (n + 1)) (n + 1))).size ≤ _
      exact CircuitUnrolling.acceptanceCircuit_size_le tm.toNTM (f (n + 1))
        (n + 1) (n + 1)
        (CircuitUnrolling.deterministicInputWires (f (n + 1)) (n + 1))

end TM

end Complexity

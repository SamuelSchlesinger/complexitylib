/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.P
public import Complexitylib.Classes.PPoly
public import Complexitylib.Classes.PPoly.Unrolling.Defs

/-!
# Deterministic unrolling families — proof internals

This module proves exact semantics and polynomial size for the family obtained
by unrolling a deterministic machine. Public statements are exposed by
`Complexitylib.Classes.PPoly.Unrolling`.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Internal exact-horizon correctness of the bounded acceptance predicate for
a deterministic decider. -/
theorem DecidesInTime.boundedAcceptanceBit_iff_internal
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) (n : ℕ) (x : BitString n)
    (choices : BitString (f n)) :
    CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x choices = true ↔
      x.toList ∈ L := by
  have hdecx := hdec x.toList
  simp only [BitString.length_toList] at hdecx
  obtain ⟨c', t, hle, hreach, hhalt, hyes, hno⟩ := hdecx
  have htrace :
      tm.toNTM.trace (f n) choices (tm.toNTM.initCfg x.toList) = c' :=
    tm.toNTM_trace_of_reachesIn hreach hhalt hle choices
  unfold CircuitUnrolling.boundedAcceptanceBit
  rw [htrace, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hout⟩
    by_contra hx
    rw [hno hx] at hout
    cases hout
  · intro hx
    exact ⟨hhalt, hyes hx⟩

/-- Internal semantics of the deterministic unrolling family at every input
length, including the explicit length-zero member. -/
theorem unrollingCircuitFamily_function_internal
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) (x : BitString n) :
    (tm.unrollingCircuitFamily f).function n x =
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
        ((CircuitUnrolling.fixedChoicesAcceptanceCircuit tm.toNTM
          (f (n + 1)) (n + 1) (fun _ => false)).eval x) 0 = _
      exact CircuitUnrolling.fixedChoicesAcceptanceCircuit_eval
        tm.toNTM (f (n + 1)) (n + 1) (fun _ => false) x

/-- Internal fixed-length correctness theorem for a deterministic unrolling
family. -/
theorem DecidesInTime.unrollingCircuitFamily_function_iff_internal
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) (n : ℕ) (x : BitString n) :
    (tm.unrollingCircuitFamily f).function n x = true ↔ x.toList ∈ L := by
  rw [tm.unrollingCircuitFamily_function_internal f n x]
  exact hdec.boundedAcceptanceBit_iff_internal n x (fun _ => false)

/-- Internal whole-language correctness theorem for deterministic unrolling. -/
theorem DecidesInTime.unrollingCircuitFamily_decides_internal
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) :
    (tm.unrollingCircuitFamily f).Decides L := by
  rw [CircuitFamily.decides_iff]
  intro xs
  simpa only [CircuitFamily.evalList, BitString.toList, List.ofFn_get] using
    hdec.unrollingCircuitFamily_function_iff_internal xs.length xs.get

/-- Internal polynomial-size bound for a deterministic unrolling family. -/
theorem unrollingCircuitFamily_size_bigO_internal
    (tm : TM k) {f : ℕ → ℕ} {d : ℕ}
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.unrollingCircuitFamily f).size =O
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
  apply (CircuitFamily.SizeBoundedBy.bigO (F := tm.unrollingCircuitFamily f) ?_).trans
    hbound
  intro n
  cases n with
  | zero => simp
  | succ n =>
      rw [CircuitFamily.size_succ]
      change
        (CircuitUnrolling.fixedChoicesAcceptanceCircuit tm.toNTM
          (f (n + 1)) (n + 1) (fun _ => false)).size ≤ _
      exact CircuitUnrolling.fixedChoicesAcceptanceCircuit_size_le
        tm.toNTM (f (n + 1)) (n + 1) (fun _ => false)

/-- Internal packaging theorem: a polynomial-time deterministic decider yields
a polynomial-size nonuniform circuit family. -/
theorem DecidesInTime.mem_PPoly_internal
    {tm : TM k} {L : Language} {f : ℕ → ℕ} {d : ℕ}
    (hdec : tm.DecidesInTime L f)
    (hf : f =O ((· ^ d) : ℕ → ℕ)) : L ∈ PPoly := by
  rw [mem_PPoly_iff]
  exact ⟨tm.unrollingCircuitFamily f, 3 * d,
    hdec.unrollingCircuitFamily_decides_internal,
    tm.unrollingCircuitFamily_size_bigO_internal hf⟩

end TM

/-- Internal direct proof that deterministic polynomial time has nonuniform
polynomial-size circuits. -/
theorem P_subset_PPoly_internal : P ⊆ PPoly := by
  intro L hL
  obtain ⟨d, hL⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, f, hdec, hf⟩ := hL
  exact hdec.mem_PPoly_internal hf

end Complexity

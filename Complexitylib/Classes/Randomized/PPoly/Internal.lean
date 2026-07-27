/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly
public import Complexitylib.Classes.Randomized.PPoly.Defs

/-!
# Nonuniform derandomization — proof internals

This module proves correctness and polynomial size for the circuit family that
hardwires a uniformly correct amplified seed at each input length. Public
statements are exposed by `Complexitylib.Classes.Randomized.PPoly`.
-/

@[expose] public section

namespace Complexity

namespace NTM

/-- Internal specification of the chosen uniformly correct seed. -/
theorem uniformCorrectSeed_correct_internal (tm : NTM k) (L : Language)
    (f : ℕ → ℕ) (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) (n : ℕ)
    (x : BitString n) :
    blockMajority (tm.repeatAcceptEvent x.toList (f n))
        (tm.uniformCorrectSeed L f haccept hreject n) = true ↔
      x.toList ∈ L :=
  Classical.choose_spec (tm.exists_uniform_correct_seed L f haccept hreject n) x

/-- Internal fixed-length correctness theorem for the hardwired family. -/
theorem hardwiredAmplificationFamily_function_iff_internal
    (tm : NTM k) (L : Language) (f : ℕ → ℕ)
    (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) (n : ℕ)
    (x : BitString n) :
    (tm.hardwiredAmplificationFamily L f haccept hreject).function n x = true ↔
      x.toList ∈ L := by
  cases n with
  | zero =>
      simp [hardwiredAmplificationFamily, BitString.toList]
  | succ n =>
      rw [CircuitFamily.function_succ]
      change
        ((CircuitUnrolling.fixedSeedAmplifiedAcceptanceCircuit tm
          (uniformSeedRuns (n + 1)) (f (n + 1)) (n + 1)
          (tm.uniformCorrectSeed L f haccept hreject (n + 1))).eval x) 0 = true ↔
            x.toList ∈ L
      rw [CircuitUnrolling.fixedSeedAmplifiedAcceptanceCircuit_eval]
      exact tm.uniformCorrectSeed_correct_internal L f haccept hreject (n + 1) x

/-- Internal correctness theorem for the hardwired family. -/
theorem hardwiredAmplificationFamily_decides_internal
    (tm : NTM k) (L : Language) (f : ℕ → ℕ)
    (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3)) :
    (tm.hardwiredAmplificationFamily L f haccept hreject).Decides L := by
  rw [CircuitFamily.decides_iff]
  intro xs
  simpa only [CircuitFamily.evalList, BitString.toList,
    List.ofFn_get] using
      tm.hardwiredAmplificationFamily_function_iff_internal L f haccept hreject
        xs.length xs.get

/-- Internal polynomial-size accounting for the hardwired amplification
family. -/
theorem hardwiredAmplificationFamily_size_bigO_internal
    (tm : NTM k) (L : Language) {f : ℕ → ℕ} {d : ℕ}
    (haccept : tm.AcceptsWithProb L f (2 / 3))
    (hreject : tm.RejectsWithProb L f (1 / 3))
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.hardwiredAmplificationFamily L f haccept hreject).size =O
      ((· ^ (3 * d + 4)) : ℕ → ℕ) := by
  have hf' : f =O ((· ^ (d + 1)) : ℕ → ℕ) :=
    hf.trans (BigO.pow_le_pow_right (Nat.le_succ d))
  have hshift : (fun n => f n + 2) =O ((· ^ (d + 1)) : ℕ → ℕ) :=
    BigO.add hf' (BigO.const_le_pow 2 (d + 1))
  have hcubeRaw := BigO.pow hshift 3
  have hcubePow :
      (fun n : ℕ => (n ^ (d + 1)) ^ 3) =O
        ((· ^ (3 * (d + 1))) : ℕ → ℕ) := by
    apply BigO.of_le
    intro n
    apply le_of_eq
    rw [← pow_mul]
    congr 1
    omega
  have hcube : (fun n => (f n + 2) ^ 3) =O
      ((· ^ (3 * (d + 1))) : ℕ → ℕ) :=
    hcubeRaw.trans hcubePow
  have hn : (fun n : ℕ => n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun n : ℕ => n)
  have hn1 : (fun n : ℕ => n + 1) =O ((· ^ 1) : ℕ → ℕ) :=
    BigO.add hn (BigO.const_le_pow 1 1)
  have hruns : (fun n : ℕ => 12 * (n + 1) + 1) =O
      ((· ^ 1) : ℕ → ℕ) :=
    BigO.add (BigO.const_mul_left 12 hn1) (BigO.const_le_pow 1 1)
  have hmainRaw :
      (fun n => (12 * (n + 1) + 1) *
        (CircuitUnrolling.acceptanceSizeCoeff tm * (f n + 2) ^ 3)) =O
      (fun n => n ^ 1 * n ^ (3 * (d + 1))) :=
    BigO.mul hruns
      (BigO.const_mul_left (CircuitUnrolling.acceptanceSizeCoeff tm) hcube)
  have hmainPow : (fun n : ℕ => n ^ 1 * n ^ (3 * (d + 1))) =O
      ((· ^ (3 * d + 4)) : ℕ → ℕ) := by
    apply BigO.of_le
    intro n
    apply le_of_eq
    rw [← pow_add]
    congr 1
    omega
  have hmain := hmainRaw.trans hmainPow
  have hquadRaw :
      (fun n : ℕ => (12 * (n + 1) + 1) * (12 * (n + 1) + 1)) =O
        (fun n => n ^ 1 * n ^ 1) :=
    BigO.mul hruns hruns
  have hpowTwo : (fun n : ℕ => n ^ 1 * n ^ 1) =O
      ((· ^ 2) : ℕ → ℕ) := by
    apply BigO.of_le
    intro n
    apply le_of_eq
    rw [← pow_add]
  have hquadCore := hquadRaw.trans
    (hpowTwo.trans
      (BigO.pow_le_pow_right (j := 2) (k := 3 * d + 4) (by omega)))
  have hquad :
      (fun n : ℕ => 2 * (12 * (n + 1) + 1) * (12 * (n + 1) + 1)) =O
        ((· ^ (3 * d + 4)) : ℕ → ℕ) := by
    simpa only [mul_assoc] using BigO.const_mul_left 2 hquadCore
  have hconst : (fun _ : ℕ => 3) =O ((· ^ (3 * d + 4)) : ℕ → ℕ) :=
    BigO.const_le_pow 3 (3 * d + 4)
  have hbound :
      (fun n =>
        let runs := 12 * (n + 1) + 1
        runs * (CircuitUnrolling.acceptanceSizeCoeff tm * (f n + 2) ^ 3) + 3 +
          2 * runs * runs) =O ((· ^ (3 * d + 4)) : ℕ → ℕ) :=
    BigO.add (BigO.add hmain hconst) hquad
  apply (CircuitFamily.SizeBoundedBy.bigO (F :=
    tm.hardwiredAmplificationFamily L f haccept hreject) ?_).trans hbound
  intro n
  cases n with
  | zero => simp
  | succ n =>
      rw [CircuitFamily.size_succ]
      change
        (CircuitUnrolling.fixedSeedAmplifiedAcceptanceCircuit tm
          (NTM.uniformSeedRuns (n + 1)) (f (n + 1)) (n + 1)
          (tm.uniformCorrectSeed L f haccept hreject (n + 1))).size ≤ _
      simpa only [NTM.uniformSeedRuns] using
        CircuitUnrolling.fixedSeedAmplifiedAcceptanceCircuit_size_le tm
          (NTM.uniformSeedRuns (n + 1)) (f (n + 1)) (n + 1)
          (tm.uniformCorrectSeed L f haccept hreject (n + 1))

end NTM

/-- Internal proof of `BPP ⊆ P/poly`. -/
theorem BPP_subset_PPoly_internal : BPP ⊆ PPoly := by
  intro L hL
  obtain ⟨d, hL⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, f, _hhalt, haccept, hreject, hf⟩ := hL
  rw [mem_PPoly_iff]
  exact ⟨tm.hardwiredAmplificationFamily L f haccept hreject,
    3 * d + 4,
    tm.hardwiredAmplificationFamily_decides_internal L f haccept hreject,
    tm.hardwiredAmplificationFamily_size_bigO_internal L haccept hreject hf⟩

end Complexity

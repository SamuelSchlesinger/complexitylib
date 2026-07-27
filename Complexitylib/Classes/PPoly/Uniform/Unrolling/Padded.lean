/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded.Internal

/-!
# Regularly padded deterministic unrolling families

For positive input length `n`, the direct tableau is padded to its closed cubic
gate bound and followed by one copy of its original acceptance wire. Thus the
raw gate count is known before serialization, while evaluation remains exactly
the deterministic bounded-run answer. The zero-length member retains the
library's explicit answer-bit convention.

## Main results

- `TM.paddedDirectUnrollingRawCircuit_length` gives the exact closed gate count.
- `TM.paddedDirectUnrollingRawCircuit_wellFormed` validates the padded syntax.
- `TM.paddedDirectUnrollingCircuitFamily_encodeAt` identifies the exact code map.
- `TM.DecidesInTime.paddedDirectUnrollingCircuitFamily_decides` proves correctness.
- `TM.paddedDirectUnrollingCircuitFamily_size_bigO` retains the cubic size bound.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- The unpadded positive tableau fits within its closed padding budget. -/
theorem directUnrollingRawCircuit_length_le_gateBound
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.directUnrollingRawCircuit f n).length ≤
      tm.directUnrollingGateBound f n :=
  tm.directUnrollingRawCircuit_length_le_gateBound_internal f n

/-- Every positive padded member has exactly the closed tableau bound plus its
terminal output-copy gate. -/
@[simp] theorem paddedDirectUnrollingRawCircuit_length
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.paddedDirectUnrollingRawCircuit f n).length =
      tm.directUnrollingGateBound f n + 1 :=
  tm.paddedDirectUnrollingRawCircuit_length_internal f n

/-- The padded gate stream is nonempty and every reference points strictly
backward. In particular, the final gate may safely copy the original last gate
through the dead padding. -/
theorem paddedDirectUnrollingRawCircuit_wellFormed
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    (tm.paddedDirectUnrollingRawCircuit f n).WellFormed n :=
  tm.paddedDirectUnrollingRawCircuit_wellFormed_internal f n

/-- Raw evaluation of a padded positive member is exactly deterministic
bounded acceptance. -/
theorem paddedDirectUnrollingRawCircuit_eval?
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n]
    (x : BitString n) :
    (tm.paddedDirectUnrollingRawCircuit f n).eval? x.toList =
      some (CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false)) :=
  tm.paddedDirectUnrollingRawCircuit_eval?_internal f n x

/-- Reconstruct a positive padded raw member as a typed single-output circuit. -/
noncomputable def paddedDirectUnrollingCircuit
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    Circuit Basis.andOr2 n 1
      ((tm.paddedDirectUnrollingRawCircuit f n).length - 1) :=
  (tm.paddedDirectUnrollingRawCircuit f n).toCircuit n
    (tm.paddedDirectUnrollingRawCircuit_wellFormed f n)

/-- Total family of regularly padded direct-unrolling circuits. -/
noncomputable def paddedDirectUnrollingCircuitFamily
    (tm : TM k) (f : ℕ → ℕ) : CircuitFamily Basis.andOr2 where
  emptyOutput := CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f 0)
    (fun i => Fin.elim0 i) (fun _ => false)
  circuits := fun n _ =>
    ⟨_, tm.paddedDirectUnrollingCircuit f n⟩

/-- The reconstructed positive circuit computes deterministic bounded
acceptance. -/
theorem paddedDirectUnrollingCircuit_eval
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) [NeZero n]
    (x : BitString n) :
    ((tm.paddedDirectUnrollingCircuit f n).eval x) 0 =
      CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false) := by
  have hbridge := CircuitCode.RawCircuit.eval?_toCircuit n
    (tm.paddedDirectUnrollingRawCircuit f n)
    (tm.paddedDirectUnrollingRawCircuit_wellFormed f n) x
  rw [tm.paddedDirectUnrollingRawCircuit_eval? f n x] at hbridge
  exact (Option.some.inj hbridge).symm

/-- The total padded family computes the same bounded deterministic trace bit
at every input length. -/
theorem paddedDirectUnrollingCircuitFamily_function
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) (x : BitString n) :
    (tm.paddedDirectUnrollingCircuitFamily f).function n x =
      CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f n) x
        (fun _ => false) := by
  cases n with
  | zero =>
      have hx : x = fun i => Fin.elim0 i := Subsingleton.elim _ _
      subst x
      rfl
  | succ n =>
      rw [CircuitFamily.function_succ]
      exact tm.paddedDirectUnrollingCircuit_eval f (n + 1) x

/-- The zero-length code is the same explicit tagged bounded-run answer as for
the direct family. -/
theorem paddedDirectUnrollingCircuitFamily_encodeAt_zero
    (tm : TM k) (f : ℕ → ℕ) :
    (tm.paddedDirectUnrollingCircuitFamily f).encodeAt 0 =
      [false, CircuitUnrolling.boundedAcceptanceBit tm.toNTM (f 0)
        (fun i => Fin.elim0 i) (fun _ => false)] := rfl

/-- A positive family member serializes to exactly the padded raw gate stream. -/
theorem paddedDirectUnrollingCircuitFamily_encodeAt_succ
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    (tm.paddedDirectUnrollingCircuitFamily f).encodeAt (n + 1) =
      true :: (tm.paddedDirectUnrollingRawCircuit f (n + 1)).encode := by
  rw [CircuitFamily.encodeAt_succ]
  change true :: CircuitCode.encodeCircuit
    (tm.paddedDirectUnrollingCircuit f (n + 1)) = _
  congr 1
  unfold CircuitCode.encodeCircuit paddedDirectUnrollingCircuit
  rw [CircuitCode.RawCircuit.ofCircuit_toCircuit]

/-- The family codec agrees at every length with the explicit padded code map. -/
theorem paddedDirectUnrollingCircuitFamily_encodeAt
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    (tm.paddedDirectUnrollingCircuitFamily f).encodeAt n =
      tm.paddedDirectUnrollingCode f n := by
  cases n with
  | zero => rfl
  | succ n =>
      exact tm.paddedDirectUnrollingCircuitFamily_encodeAt_succ f n

/-- A deterministic decider's padded direct family decides the same language. -/
theorem DecidesInTime.paddedDirectUnrollingCircuitFamily_decides
    {tm : TM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInTime L f) :
    (tm.paddedDirectUnrollingCircuitFamily f).Decides L := by
  rw [CircuitFamily.decides_iff]
  intro xs
  change
    (tm.paddedDirectUnrollingCircuitFamily f).function xs.length xs.get =
      true ↔ xs ∈ L
  rw [tm.paddedDirectUnrollingCircuitFamily_function f xs.length xs.get]
  simpa only [BitString.toList, List.ofFn_get] using
    hdec.boundedAcceptanceBit_iff xs.length xs.get (fun _ => false)

/-- At positive length, the padded family size is exactly its closed tableau
bound plus one terminal copy. -/
theorem paddedDirectUnrollingCircuitFamily_size_succ
    (tm : TM k) (f : ℕ → ℕ) (n : ℕ) :
    (tm.paddedDirectUnrollingCircuitFamily f).size (n + 1) =
      tm.directUnrollingGateBound f (n + 1) + 1 := by
  rw [CircuitFamily.size_succ]
  change (tm.paddedDirectUnrollingCircuit f (n + 1)).size = _
  unfold paddedDirectUnrollingCircuit
  rw [CircuitCode.RawCircuit.size_toCircuit,
    tm.paddedDirectUnrollingRawCircuit_length]

/-- A horizon in `O(n^d)` gives padded family size `O(n^(3d))`. -/
theorem paddedDirectUnrollingCircuitFamily_size_bigO
    (tm : TM k) {f : ℕ → ℕ} {d : ℕ}
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.paddedDirectUnrollingCircuitFamily f).size =O
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
      (fun n => tm.directUnrollingGateBound f n) =O
        ((· ^ (3 * d)) : ℕ → ℕ) := by
    unfold directUnrollingGateBound
    exact BigO.const_mul_left
      (CircuitUnrolling.acceptanceSizeCoeff tm.toNTM)
      (hcubeRaw.trans hcubePow)
  have hboundPlus :
      (fun n => tm.directUnrollingGateBound f n + 1) =O
        ((· ^ (3 * d)) : ℕ → ℕ) :=
    BigO.add hbound (BigO.const_le_pow 1 (3 * d))
  apply (CircuitFamily.SizeBoundedBy.bigO
    (F := tm.paddedDirectUnrollingCircuitFamily f) ?_).trans hboundPlus
  intro n
  cases n with
  | zero => simp
  | succ n =>
      rw [tm.paddedDirectUnrollingCircuitFamily_size_succ]

/-- Polynomially bounded horizons yield a polynomial-size padded family. -/
theorem paddedDirectUnrollingCircuitFamily_polynomialSize
    (tm : TM k) {f : ℕ → ℕ} {d : ℕ}
    (hf : f =O ((· ^ d) : ℕ → ℕ)) :
    (tm.paddedDirectUnrollingCircuitFamily f).PolynomialSize :=
  (CircuitFamily.polynomialSize_iff_bigO
    (tm.paddedDirectUnrollingCircuitFamily f)).2
      ⟨3 * d, tm.paddedDirectUnrollingCircuitFamily_size_bigO hf⟩

end TM

end Complexity

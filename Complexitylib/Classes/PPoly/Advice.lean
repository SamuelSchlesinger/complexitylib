/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Advice.Defs
public import Complexitylib.Classes.PPoly.Advice.Internal
public import Complexitylib.Classes.PPoly.Advice.Reverse
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Polynomial advice and nonuniform circuits

This module exposes the polynomial-advice machine class and its equivalence
with polynomial-size nonuniform circuits. The reverse simulation supplies each
canonical family-member encoding as advice to the verified serialized-circuit
evaluator.

## Main definitions and results

- `Advice`, `advisedInput`, `PolynomialAdvice`: the advice convention.
- `TM.DecidesWithAdviceInTime`, `PAdvice`: advised decision and its class.
- `TM.adviceCircuitFamily`: hardwire advice into bounded acceptance circuits.
- `PAdvice_subset_PPoly`: polynomial-time advice machines have polynomial-size
  circuit families.
- `PPoly_subset_PAdvice`: polynomial-size circuit families yield
  polynomial-time advice machines.
- `PAdvice_eq_PPoly`: the two nonuniform formulations coincide.
-/

@[expose] public section

namespace Complexity

/-- The advised input has the exact self-delimiting pairing length. -/
@[simp] theorem advisedInput_length (a : Advice) (x : List Bool) :
    (advisedInput a x).length = 2 * (a x.length).length + 2 + x.length := by
  simp [advisedInput]

namespace Advice

/-- The fixed advice prefix followed by `x` is exactly the advised machine
input. -/
theorem fixedPrefix_append (a : Advice) (x : List Bool) :
    a.fixedPrefix x.length ++ x = advisedInput a x := by
  simp [fixedPrefix, advisedInput, pair, List.append_assoc]

/-- The fixed-prefix bit string serializes to the self-delimiting advised
machine input. -/
@[simp] theorem inputBits_toList (a : Advice) {n : ℕ} (x : BitString n) :
    (a.inputBits x).toList = advisedInput a x.toList :=
  inputBits_toList_internal a x

/-- Advice has polynomial length exactly when its length function has a big-O
power bound. -/
theorem polynomialAdvice_iff_bigO (a : Advice) :
    PolynomialAdvice a ↔
      ∃ d : ℕ, (fun n => (a n).length) =O ((· ^ d) : ℕ → ℕ) :=
  polynomialAdvice_iff_bigO_internal a

/-- Empty advice has constant (hence polynomial) length. -/
theorem polynomialAdvice_nil : PolynomialAdvice (fun _ => []) := by
  exact ⟨0, by simp⟩

end Advice

/-- Pointwise shortening preserves polynomial advice length. -/
theorem PolynomialAdvice.of_length_le {a b : Advice} (hb : PolynomialAdvice b)
    (hle : ∀ n, (a n).length ≤ (b n).length) : PolynomialAdvice a :=
  PolynomialAdvice.of_length_le_internal hb hle

namespace TM

/-- Advised decision is monotone under pointwise enlargement of its time bound. -/
theorem DecidesWithAdviceInTime.mono
    {tm : TM k} {a : Advice} {L : Language} {T T' : ℕ → ℕ}
    (hle : ∀ n, T n ≤ T' n) (hdec : tm.DecidesWithAdviceInTime a L T) :
    tm.DecidesWithAdviceInTime a L T' :=
  hdec.mono_internal hle

/-- Exact-horizon advised acceptance agrees with ordinary language membership. -/
theorem DecidesWithAdviceInTime.advisedBoundedAcceptanceBit_iff
    {tm : TM k} {a : Advice} {L : Language} {T : ℕ → ℕ}
    (hdec : tm.DecidesWithAdviceInTime a L T)
    (n : ℕ) (x : BitString n) :
    tm.advisedBoundedAcceptanceBit a T x = true ↔ x.toList ∈ L :=
  hdec.advisedBoundedAcceptanceBit_iff_internal n x

/-- The hardwired advice family computes the exact bounded advised verdict. -/
theorem adviceCircuitFamily_function
    (tm : TM k) (a : Advice) (T : ℕ → ℕ)
    (n : ℕ) (x : BitString n) :
    (tm.adviceCircuitFamily a T).function n x =
      tm.advisedBoundedAcceptanceBit a T x :=
  tm.adviceCircuitFamily_function_internal a T n x

/-- The hardwired advice family decides the advised machine's language. -/
theorem DecidesWithAdviceInTime.adviceCircuitFamily_decides
    {tm : TM k} {a : Advice} {L : Language} {T : ℕ → ℕ}
    (hdec : tm.DecidesWithAdviceInTime a L T) :
    (tm.adviceCircuitFamily a T).Decides L :=
  hdec.adviceCircuitFamily_decides_internal

/-- Pointwise cubic size bound for hardwired advised computation. -/
theorem adviceCircuitFamily_size_le
    (tm : TM k) (a : Advice) (T : ℕ → ℕ) (n : ℕ) :
    (tm.adviceCircuitFamily a T).size n ≤
      CircuitUnrolling.acceptanceSizeCoeff tm.toNTM * (T n + 2) ^ 3 :=
  tm.adviceCircuitFamily_size_le_internal a T n

/-- A time-`O(n^d)` advised computation yields a circuit family of size
`O(n^(3d))`. -/
theorem adviceCircuitFamily_size_bigO
    (tm : TM k) (a : Advice) {T : ℕ → ℕ} {d : ℕ}
    (hT : T =O ((· ^ d) : ℕ → ℕ)) :
    (tm.adviceCircuitFamily a T).size =O
      ((· ^ (3 * d)) : ℕ → ℕ) :=
  tm.adviceCircuitFamily_size_bigO_internal a hT

/-- One polynomial-time advised decider directly witnesses membership in
`P/poly`.

No advice-length hypothesis is needed for this direction: the advice prefix is
hardwired without adding gates, while the unrolling size depends only on the time
horizon. `PAdvice` still requires polynomial advice length to match the standard
class convention. -/
theorem DecidesWithAdviceInTime.mem_PPoly
    {tm : TM k} {a : Advice} {L : Language} {T : ℕ → ℕ} {d : ℕ}
    (hdec : tm.DecidesWithAdviceInTime a L T)
    (hT : T =O ((· ^ d) : ℕ → ℕ)) : L ∈ PPoly :=
  hdec.mem_PPoly_internal hT

end TM

/-- Polynomial-time advice machines have polynomial-size nonuniform circuits. -/
theorem PAdvice_subset_PPoly : PAdvice ⊆ PPoly :=
  PAdvice_subset_PPoly_internal

/-- Polynomial advice and polynomial-size nonuniform circuit families define
the same language class. -/
theorem PAdvice_eq_PPoly : PAdvice = PPoly :=
  Set.Subset.antisymm PAdvice_subset_PPoly PPoly_subset_PAdvice

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly
public import Complexitylib.Classes.PPoly.Advice.Defs
public import Complexitylib.Models.TuringMachine.Internal

/-!
# Polynomial advice — proof internals

This module proves representation laws, exact semantics, and polynomial size
for advised-computation circuit families. Public statements are exposed by
`Complexitylib.Classes.PPoly.Advice`.
-/

@[expose] public section

namespace Complexity

namespace Advice

/-- Internal serialization law for the fixed-prefix advised input. -/
theorem inputBits_toList_internal (a : Advice) {n : ℕ} (x : BitString n) :
    (a.inputBits x).toList = advisedInput a x.toList := by
  rw [inputBits, BitString.toList_append]
  simp only [BitString.toList, List.ofFn_get]
  simp [fixedPrefix, advisedInput, pair]

/-- Internal big-O characterization of polynomial advice length. -/
theorem polynomialAdvice_iff_bigO_internal (a : Advice) :
    PolynomialAdvice a ↔
      ∃ d : ℕ, (fun n => (a n).length) =O ((· ^ d) : ℕ → ℕ) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.natDegree, BigO.of_polynomial_bound p hp⟩
  · rintro ⟨d, hd⟩
    obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hd
    exact ⟨p, hp⟩

end Advice

/-- Internal monotonicity of polynomial advice under pointwise shortening. -/
theorem PolynomialAdvice.of_length_le_internal {a b : Advice}
    (hb : PolynomialAdvice b)
    (hle : ∀ n, (a n).length ≤ (b n).length) : PolynomialAdvice a := by
  obtain ⟨p, hp⟩ := hb
  exact ⟨p, fun n => (hle n).trans (hp n)⟩

namespace TM

/-- Internal time-bound monotonicity for advised decision. -/
theorem DecidesWithAdviceInTime.mono_internal
    {tm : TM k} {a : Advice} {L : Language} {T T' : ℕ → ℕ}
    (hle : ∀ n, T n ≤ T' n) (hdec : tm.DecidesWithAdviceInTime a L T) :
    tm.DecidesWithAdviceInTime a L T' := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ := hdec x
  exact ⟨c', t, ht.trans (hle x.length), hreach, hhalt, hyes, hno⟩

/-- Internal exact-horizon correctness of the advised bounded acceptance bit. -/
theorem DecidesWithAdviceInTime.advisedBoundedAcceptanceBit_iff_internal
    {tm : TM k} {a : Advice} {L : Language} {T : ℕ → ℕ}
    (hdec : tm.DecidesWithAdviceInTime a L T)
    (n : ℕ) (x : BitString n) :
    tm.advisedBoundedAcceptanceBit a T x = true ↔ x.toList ∈ L := by
  have hdecx := hdec x.toList
  simp only [BitString.length_toList] at hdecx
  obtain ⟨c', t, hle, hreach, hhalt, hyes, hno⟩ := hdecx
  have htrace :
      tm.toNTM.trace (T n) (fun _ => false)
        (tm.toNTM.initCfg (advisedInput a x.toList)) = c' :=
    tm.toNTM_trace_of_reachesIn hreach hhalt hle (fun _ => false)
  unfold advisedBoundedAcceptanceBit CircuitUnrolling.boundedAcceptanceBit
  rw [Advice.inputBits_toList_internal, htrace, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hout⟩
    by_contra hx
    rw [hno hx] at hout
    cases hout
  · intro hx
    exact ⟨hhalt, hyes hx⟩

/-- Internal semantics of the hardwired advice circuit family. -/
theorem adviceCircuitFamily_function_internal
    (tm : TM k) (a : Advice) (T : ℕ → ℕ)
    (n : ℕ) (x : BitString n) :
    (tm.adviceCircuitFamily a T).function n x =
      tm.advisedBoundedAcceptanceBit a T x := by
  cases n with
  | zero =>
      have hx : x = fun i => Fin.elim0 i := Subsingleton.elim _ _
      subst x
      rfl
  | succ n =>
      rw [CircuitFamily.function_succ]
      change
        ((Circuit.restrictPrefix (a.fixedPrefix (n + 1)).get
          (CircuitUnrolling.fixedChoicesAcceptanceCircuit tm.toNTM (T (n + 1))
            ((a.fixedPrefix (n + 1)).length + (n + 1))
            (fun _ => false))).eval x) 0 = _
      rw [Circuit.restrictPrefix_eval,
        CircuitUnrolling.fixedChoicesAcceptanceCircuit_eval]
      rfl

/-- Internal whole-language correctness of the hardwired advice family. -/
theorem DecidesWithAdviceInTime.adviceCircuitFamily_decides_internal
    {tm : TM k} {a : Advice} {L : Language} {T : ℕ → ℕ}
    (hdec : tm.DecidesWithAdviceInTime a L T) :
    (tm.adviceCircuitFamily a T).Decides L := by
  rw [CircuitFamily.decides_iff]
  intro xs
  rw [CircuitFamily.evalList]
  rw [tm.adviceCircuitFamily_function_internal a T]
  simpa only [BitString.toList, List.ofFn_get] using
    hdec.advisedBoundedAcceptanceBit_iff_internal xs.length xs.get

/-- Internal pointwise cubic size bound for the hardwired advice family. -/
theorem adviceCircuitFamily_size_le_internal
    (tm : TM k) (a : Advice) (T : ℕ → ℕ) (n : ℕ) :
    (tm.adviceCircuitFamily a T).size n ≤
      CircuitUnrolling.acceptanceSizeCoeff tm.toNTM * (T n + 2) ^ 3 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [CircuitFamily.size_succ]
      change
        (Circuit.restrictPrefix (a.fixedPrefix (n + 1)).get
          (CircuitUnrolling.fixedChoicesAcceptanceCircuit tm.toNTM (T (n + 1))
            ((a.fixedPrefix (n + 1)).length + (n + 1))
            (fun _ => false))).size ≤ _
      rw [Circuit.restrictPrefix_size]
      exact CircuitUnrolling.fixedChoicesAcceptanceCircuit_size_le tm.toNTM
        (T (n + 1)) ((a.fixedPrefix (n + 1)).length + (n + 1)) (fun _ => false)

/-- Internal asymptotic size bound for the hardwired advice family. -/
theorem adviceCircuitFamily_size_bigO_internal
    (tm : TM k) (a : Advice) {T : ℕ → ℕ} {d : ℕ}
    (hT : T =O ((· ^ d) : ℕ → ℕ)) :
    (tm.adviceCircuitFamily a T).size =O
      ((· ^ (3 * d)) : ℕ → ℕ) := by
  have hshift : (fun n => T n + 2) =O ((· ^ d) : ℕ → ℕ) :=
    BigO.add hT (BigO.const_le_pow 2 d)
  have hcubeRaw := BigO.pow hshift 3
  have hcubePow : (fun n : ℕ => (n ^ d) ^ 3) =O
      ((· ^ (3 * d)) : ℕ → ℕ) := by
    apply BigO.of_le
    intro n
    apply le_of_eq
    rw [← pow_mul]
    congr 1
    omega
  apply (CircuitFamily.SizeBoundedBy.bigO
    (tm.adviceCircuitFamily_size_le_internal a T)).trans
  exact BigO.const_mul_left (CircuitUnrolling.acceptanceSizeCoeff tm.toNTM)
    (hcubeRaw.trans hcubePow)

/-- Internal packaging theorem from one polynomial-time advised decider to
`P/poly`. -/
theorem DecidesWithAdviceInTime.mem_PPoly_internal
    {tm : TM k} {a : Advice} {L : Language} {T : ℕ → ℕ} {d : ℕ}
    (hdec : tm.DecidesWithAdviceInTime a L T)
    (hT : T =O ((· ^ d) : ℕ → ℕ)) : L ∈ PPoly := by
  rw [mem_PPoly_iff]
  exact ⟨tm.adviceCircuitFamily a T, 3 * d,
    hdec.adviceCircuitFamily_decides_internal,
    tm.adviceCircuitFamily_size_bigO_internal a hT⟩

end TM

/-- Internal proof that polynomial-time advice machines have polynomial-size
nonuniform circuits. -/
theorem PAdvice_subset_PPoly_internal : PAdvice ⊆ PPoly := by
  intro L hL
  obtain ⟨d, k, tm, a, T, _ha, hdec, hT⟩ := hL
  exact hdec.mem_PPoly_internal hT

end Complexity

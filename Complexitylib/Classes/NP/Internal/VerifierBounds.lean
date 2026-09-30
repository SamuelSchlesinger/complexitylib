/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.Verifier.Defs
public import Complexitylib.Asymptotics

/-!
# Polynomial time for linear finite-certificate verification

The concrete compiler overhead and its finite verifier-time maximum have a
uniform explicit polynomial bound, without assuming verifier-time monotonicity.
-/

public section

namespace Complexity

namespace WitnessTM.Verifier

/-- Exact linear setup overhead, including phase handoffs. -/
theorem time_linear_eq (T : ℕ → ℕ) (n : ℕ) :
    time WitnessBoundSetup.linear T n =
      13 * n + 32 + window (fun n => n + 1) T n := by
  simp only [time, WitnessBoundSetup.linear, NTM.guessBoundedTime, TM.pairBuildTime]
  omega

/-- A natural polynomial bound for the verifier induces an explicit polynomial
bound for the whole linear-witness compiler, without monotonicity of `T`. -/
theorem time_linear_polynomial_bound {T : ℕ → ℕ} {c : ℕ}
    (hT : T =O (· ^ c)) :
    ∃ q : Polynomial ℕ, ∀ n, time WitnessBoundSetup.linear T n ≤ q.eval n := by
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hT
  let lin : Polynomial ℕ := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  let q : Polynomial ℕ := (Polynomial.C 13 * Polynomial.X + Polynomial.C 32) + p.comp lin
  refine ⟨q, ?_⟩
  intro n
  have hwindow : window (fun n => n + 1) T n ≤ (p.comp lin).eval n := by
    unfold window
    refine Finset.sup_le ?_
    intro m hm
    have harg : 2 * n + 2 + m ≤ 3 * n + 3 := by
      simp only [Finset.mem_range] at hm
      omega
    have hpmono := polynomial_eval_mono_nat p harg
    exact le_trans (hp _) (by simpa [lin, Polynomial.eval_comp] using hpmono)
  calc
    time WitnessBoundSetup.linear T n =
        13 * n + 32 + window (fun n => n + 1) T n := time_linear_eq T n
    _ ≤ 13 * n + 32 + (p.comp lin).eval n := Nat.add_le_add_left hwindow _
    _ = q.eval n := by simp [q]

/-- The linear-witness compiler preserves polynomial running time. -/
theorem time_linear_bigO_of_bigO {T : ℕ → ℕ} {c : ℕ} (hT : T =O (· ^ c)) :
    ∃ d : ℕ, time WitnessBoundSetup.linear T =O (· ^ d) := by
  obtain ⟨q, hq⟩ := time_linear_polynomial_bound hT
  exact ⟨q.natDegree, BigO.of_polynomial_bound q hq⟩

end WitnessTM.Verifier

end Complexity

/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.SimLoop
public import Complexitylib.Asymptotics

/-!
# Support lemmas for the time-hierarchy theorem

Four self-contained ingredients used by the diagonalization argument:

* `groupPairs_length_le` — decoding a bit string into 2-bit groups at most
  halves its length.
* `TM.UTMBody.utmStepTime_le_sq` — the per-iteration cost of the UTM loop
  is quadratic in the description length, with an explicit constant.
* `Complexity.LittleO.nat_mul_le` — a little-o hypothesis yields, for every
  scale factor `C`, an eventual pointwise bound `C * f n ≤ g n` over `ℕ`.
* `TM.halt_or_run_dichotomy` — a deterministic machine either halts within
  a step budget `V` or is still running after exactly `V` steps.
-/


public section

namespace Complexity

open Asymptotics Filter

-- ════════════════════════════════════════════════════════════════════════
-- groupPairs length bound
-- ════════════════════════════════════════════════════════════════════════

/-- `groupPairs` consumes two bits per emitted symbol (a trailing odd bit
    is dropped), so its output is at most half as long as its input. -/
theorem groupPairs_length_le : ∀ α : List Bool, 2 * (groupPairs α).length ≤ α.length
  | [] => Nat.le_refl 0
  | [_] => by simp [groupPairs]
  | _ :: _ :: rest => by
    have ih := groupPairs_length_le rest
    simp only [groupPairs, List.length_cons]
    omega

-- ════════════════════════════════════════════════════════════════════════
-- utmStepTime polynomial bound
-- ════════════════════════════════════════════════════════════════════════

namespace TM.UTMBody

/-- The per-iteration cost of the UTM's simulate/halt-test loop is
    quadratic in the description length, with explicit constant `240`. -/
theorem utmStepTime_le_sq (α : List Bool) :
    utmStepTime α ≤ 240 * (α.length + 1) ^ 2 := by
  have hL : (groupPairs α).length ≤ α.length := by
    have := groupPairs_length_le α; omega
  have hLL : (groupPairs α).length * (groupPairs α).length ≤ α.length * α.length :=
    Nat.mul_le_mul hL hL
  unfold utmStepTime bodyIterTime
  nlinarith [hL, hLL]

end TM.UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- Little-o to ℕ-scaled eventual bound
-- ════════════════════════════════════════════════════════════════════════


/-- A little-o hypothesis beats every constant multiple eventually: from
    `f = o(g)` extract, for any scale `C : ℕ`, a threshold `N` past which
    `C * f n ≤ g n` pointwise over `ℕ`. -/
theorem LittleO.nat_mul_le {f g : ℕ → ℕ} (h : LittleO f g) (C : ℕ) :
    ∃ N, ∀ n, N ≤ n → C * f n ≤ g n := by
  have h' := LittleO.const_mul_left C h
  have hb := isLittleO_iff.mp h' one_pos
  rw [eventually_atTop] at hb
  obtain ⟨N, hN⟩ := hb
  refine ⟨N, fun n hn => ?_⟩
  have hbound := hN n hn
  simp only [Real.norm_natCast, one_mul] at hbound
  exact_mod_cast hbound


-- ════════════════════════════════════════════════════════════════════════
-- Run dichotomy
-- ════════════════════════════════════════════════════════════════════════

/-- **Run dichotomy**: from any configuration, a deterministic machine
    either halts within `V` steps or reaches a non-halted configuration in
    exactly `V` steps. -/
theorem TM.halt_or_run_dichotomy {k : ℕ} (tm : TM k) (c₀ : Cfg k tm.Q) (V : ℕ) :
    (∃ (T : ℕ) (c : Cfg k tm.Q), T ≤ V ∧ tm.reachesIn T c₀ c ∧ tm.halted c) ∨
    (∃ c : Cfg k tm.Q, tm.reachesIn V c₀ c ∧ ¬tm.halted c) := by
  induction V generalizing c₀ with
  | zero =>
    by_cases hh : tm.halted c₀
    · exact Or.inl ⟨0, c₀, Nat.le_refl 0, .zero, hh⟩
    · exact Or.inr ⟨c₀, .zero, hh⟩
  | succ V ih =>
    by_cases hh : tm.halted c₀
    · exact Or.inl ⟨0, c₀, Nat.zero_le _, .zero, hh⟩
    · obtain ⟨c₁, hs⟩ : ∃ c₁, tm.step c₀ = some c₁ := by
        unfold TM.step
        rw [ite_eq_right hh]
        exact ⟨_, rfl⟩
      rcases ih c₁ with ⟨T, c, hT, hr, hhalt⟩ | ⟨c, hr, hnh⟩
      · exact Or.inl ⟨T + 1, c, by omega, .step hs hr, hhalt⟩
      · exact Or.inr ⟨c, .step hs hr, hnh⟩

end Complexity

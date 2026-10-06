/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Corollaries
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Gates with arbitrary activations

Every gate of an `ActivationProgram` is its own block. Given the earlier gates, an input-reading
gate `j` is `activation j (t + c)` in its weighted input sum `t`, for a constant `c`, so it
changes at most `T j` times when its activation does; a gate reading no input is a function of
the earlier gates. The capacity theorem then charges `max 1 (4 T j)` to every input-reading gate
and nothing to the other gates.
-/

public section

namespace Algebraic.Threshold

variable {n s : ℕ} {β γ : Type*}

theorem ChangesAtMost.map {Ψ : ℝ → β} {T : ℕ} (h : ChangesAtMost Ψ T) (G : β → γ) :
    ChangesAtMost (fun t => G (Ψ t)) T :=
  fun z hz S hS => h z hz S fun i hi heq => hS i hi (by simp only [heq])

theorem changesAtMost_const (c : β) : ChangesAtMost (fun _ : ℝ => c) 0 := by
  intro z _ S hS
  rcases S.eq_empty_or_nonempty with h | ⟨i, hi⟩
  · simp [h]
  · exact absurd rfl (hS i hi)

namespace ActivationProgram

variable (C : ActivationProgram n s)

theorem eval_eq_internal (x : Fin n → Bool) (j : Fin s) :
    C.eval x j = C.activation j (weightedSum (C.inputWeight j) x + ∑ k : Fin s,
      if k < j then C.gateWeight j k * (C.eval x k).toNat else 0) := by
  rw [eval]
  simp only [dite_eq_ite]

open scoped Classical in
/-- The change budget of the `i`-th gate: `T` for an input-reading gate, `0` otherwise. -/
noncomputable def budget (T : Fin s → ℕ) (i : ℕ) : ℕ :=
  if h : i < s then (if (⟨i, h⟩ : Fin s) ∈ C.inputGates then T ⟨i, h⟩ else 0) else 0

open scoped Classical in
/-- The gate-by-gate block decomposition of an activation program. -/
@[expose] noncomputable def toBlockDecomposition {f : Cslib.BooleanFunction n}
    (hC : C.Computes f) (T : Fin s → ℕ)
    (hT : ∀ j ∈ C.inputGates, ChangesAtMost (C.activation j) (T j)) :
    BlockDecomposition f (Fin s → Bool) where
  length := s
  kind i := .oneDim (C.budget T i)
  history i x := fun j => if j.1 < i then C.eval x j else false
  output v := v C.output
  history_zero _ _ := by
    funext j
    simp
  step i hi := by
    let j₀ : Fin s := ⟨i, hi⟩
    let c : (Fin s → Bool) → ℝ := fun η => ∑ k : Fin s,
      if k < j₀ then C.gateWeight j₀ k * (η k).toNat else 0
    let arg : ℝ → ℝ := fun t => if j₀ ∈ C.inputGates then t else 0
    let G : (Fin s → Bool) → Bool → Fin s → Bool := fun η b j =>
      if j.1 < i then η j else if j.1 = i then b else false
    refine ⟨C.inputWeight j₀, fun η t => G η (C.activation j₀ (arg t + c η)), ?_, ?_⟩
    · intro η
      by_cases hin : j₀ ∈ C.inputGates
      · have hb : C.budget T i = T j₀ := by simp [budget, hi, j₀, hin]
        rw [hb]
        have := ((hT j₀ hin).comp_add_const (c η)).map (G η)
        simpa [arg, hin] using this
      · have hb : C.budget T i = 0 := by simp [budget, hi, j₀, hin]
        rw [hb]
        simpa [arg, hin] using changesAtMost_const (G η (C.activation j₀ (0 + c η)))
    · intro x
      funext j
      by_cases hj : j.1 < i
      · simp [G, hj, Nat.lt_succ_of_lt hj]
      · by_cases hji : j.1 = i
        · have hjj : j = j₀ := Fin.ext hji
          subst hjj
          have harg : arg (weightedSum (C.inputWeight j₀) x) =
              weightedSum (C.inputWeight j₀) x := by
            by_cases hin : j₀ ∈ C.inputGates
            · simp [arg, hin]
            · have hw : C.inputWeight j₀ = 0 := by
                simpa [inputGates] using hin
              simp [arg, hin, hw, weightedSum]
          have hc : c (fun j => if j.1 < i then C.eval x j else false) =
              ∑ k : Fin s, if k < j₀ then C.gateWeight j₀ k * (C.eval x k).toNat else 0 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            by_cases hk : k < j₀
            · have hk' : k.1 < i := hk
              simp [hk, hk']
            · simp [hk]
          simp only [G, lt_irrefl, ite_false, ite_true, Nat.lt_succ_self, harg, hc, j₀]
          rw [eval_eq_internal]
        · have : ¬ j.1 < i + 1 := by omega
          simp [G, hj, hji, this]
  output_history x := by
    simp only [C.output.2, ite_true]
    exact hC x

theorem toBlockDecomposition_cost {f : Cslib.BooleanFunction n} (hC : C.Computes f)
    (T : Fin s → ℕ) (hT : ∀ j ∈ C.inputGates, ChangesAtMost (C.activation j) (T j)) :
    (C.toBlockDecomposition hC T hT).cost = ∏ j ∈ C.inputGates, max 1 (4 * T j) := by
  classical
  have hterm : ∀ j : Fin s, (BlockKind.oneDim (C.budget T j.1)).cost =
      if j ∈ C.inputGates then max 1 (4 * T j) else 1 := by
    intro j
    rw [cost_oneDim_eq_max]
    by_cases hj : j ∈ C.inputGates
    · simp [budget, j.2, hj]
    · simp [budget, j.2, hj]
  change ∏ i ∈ Finset.range s, (BlockKind.oneDim (C.budget T i)).cost = _
  rw [Finset.prod_range, Finset.prod_congr rfl fun j _ => hterm j, Finset.prod_ite_mem,
    Finset.univ_inter]

end ActivationProgram

theorem two_pow_lt_of_activations_internal {f : Cslib.BooleanFunction n} {K : ℕ}
    (hf : TwoSidedRectangleFree f K) {C : ActivationProgram n s} (hC : C.Computes f)
    (T : Fin s → ℕ) (hT : ∀ j ∈ C.inputGates, ChangesAtMost (C.activation j) (T j)) :
    2 ^ n < 4 * K ^ 2 * ∏ j ∈ C.inputGates, max 1 (4 * T j) :=
  (C.toBlockDecomposition_cost hC T hT) ▸
    two_pow_lt_mul_cost_internal hf (C.toBlockDecomposition hC T hT)

end Algebraic.Threshold

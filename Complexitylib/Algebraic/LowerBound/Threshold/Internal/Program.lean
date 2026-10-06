/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Capacity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Threshold programs as block decompositions

* `Program.evalFrom_eq_eval`: overriding gates by their true values and feeding the other gates
  their true weighted input sums recovers the ordinary evaluation.
* `Program.piecesAtMost_evalFrom` (Lemma 2): if every unfixed gate `j` receives the input
  contribution `slope j * t`, the gate values have at most `2 ^ r` pieces as functions of `t`,
  where `r` counts the unfixed gates with `slope j ≠ 0`. Induction over the gates: on each piece
  of the earlier gates, the next gate is `[slope * t + c ≥ 0]` for one constant `c`, which is
  monotone in `t` and splits the piece into at most two intervals; a gate with zero slope or a
  fixed gate is constant on each piece.
* `Program.DirectionRuns.toBlockDecomposition`: a split of the gates into runs along single
  directions gives a block decomposition whose `i`-th block changes at most `2 ^ rᵢ - 1` times,
  `rᵢ` being the number of input-reading gates of the run.
-/

public section

namespace Algebraic.Threshold

open Cutwidth

variable {n s : ℕ}

namespace Program

variable (C : Program n s)

theorem evalFrom_eq (fixed : Finset (Fin s)) (η : Fin s → Bool) (z : Fin s → ℝ) (j : Fin s) :
    C.evalFrom fixed η z j = if j ∈ fixed then η j else
      decide (0 ≤ z j + (∑ k : Fin s,
        if k < j then C.gateWeight j k * (C.evalFrom fixed η z k).toNat else 0) + C.bias j) := by
  rw [evalFrom]
  simp only [dite_eq_ite]

theorem eval_eq (x : Fin n → Bool) (j : Fin s) :
    C.eval x j = decide (0 ≤ weightedSum (C.inputWeight j) x + (∑ k : Fin s,
        if k < j then C.gateWeight j k * (C.eval x k).toNat else 0) + C.bias j) := by
  rw [eval, evalFrom_eq]
  simp only [Finset.notMem_empty, ite_false]

/-- Overriding gates by their true values and feeding the other gates their true weighted input
sums recovers the ordinary evaluation, gate by gate. -/
theorem evalFrom_eq_eval {fixed : Finset (Fin s)} {η : Fin s → Bool} {z : Fin s → ℝ}
    {x : Fin n → Bool} (j : Fin s)
    (hfix : ∀ k ≤ j, k ∈ fixed → η k = C.eval x k)
    (hz : ∀ k ≤ j, k ∉ fixed → z k = weightedSum (C.inputWeight k) x) :
    C.evalFrom fixed η z j = C.eval x j := by
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  by_cases hj : j ∈ fixed
  · rw [evalFrom_eq, ite_eq_left hj]
    exact hfix j le_rfl hj
  · rw [evalFrom_eq, ite_eq_right hj, eval_eq, hz j le_rfl hj]
    have hsum : (∑ k : Fin s,
        if k < j then C.gateWeight j k * (C.evalFrom fixed η z k).toNat else 0) =
        ∑ k : Fin s, if k < j then C.gateWeight j k * (C.eval x k).toNat else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hk
      · rw [ih k hk (fun k' hk' => hfix k' (hk'.trans hk.le))
          (fun k' hk' => hz k' (hk'.trans hk.le))]
      · rfl
    rw [hsum]

/-- The values of the first `d` gates, as functions of the parameter `t`. -/
noncomputable def prefixValues (fixed : Finset (Fin s)) (η : Fin s → Bool) (slope : Fin s → ℝ)
    (d : ℕ) (t : ℝ) : Fin s → Bool :=
  fun j => if j.1 < d then C.evalFrom fixed η (fun k => slope k * t) j else false

open scoped Classical in
/-- The number of unfixed gates with a nonzero slope among the first `d` gates. -/
noncomputable def activeCount (fixed : Finset (Fin s)) (slope : Fin s → ℝ) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin s => j.1 < d ∧ j ∉ fixed ∧ slope j ≠ 0).card

private theorem activeCount_succ (fixed : Finset (Fin s)) (slope : Fin s → ℝ) {d : ℕ}
    (j₀ : Fin s) (hj₀ : j₀.1 = d) :
    activeCount fixed slope (d + 1) = activeCount fixed slope d +
      if j₀ ∉ fixed ∧ slope j₀ ≠ 0 then 1 else 0 := by
  classical
  unfold activeCount
  split_ifs with hc
  · rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun j : Fin s =>
      j.1 < d ∧ j ∉ fixed ∧ slope j ≠ 0) (a := j₀) (by simp [hj₀])]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hj : j.1 = d
      · left
        exact Fin.ext (hj.trans hj₀.symm)
      · right
        exact ⟨by omega, h2, h3⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨by omega, hc⟩
      · exact ⟨by omega, h2, h3⟩
  · rw [add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      by_contra hj
      have : j = j₀ := Fin.ext (by omega)
      subst this
      exact hc ⟨h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h2, h3⟩

private theorem prefixValues_succ (fixed : Finset (Fin s)) (η : Fin s → Bool)
    (slope : Fin s → ℝ) {d : ℕ} (j₀ : Fin s) (hj₀ : j₀.1 = d) (t : ℝ) :
    C.prefixValues fixed η slope (d + 1) t = Function.update (C.prefixValues fixed η slope d t)
      j₀ (C.evalFrom fixed η (fun k => slope k * t) j₀) := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    simp [prefixValues, hj₀]
  · rw [Function.update_of_ne hj]
    have hj' : j.1 ≠ d := fun h => hj (Fin.ext (h.trans hj₀.symm))
    simp only [prefixValues]
    by_cases hlt : j.1 < d
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- The next gate as a function of the earlier gate values and the parameter. -/
private theorem evalFrom_next (fixed : Finset (Fin s)) (η : Fin s → Bool) (slope : Fin s → ℝ)
    {d : ℕ} (j₀ : Fin s) (hj₀ : j₀.1 = d) (t : ℝ) :
    C.evalFrom fixed η (fun k => slope k * t) j₀ =
      if j₀ ∈ fixed then η j₀ else
        decide (0 ≤ slope j₀ * t + (∑ k : Fin s, if k < j₀ then
          C.gateWeight j₀ k * (C.prefixValues fixed η slope d t k).toNat else 0) +
          C.bias j₀) := by
  rw [evalFrom_eq]
  have hsum : (∑ k : Fin s, if k < j₀ then
      C.gateWeight j₀ k * (C.evalFrom fixed η (fun k => slope k * t) k).toNat else 0) =
      ∑ k : Fin s, if k < j₀ then
        C.gateWeight j₀ k * (C.prefixValues fixed η slope d t k).toNat else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · have hk' : k.1 < d := hj₀ ▸ hk
      simp [prefixValues, hk']
    · rfl
  rw [hsum]

private theorem bool_eq_of_toNat_eq : ∀ a b : Bool, a.toNat = b.toNat → a = b := by decide

private theorem bool_eq_of_not_toNat_eq : ∀ a b : Bool, (!a).toNat = (!b).toNat → a = b := by
  decide

private theorem piecesAtMost_prefixValues (fixed : Finset (Fin s)) (η : Fin s → Bool)
    (slope : Fin s → ℝ) (d : ℕ) :
    PiecesAtMost (C.prefixValues fixed η slope d) (2 ^ activeCount fixed slope d) := by
  induction d with
  | zero =>
    refine ⟨fun _ => 0, monotone_const, fun _ => by positivity, fun t t' _ => ?_⟩
    funext j
    simp [prefixValues]
  | succ d ih =>
    by_cases hd : d < s
    swap
    · have heq : C.prefixValues fixed η slope (d + 1) = C.prefixValues fixed η slope d := by
        funext t j
        simp only [prefixValues]
        rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      have hcount : activeCount fixed slope (d + 1) = activeCount fixed slope d := by
        unfold activeCount
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      rw [heq, hcount]
      exact ih
    obtain ⟨π, mono, lt, fac⟩ := ih
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin s, j₀.1 = d := ⟨⟨d, hd⟩, rfl⟩
    let F : (Fin s → Bool) → ℝ := fun v => ∑ k : Fin s,
      if k < j₀ then C.gateWeight j₀ k * (v k).toNat else 0
    have hsucc := C.prefixValues_succ fixed η slope j₀ hj₀
    have hnext := C.evalFrom_next fixed η slope j₀ hj₀
    rw [activeCount_succ fixed slope j₀ hj₀]
    by_cases hfix : j₀ ∈ fixed
    · -- A fixed gate is constant.
      simp only [hfix, not_true_eq_false, false_and, ite_false, add_zero]
      refine ⟨π, mono, lt, fun t t' e => ?_⟩
      rw [hsucc t, hsucc t', fac t t' e, hnext t, hnext t', ite_eq_left hfix, ite_eq_left hfix]
    by_cases hslope : slope j₀ = 0
    · -- A gate with zero slope is a function of the earlier gates.
      simp only [hslope, ne_eq, not_true_eq_false, and_false, ite_false, add_zero]
      refine ⟨π, mono, lt, fun t t' e => ?_⟩
      rw [hsucc t, hsucc t', hnext t, hnext t', ite_eq_right hfix, ite_eq_right hfix, hslope,
        zero_mul, zero_mul, fac t t' e]
    -- A gate with nonzero slope splits each piece in two.
    simp only [hfix, not_false_eq_true, hslope, ne_eq, and_self, ite_true]
    let g : ℝ → Bool := fun t => C.evalFrom fixed η (fun k => slope k * t) j₀
    have hg : ∀ t, g t = decide (0 ≤ slope j₀ * t +
        F (C.prefixValues fixed η slope d t) + C.bias j₀) := by
      intro t
      simp only [g, F]
      rw [hnext t, ite_eq_right hfix]
    let b : ℝ → ℕ := fun t => (if 0 < slope j₀ then g t else !g t).toNat
    have hb1 : ∀ t, b t ≤ 1 := fun t => Bool.toNat_le _
    have hbmono : ∀ t t', t ≤ t' → π t = π t' → b t ≤ b t' := by
      intro t t' htt' e
      have hv := fac t t' e
      simp only [b, hg, hv]
      by_cases hpos : 0 < slope j₀
      · simp only [hpos, ite_true]
        have : slope j₀ * t ≤ slope j₀ * t' := mul_le_mul_of_nonneg_left htt' hpos.le
        by_cases h : 0 ≤ slope j₀ * t + F (C.prefixValues fixed η slope d t') + C.bias j₀
        · have h' : 0 ≤ slope j₀ * t' + F (C.prefixValues fixed η slope d t') + C.bias j₀ := by
            linarith
          simp [h, h']
        · simp [h]
      · simp only [hpos, ite_false]
        have hneg : slope j₀ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hslope
        have : slope j₀ * t' ≤ slope j₀ * t := mul_le_mul_of_nonpos_left htt' hneg.le
        by_cases h : 0 ≤ slope j₀ * t' + F (C.prefixValues fixed η slope d t') + C.bias j₀
        · have h' : 0 ≤ slope j₀ * t + F (C.prefixValues fixed η slope d t') + C.bias j₀ := by
            linarith
          simp [h, h']
        · simp [h, Bool.toNat_le]
    refine ⟨fun t => 2 * π t + b t, ?_, ?_, ?_⟩
    · intro t t' htt'
      rcases (mono htt').lt_or_eq with h | h
      · have := hb1 t
        simp only
        omega
      · have := hbmono t t' htt' h
        simp only
        omega
    · intro t
      have := lt t
      have := hb1 t
      show 2 * π t + b t < 2 ^ (activeCount fixed slope d + 1)
      rw [pow_succ]
      omega
    · intro t t' e
      simp only at e
      have h1 := hb1 t
      have h2 := hb1 t'
      have hπ : π t = π t' := by omega
      have hbb : b t = b t' := by omega
      have hgg : g t = g t' := by
        simp only [b] at hbb
        by_cases hpos : 0 < slope j₀
        · simp only [hpos, ite_true] at hbb
          exact bool_eq_of_toNat_eq _ _ hbb
        · simp only [hpos, ite_false] at hbb
          exact bool_eq_of_not_toNat_eq _ _ hbb
      rw [hsucc t, hsucc t', fac t t' hπ]
      exact congrArg _ hgg

open scoped Classical in
/-- **Lemma 2 (pieces of a run).** If every gate outside `fixed` receives the input contribution
`slope j * t`, the gate values have at most `2 ^ r` pieces as functions of `t`, where `r` counts
the gates outside `fixed` with a nonzero slope. -/
theorem piecesAtMost_evalFrom (fixed : Finset (Fin s)) (η : Fin s → Bool)
    (slope : Fin s → ℝ) :
    PiecesAtMost (fun t => C.evalFrom fixed η (fun j => slope j * t))
      (2 ^ (Finset.univ.filter fun j => j ∉ fixed ∧ slope j ≠ 0).card) := by
  have h := C.piecesAtMost_prefixValues fixed η slope s
  have heq : C.prefixValues fixed η slope s = fun t => C.evalFrom fixed η (fun j => slope j * t) :=
    by
      funext t j
      simp [prefixValues]
  have hcount : activeCount fixed slope s =
      (Finset.univ.filter fun j => j ∉ fixed ∧ slope j ≠ 0).card := by
    unfold activeCount
    congr 1
    ext j
    simp
  rw [heq, hcount] at h
  exact h

variable {C} {B : ℕ}

/-- The slope of a gate of run `i` along the direction of the run, and zero elsewhere. -/
noncomputable def DirectionRuns.slope (R : C.DirectionRuns B) (i : ℕ) (j : Fin s) : ℝ :=
  open scoped Classical in
  if R.run j = i ∧ C.inputWeight j ≠ 0 then (R.along j).choose else 0

theorem weightedSum_smul (c : ℝ) (w : Fin n → ℝ) (x : Fin n → Bool) :
    weightedSum (c • w) x = c * weightedSum w x := by
  simp [weightedSum, Finset.mul_sum, mul_assoc]

theorem weightedSum_zero (x : Fin n → Bool) : weightedSum (0 : Fin n → ℝ) x = 0 := by
  simp [weightedSum]

theorem DirectionRuns.weightedSum_eq (R : C.DirectionRuns B) {i : ℕ} {j : Fin s}
    (hj : R.run j = i) (x : Fin n → Bool) :
    weightedSum (C.inputWeight j) x = R.slope i j * weightedSum (R.dir i) x := by
  classical
  by_cases hw : C.inputWeight j = 0
  · simp [slope, hw, weightedSum_zero]
  · subst hj
    have hspec := congrArg (fun w => weightedSum w x) (R.along j).choose_spec
    simp only [weightedSum_smul] at hspec
    simp only [slope, hw, ne_eq, not_false_eq_true, and_self, ite_true]
    exact hspec

/-- The block decomposition of a program along a split into direction runs: the history after
`i` blocks holds the values of the gates of the first `i` runs. -/
noncomputable def DirectionRuns.toBlockDecomposition {f : Cslib.BooleanFunction n}
    (R : C.DirectionRuns B) (hC : C.Computes f) : BlockDecomposition f (Fin s → Bool) where
  length := B
  kind i := .oneDim (2 ^ R.size i - 1)
  history i x := fun j => if R.run j < i then C.eval x j else false
  output v := v C.output
  history_zero x y := by
    funext j
    simp
  step i _ := by
    classical
    let fixed : Finset (Fin s) := Finset.univ.filter fun j => R.run j < i
    refine ⟨R.dir i, fun η t j => if R.run j < i + 1 then
      C.evalFrom fixed η (fun k => R.slope i k * t) j else false, ?_, ?_⟩
    · intro η
      have hp := (C.piecesAtMost_evalFrom fixed η (R.slope i)).comp
        (fun v j => if R.run j < i + 1 then v j else false)
      have hcount : (Finset.univ.filter fun j => j ∉ fixed ∧ R.slope i j ≠ 0).card ≤
          R.size i := by
        unfold DirectionRuns.size
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨-, hs⟩ := hj
        have hc : R.run j = i ∧ C.inputWeight j ≠ 0 := by
          by_contra hc
          exact hs (by simp [DirectionRuns.slope, hc])
        simp [inputGates, hc.1, hc.2]
      have := (hp.mono (Nat.pow_le_pow_right two_pos hcount)).changesAtMost
      exact this
    · intro x
      funext j
      by_cases hj : R.run j < i + 1
      · simp only [hj, ite_true]
        symm
        apply C.evalFrom_eq_eval
        · intro k hk hkf
          simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hkf
          simp [hkf]
        · intro k hk hkf
          simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hkf
          have hrun : R.run k = i := by
            have := R.monotone hk
            omega
          exact (R.weightedSum_eq hrun x).symm
      · simp [hj]
  output_history x := by
    simp only [R.run_lt, ite_true]
    exact hC x

end Program

end Algebraic.Threshold

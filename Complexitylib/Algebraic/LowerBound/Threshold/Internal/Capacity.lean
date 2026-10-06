/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Changes
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proof of the one-dimensional capacity theorem

Fix a split `U` with `|U| = a` and process the blocks of a decomposition in order, keeping a
rectangle `P × Q` on which the current history is a function of the second side `q` alone.

* A one-dimensional block with `T ≥ 1` changes is `Ψ_q(α(p))` on the rectangle, where
  `⟨w, glue p q⟩ = α(p) + β(q)`. The sorted-group lemma with `2T` groups keeps a group of
  `⌊|P| / 2T⌋` elements of `P` and at least half of `Q`.
* A summary block with `V` values keeps the largest fiber of `σ`, of `⌊|P| / V⌋` elements.

At the end the output is a function of `q` on `P × Q`; keep a majority value on at least half of
`Q`. Choosing `a = ⌈log₂ (K Dₚ)⌉`, where `Dₚ` is the product of the first-side factors, both sides
have at least `K` elements whenever `4 K² · cost ≤ 2ⁿ`, contradicting two-sided
rectangle-freeness.
-/

public section

namespace Algebraic.Threshold

open Cutwidth

variable {n : ℕ}

/-- The weighted sum of a glued input splits into the two sides. -/
theorem weightedSum_glue (w : Fin n → ℝ) (U : Finset (Fin n)) (p : U → Bool)
    (q : ↥Uᶜ → Bool) :
    weightedSum w (glue U p q) =
      weightedSum w (glue U p fun _ => false) + weightedSum w (glue U (fun _ => false) q) := by
  unfold weightedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ U <;> simp [glue, hi]

namespace BlockKind

/-- The factor by which a block shrinks the first side. -/
def pcost : BlockKind → ℕ
  | oneDim T => if T = 0 then 1 else 2 * T
  | summary V => V

/-- The factor by which a block shrinks the second side. -/
def qcost : BlockKind → ℕ
  | oneDim T => if T = 0 then 1 else 2
  | summary _ => 1

theorem cost_eq_mul (κ : BlockKind) : κ.cost = κ.pcost * κ.qcost := by
  cases κ with
  | oneDim T =>
    by_cases hT : T = 0
    · simp [cost, pcost, qcost, hT]
    · simp only [cost, pcost, qcost, hT, ite_false]
      ring
  | summary V => simp [cost, pcost, qcost]

theorem qcost_pos (κ : BlockKind) : 0 < κ.qcost := by
  cases κ with
  | oneDim T => by_cases hT : T = 0 <;> simp [qcost, hT]
  | summary V => simp [qcost]

theorem pcost_pos_of_step {H : Type*} {κ : BlockKind} {prev next : (Fin n → Bool) → H}
    (h : κ.Step prev next) : 0 < κ.pcost := by
  cases κ with
  | oneDim T =>
    by_cases hT : T = 0
    · simp [pcost, hT]
    · simp only [pcost, hT, ite_false]
      omega
  | summary V =>
    obtain ⟨σ, -, -⟩ := h ∅
    exact Fin.pos (σ fun _ => false)

end BlockKind

/-- After the first `i` blocks, some rectangle with sides of at least `NP` and `NQ` elements
has the history determined by the second side. -/
def Reachable {f : Cslib.BooleanFunction n} {H : Type*} (D : BlockDecomposition f H)
    (U : Finset (Fin n)) (i NP NQ : ℕ) : Prop :=
  ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (η : (↥Uᶜ → Bool) → H),
    NP ≤ P.card ∧ NQ ≤ Q.card ∧ ∀ p ∈ P, ∀ q ∈ Q, D.history i (glue U p q) = η q

variable {f : Cslib.BooleanFunction n} {H : Type*}

theorem reachable_zero (D : BlockDecomposition f H) (U : Finset (Fin n)) :
    Reachable D U 0 (2 ^ U.card) (2 ^ Uᶜ.card) := by
  refine ⟨Finset.univ, Finset.univ, fun _ => D.history 0 (fun _ => false), ?_, ?_, ?_⟩
  · simp [Finset.card_univ, Fintype.card_bool]
  · simp [Finset.card_univ, Fintype.card_bool, Finset.card_compl]
  · intro p _ q _
    exact D.history_zero _ _

theorem reachable_succ (D : BlockDecomposition f H) (U : Finset (Fin n)) {i NP NQ : ℕ}
    (hi : i < D.length) (h : Reachable D U i NP NQ) :
    Reachable D U (i + 1) (NP / (D.kind i).pcost) (NQ / (D.kind i).qcost) := by
  classical
  obtain ⟨P, Q, η, hP, hQ, hη⟩ := h
  have hstep := D.step i hi
  have hG := BlockKind.pcost_pos_of_step hstep
  generalize D.kind i = κ at hstep hG ⊢
  cases κ with
  | oneDim T =>
    obtain ⟨w, Φ, hΦ, hnext⟩ := hstep
    let α : (U → Bool) → ℝ := fun p => weightedSum w (glue U p fun _ => false)
    let β : (↥Uᶜ → Bool) → ℝ := fun q => weightedSum w (glue U (fun _ => false) q)
    let Ψ : (↥Uᶜ → Bool) → ℝ → H := fun q t => Φ (η q) (t + β q)
    have hval : ∀ p ∈ P, ∀ q ∈ Q, D.history (i + 1) (glue U p q) = Ψ q (α p) := by
      intro p hp q hq
      rw [hnext, hη p hp q hq, weightedSum_glue]
    obtain ⟨P', hP', Qbad, hQbad, hcardP, hcardQ, hconst⟩ :=
      exists_sorted_group P Q α Ψ hG (fun q _ => (hΦ (η q)).comp_add_const (β q))
    refine ⟨P', Q.filter (· ∉ Qbad),
      fun q => if h : P'.Nonempty then Ψ q (α h.choose) else Ψ q 0, ?_, ?_, ?_⟩
    · exact (Nat.div_le_div_right hP).trans hcardP
    · have hsplit := Finset.card_filter_add_card_filter_not (s := Q) (fun q => q ∈ Qbad)
      have hin : Q.filter (· ∈ Qbad) = Qbad := by
        ext q
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun hq => hQbad hq
      rw [hin] at hsplit
      by_cases hT : T = 0
      · simp only [BlockKind.pcost, BlockKind.qcost, hT, ite_true, zero_mul, one_mul,
          Nat.le_zero, Finset.card_eq_zero] at hcardQ ⊢
        subst hcardQ
        simp only [Finset.card_empty, zero_add] at hsplit
        omega
      · simp only [BlockKind.pcost, BlockKind.qcost, hT, ite_false] at hcardQ ⊢
        have h2 : 2 * Qbad.card ≤ Q.card := by
          have hTpos : 0 < T := Nat.pos_of_ne_zero hT
          have : T * (2 * Qbad.card) ≤ T * Q.card := by linarith
          exact Nat.le_of_mul_le_mul_left this hTpos
        have : NQ / 2 ≤ Q.card / 2 := Nat.div_le_div_right hQ
        omega
    · intro p hp q hq
      have hq' := Finset.mem_filter.mp hq
      have hne : P'.Nonempty := ⟨p, hp⟩
      simp only [dite_eq_left hne]
      rw [hval p (hP' hp) q hq'.1]
      exact hconst q hq'.1 hq'.2 p hp _ hne.choose_spec
  | summary V =>
    obtain ⟨σ, Φ, hΦ⟩ := hstep U
    obtain ⟨v, -, hv⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := P) (t := Finset.univ) (f := σ) (n := P.card / V) (by simp)
      ⟨σ fun _ => false, Finset.mem_univ _⟩ (by simpa [Finset.card_univ] using Nat.mul_div_le P.card V)
    refine ⟨P.filter (σ · = v), Q, fun q => Φ (η q) v q, ?_, ?_, ?_⟩
    · exact (Nat.div_le_div_right hP).trans hv
    · simpa [BlockKind.qcost] using hQ
    · intro p hp q hq
      obtain ⟨hp, hσ⟩ := Finset.mem_filter.mp hp
      rw [hΦ, hη p hp q hq, hσ]

theorem reachable_le (D : BlockDecomposition f H) (U : Finset (Fin n)) :
    ∀ i ≤ D.length, Reachable D U i
      (2 ^ U.card / ∏ j ∈ Finset.range i, (D.kind j).pcost)
      (2 ^ Uᶜ.card / ∏ j ∈ Finset.range i, (D.kind j).qcost) := by
  intro i hi
  induction i with
  | zero => simpa using reachable_zero D U
  | succ i ih =>
    have := reachable_succ D U (by omega) (ih (by omega))
    simpa [Finset.prod_range_succ, Nat.div_div_eq_div_mul] using this

theorem not_reachable {K : ℕ} (hf : TwoSidedRectangleFree f K) (D : BlockDecomposition f H)
    (U : Finset (Fin n)) {NP NQ : ℕ} (h : Reachable D U D.length NP NQ) (hP : K ≤ NP)
    (hQ : 2 * K ≤ NQ) : False := by
  classical
  obtain ⟨P, Q, η, hNP, hNQ, hη⟩ := h
  let o : (↥Uᶜ → Bool) → Bool := fun q => D.output (η q)
  have hf' : ∀ p ∈ P, ∀ q ∈ Q, f (glue U p q) = o q := by
    intro p hp q hq
    rw [← D.output_history, hη p hp q hq]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Q) (fun q => o q = true)
  have hfalse : (Q.filter fun q => ¬ o q = true) = Q.filter fun q => o q = false := by
    ext q
    simp
  rw [hfalse] at hsplit
  have hlarge : ∃ b : Bool, K ≤ (Q.filter fun q => o q = b).card := by
    by_contra hno
    push Not at hno
    have h1 := hno true
    have h2 := hno false
    omega
  obtain ⟨b, hb⟩ := hlarge
  rcases hf U P (Q.filter fun q => o q = b) b (by
    intro p hp q hq
    obtain ⟨hq, hob⟩ := Finset.mem_filter.mp hq
    rw [hf' p hp q hq, hob]) with h | h <;> omega

/-- **Theorem U (one-dimensional capacity).** If `f` is two-sided `K`-rectangle-free, every
block decomposition of `f` has `2ⁿ < 4 K² · cost`. -/
theorem two_pow_lt_mul_cost {K : ℕ} (hf : TwoSidedRectangleFree f K)
    (D : BlockDecomposition f H) : 2 ^ n < 4 * K ^ 2 * D.cost := by
  by_contra hle
  push Not at hle
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · exfalso
      rcases hf ∅ ∅ ∅ true (by simp) with h | h <;> simp [h0] at h
    · exact h0
  set Dp := ∏ j ∈ Finset.range D.length, (D.kind j).pcost with hDpdef
  set Dq := ∏ j ∈ Finset.range D.length, (D.kind j).qcost with hDqdef
  have hcost : D.cost = Dp * Dq := by
    simp only [BlockDecomposition.cost, BlockKind.cost_eq_mul, Finset.prod_mul_distrib, Dp, Dq]
  have hDp : 0 < Dp := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj =>
    (BlockKind.pcost_pos_of_step (D.step j (Finset.mem_range.mp hj))).ne')
  have hDq : 0 < Dq := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ =>
    (BlockKind.qcost_pos _).ne')
  set a := Nat.clog 2 (K * Dp) with hadef
  have ha1 : K * Dp ≤ 2 ^ a := Nat.le_pow_clog one_lt_two _
  have ha2 : 2 ^ a < 2 * (K * Dp) := by
    rcases Nat.lt_or_ge 1 (K * Dp) with h1 | h1
    · have hlt := Nat.pow_pred_clog_lt_self one_lt_two h1
      have hpos : 0 < a := Nat.clog_pos one_lt_two h1
      rw [← hadef] at hlt
      have : 2 ^ a = 2 * 2 ^ a.pred := by
        rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel hpos]
      omega
    · have hone : K * Dp = 1 := le_antisymm h1 (Nat.mul_pos hK hDp)
      rw [hadef, hone]
      simp
  have hpos : 0 < 2 * K * Dq := by positivity
  have key : 2 ^ a * (2 * K * Dq) < 2 ^ n := by
    calc 2 ^ a * (2 * K * Dq) < 2 * (K * Dp) * (2 * K * Dq) :=
          Nat.mul_lt_mul_of_pos_right ha2 hpos
      _ = 4 * K ^ 2 * (Dp * Dq) := by ring
      _ ≤ 2 ^ n := by rw [← hcost]; exact hle
  have han : a ≤ n := by
    by_contra hna
    push Not at hna
    have : 2 ^ n ≤ 2 ^ a := Nat.pow_le_pow_right two_pos hna.le
    have : 2 ^ a ≤ 2 ^ a * (2 * K * Dq) := Nat.le_mul_of_pos_right _ hpos
    omega
  obtain ⟨U, -, hU⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (n := a) (by simpa using han)
  have hUc : Uᶜ.card = n - a := by rw [Finset.card_compl, hU, Fintype.card_fin]
  have reach := reachable_le D U D.length le_rfl
  rw [hU, hUc, ← hDpdef, ← hDqdef] at reach
  refine not_reachable hf D U reach ?_ ?_
  · rw [Nat.le_div_iff_mul_le hDp]
    exact ha1
  · rw [Nat.le_div_iff_mul_le hDq]
    have hsplit : 2 ^ n = 2 ^ a * 2 ^ (n - a) := by rw [← pow_add, Nat.add_sub_cancel' han]
    rw [hsplit] at key
    exact (Nat.lt_of_mul_lt_mul_left key).le

end Algebraic.Threshold

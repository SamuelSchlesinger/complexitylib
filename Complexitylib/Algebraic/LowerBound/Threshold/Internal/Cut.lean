/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Defs
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Split
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Capacity
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Components
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cut theorem for threshold programs

Fix a split of the coordinates into `U` and its complement, with no assumption on the supports
of the gates. Processing the gates in order while maintaining a rectangle `P × Q` on which every
earlier gate is constant, gate `m` is `[α(p) + β(q) + c ≥ 0]` on the rectangle, where
`⟨w, glue p q⟩ = α(p) + β(q)` and `c` collects the constant contributions of the earlier gates.

* If the support of the gate misses `U`, then `α = 0` and the gate is a function of `q` alone:
  keep the larger level set of `Q`, paying a factor `2` on the `Q` side (or nothing when the
  support is empty, since the gate is then constant).
* Symmetrically when the support misses `Uᶜ`.
* Otherwise take medians `μ_P` of `α` on `P` and `μ_Q` of `β` on `Q`. If `μ_P + μ_Q + c ≥ 0`,
  the gate is `1` on `{α ≥ μ_P} × {β ≥ μ_Q}`; otherwise it is `0` on `{α ≤ μ_P} × {β ≤ μ_Q}`.
  Either way both sides keep at least half, paid by the gates touching each side.

* `TwoSidedRectangleFree.lt_of_split_internal`: for every split `U`, either
  `|U| < #{j : support j ∩ U ≠ ∅} + k` or `|Uᶜ| < #{j : support j ∩ Uᶜ ≠ ∅} + k`, whenever
  `f` is two-sided `K`-rectangle-free with `K ≤ 2 ^ k`.
* `TwoSidedRectangleFree.le_two_mul_add_internal`: `n ≤ 2 (s_in + k)`.
-/

public section

namespace Algebraic.Threshold

open Cutwidth

variable {n s : ℕ}

/-- A median of a real function on a finite set: both weak level sets have at least half of
the elements. -/
theorem exists_median_internal {α : Type*} (P : Finset α) (g : α → ℝ) :
    ∃ μ : ℝ, P.card ≤ 2 * (P.filter fun p => g p ≤ μ).card ∧
      P.card ≤ 2 * (P.filter fun p => μ ≤ g p).card := by
  classical
  rcases P.eq_empty_or_nonempty with hP | hP
  · exact ⟨0, by simp [hP]⟩
  let L := P.filter fun p => P.card ≤ 2 * (P.filter fun p' => g p' ≤ g p).card
  have hL : L.Nonempty := by
    obtain ⟨pm, hpm, hmax⟩ := P.exists_max_image g hP
    refine ⟨pm, Finset.mem_filter.mpr ⟨hpm, ?_⟩⟩
    rw [Finset.filter_true_of_mem hmax]
    omega
  obtain ⟨p₀, hp₀, hmin⟩ := L.exists_min_image g hL
  obtain ⟨hp₀P, hp₀c⟩ := Finset.mem_filter.mp hp₀
  refine ⟨g p₀, hp₀c, ?_⟩
  by_contra hlt
  push Not at hlt
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) fun p => g p₀ ≤ g p
  have hne : (P.filter fun p => ¬ g p₀ ≤ g p).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨p₁, hp₁, hmax₁⟩ := (P.filter fun p => ¬ g p₀ ≤ g p).exists_max_image g hne
  obtain ⟨hp₁P, hp₁lt⟩ := Finset.mem_filter.mp hp₁
  have hsub : (P.filter fun p => ¬ g p₀ ≤ g p) ⊆ P.filter fun p' => g p' ≤ g p₁ := fun p hp =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, hmax₁ p hp⟩
  have hcard := Finset.card_le_card hsub
  exact hp₁lt (hmin p₁ (Finset.mem_filter.mpr ⟨hp₁P, by omega⟩))

/-- Keeping at least half of a side costs one more factor `2`. -/
private theorem half_step_internal {N a a' b : ℕ} (h : N ≤ a * 2 ^ b) (h2 : a ≤ 2 * a') :
    N ≤ a' * 2 ^ (b + 1) := by
  rw [pow_succ]
  calc N ≤ a * 2 ^ b := h
    _ ≤ 2 * a' * 2 ^ b := Nat.mul_le_mul_right _ h2
    _ = a' * (2 ^ b * 2) := by ring

/-- From `2 ^ N ≤ a · 2 ^ t` and `t + k ≤ N`, the side has at least `2 ^ k ≥ K` elements. -/
private theorem le_card_of_pow_le_internal {N a k K t : ℕ} (h : 2 ^ N ≤ a * 2 ^ t)
    (hN : t + k ≤ N) (hK : K ≤ 2 ^ k) : K ≤ a := by
  have h1 : 2 ^ (t + k) ≤ a * 2 ^ t := le_trans (Nat.pow_le_pow_right (by norm_num) hN) h
  rw [pow_add, mul_comm] at h1
  have := le_of_mul_le_mul_right h1 (Nat.two_pow_pos t)
  omega

namespace Program

/-- The number of gates below `m` whose support meets `S`. -/
noncomputable def touchBelow (C : Program n s) (S : Finset (Fin n)) (m : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin s => j.1 < m ∧ (C.support j ∩ S).Nonempty).card

private theorem filter_lt_succ_card_internal (pred : Fin s → Prop) [DecidablePred pred] {m : ℕ}
    (j₀ : Fin s) (hj₀ : j₀.1 = m) :
    (Finset.univ.filter fun j : Fin s => j.1 < m + 1 ∧ pred j).card =
      (Finset.univ.filter fun j : Fin s => j.1 < m ∧ pred j).card +
        if pred j₀ then 1 else 0 := by
  by_cases hp : pred j₀
  · rw [ite_eq_left hp, ← Finset.card_insert_of_notMem (s := Finset.univ.filter fun j : Fin s =>
      j.1 < m ∧ pred j) (a := j₀) (by simp [hj₀])]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hj : j.1 = m
      · exact Or.inl (Fin.ext (hj.trans hj₀.symm))
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨by omega, h2⟩
  · rw [ite_eq_right hp, add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hj
      have : j = j₀ := Fin.ext (by omega)
      subst this
      exact hp h2
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩

theorem touchBelow_succ (C : Program n s) (S : Finset (Fin n)) {m : ℕ} (j₀ : Fin s)
    (hj₀ : j₀.1 = m) :
    C.touchBelow S (m + 1) = C.touchBelow S m + if (C.support j₀ ∩ S).Nonempty then 1 else 0 :=
  filter_lt_succ_card_internal (fun j => (C.support j ∩ S).Nonempty) j₀ hj₀

theorem touchBelow_zero (C : Program n s) (S : Finset (Fin n)) : C.touchBelow S 0 = 0 := by
  simp [touchBelow]

theorem touchBelow_top (C : Program n s) (S : Finset (Fin n)) :
    C.touchBelow S s = (Finset.univ.filter fun j => (C.support j ∩ S).Nonempty).card := by
  unfold touchBelow
  congr 1
  ext j
  simp

/-- The invariant after the first `m` gates: a rectangle `P × Q` on which every gate below `m`
takes the value `v`, whose sides have lost at most a factor `2` per gate touching them. -/
def CutInv (C : Program n s) (U : Finset (Fin n)) (m : ℕ) : Prop :=
  ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (v : Fin s → Bool),
    (∀ p ∈ P, ∀ q ∈ Q, ∀ k : Fin s, k.1 < m → C.eval (glue U p q) k = v k) ∧
    2 ^ U.card ≤ P.card * 2 ^ C.touchBelow U m ∧
    2 ^ Uᶜ.card ≤ Q.card * 2 ^ C.touchBelow Uᶜ m

theorem cutInv_zero (C : Program n s) (U : Finset (Fin n)) : C.CutInv U 0 := by
  refine ⟨Finset.univ, Finset.univ, fun _ => false,
    fun p _ q _ k hk => absurd hk (Nat.not_lt_zero _), ?_, ?_⟩
  · rw [touchBelow_zero, pow_zero, mul_one, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe]
  · rw [touchBelow_zero, pow_zero, mul_one, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe]

theorem cutInv_succ (C : Program n s) (U : Finset (Fin n)) {m : ℕ} (hm : m < s)
    (h : C.CutInv U m) : C.CutInv U (m + 1) := by
  classical
  obtain ⟨P, Q, v, hv, hP, hQ⟩ := h
  set j₀ : Fin s := ⟨m, hm⟩ with hj₀
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = (∑ k : Fin s, if k < j₀ then C.gateWeight j₀ k * (v k).toNat else 0) + C.bias j₀ :=
    ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (U → Bool) → ℝ,
      ∀ p, α p = weightedSum (C.inputWeight j₀) (glue U p fun _ => false) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : (↥Uᶜ → Bool) → ℝ,
      ∀ q, β q = weightedSum (C.inputWeight j₀) (glue U (fun _ => false) q) :=
    ⟨_, fun _ => rfl⟩
  have hgate : ∀ p ∈ P, ∀ q ∈ Q, C.eval (glue U p q) j₀ = decide (0 ≤ α p + β q + c) := by
    intro p hp q hq
    rw [C.eval_eq_of_lt_internal (glue U p q) v j₀ fun k hk => hv p hp q hq k (Fin.lt_def.mp hk),
      weightedSum_glue, ← hα, ← hβ, ← hc]
  have htU := C.touchBelow_succ U j₀ rfl
  have htV := C.touchBelow_succ Uᶜ j₀ rfl
  -- Extending the value vector by the constant value of gate `j₀` on a subrectangle.
  have hext : ∀ (b : Bool) (P' : Finset (U → Bool)) (Q' : Finset (↥Uᶜ → Bool)), P' ⊆ P →
      Q' ⊆ Q → (∀ p ∈ P', ∀ q ∈ Q', C.eval (glue U p q) j₀ = b) →
      ∀ p ∈ P', ∀ q ∈ Q', ∀ k : Fin s, k.1 < m + 1 →
        C.eval (glue U p q) k = Function.update v j₀ b k := by
    intro b P' Q' hP' hQ' hb p hp q hq k hk
    by_cases hkj : k = j₀
    · subst hkj
      rw [Function.update_self]
      exact hb p hp q hq
    · rw [Function.update_of_ne hkj]
      have hkm : k.1 ≠ m := fun h => hkj (Fin.ext h)
      exact hv p (hP' hp) q (hQ' hq) k (by omega)
  -- A side missed by the support contributes nothing.
  have hαzero : ¬ (C.support j₀ ∩ U).Nonempty → ∀ p, α p = 0 := by
    intro hU p
    rw [hα]
    refine weightedSum_eq_zero_internal _ fun i hi => ?_
    have hiU : i ∉ U := fun hiU =>
      hU ⟨i, Finset.mem_inter.mpr ⟨(C.mem_support_internal j₀ i).mpr hi, hiU⟩⟩
    simp [glue, hiU]
  have hβzero : ¬ (C.support j₀ ∩ Uᶜ).Nonempty → ∀ q, β q = 0 := by
    intro hV q
    rw [hβ]
    refine weightedSum_eq_zero_internal _ fun i hi => ?_
    have hiU : i ∈ U := by
      by_contra hiU
      exact hV ⟨i, Finset.mem_inter.mpr ⟨(C.mem_support_internal j₀ i).mpr hi,
        Finset.mem_compl.mpr hiU⟩⟩
    simp [glue, hiU]
  by_cases hU : (C.support j₀ ∩ U).Nonempty <;> by_cases hV : (C.support j₀ ∩ Uᶜ).Nonempty
  · -- The support meets both sides: cut both at a median.
    rw [ite_eq_left hU] at htU
    rw [ite_eq_left hV] at htV
    obtain ⟨μP, hPlo, hPhi⟩ := exists_median_internal P α
    obtain ⟨μQ, hQlo, hQhi⟩ := exists_median_internal Q β
    by_cases hμ : 0 ≤ μP + μQ + c
    · refine ⟨P.filter fun p => μP ≤ α p, Q.filter fun q => μQ ≤ β q, Function.update v j₀ true,
        hext true _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) fun p hp q hq => ?_,
        by rw [htU]; exact half_step_internal hP hPhi,
        by rw [htV]; exact half_step_internal hQ hQhi⟩
      obtain ⟨hp, hpμ⟩ := Finset.mem_filter.mp hp
      obtain ⟨hq, hqμ⟩ := Finset.mem_filter.mp hq
      rw [hgate p hp q hq, decide_eq_true_eq]
      linarith
    · refine ⟨P.filter fun p => α p ≤ μP, Q.filter fun q => β q ≤ μQ, Function.update v j₀ false,
        hext false _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) fun p hp q hq => ?_,
        by rw [htU]; exact half_step_internal hP hPlo,
        by rw [htV]; exact half_step_internal hQ hQlo⟩
      obtain ⟨hp, hpμ⟩ := Finset.mem_filter.mp hp
      obtain ⟨hq, hqμ⟩ := Finset.mem_filter.mp hq
      rw [hgate p hp q hq, decide_eq_false_iff_not]
      intro h0
      exact hμ (by linarith)
  · -- The support misses `Uᶜ`: the gate depends on `p` alone; halve `P`.
    rw [ite_eq_left hU] at htU
    rw [ite_eq_right hV, add_zero] at htV
    obtain ⟨b, hb⟩ := exists_half_internal P fun p => decide (0 ≤ α p + c)
    refine ⟨P.filter fun p => decide (0 ≤ α p + c) = b, Q, Function.update v j₀ b,
      hext b _ Q (Finset.filter_subset _ _) subset_rfl fun p hp q hq => ?_,
      by rw [htU]; exact half_step_internal hP hb, by rwa [htV]⟩
    obtain ⟨hp, hpb⟩ := Finset.mem_filter.mp hp
    rw [hgate p hp q hq, hβzero hV q, add_zero]
    exact hpb
  · -- The support misses `U`: the gate depends on `q` alone; halve `Q`.
    rw [ite_eq_right hU, add_zero] at htU
    rw [ite_eq_left hV] at htV
    obtain ⟨b, hb⟩ := exists_half_internal Q fun q => decide (0 ≤ β q + c)
    refine ⟨P, Q.filter fun q => decide (0 ≤ β q + c) = b, Function.update v j₀ b,
      hext b P _ subset_rfl (Finset.filter_subset _ _) fun p hp q hq => ?_,
      by rwa [htU], by rw [htV]; exact half_step_internal hQ hb⟩
    obtain ⟨hq, hqb⟩ := Finset.mem_filter.mp hq
    rw [hgate p hp q hq, hαzero hU p, zero_add]
    exact hqb
  · -- The support is empty: the gate is constant on the rectangle.
    rw [ite_eq_right hU, add_zero] at htU
    rw [ite_eq_right hV, add_zero] at htV
    refine ⟨P, Q, Function.update v j₀ (decide (0 ≤ c)),
      hext _ P Q subset_rfl subset_rfl fun p hp q hq => ?_, by rwa [htU], by rwa [htV]⟩
    rw [hgate p hp q hq, hαzero hU p, hβzero hV q, zero_add, zero_add]

theorem cutInv_all (C : Program n s) (U : Finset (Fin n)) : ∀ m ≤ s, C.CutInv U m := by
  intro m hm
  induction m with
  | zero => exact C.cutInv_zero U
  | succ m ih => exact C.cutInv_succ U (by omega) (ih (by omega))

/-- **The cut lemma.** For every split `U` there is a rectangle `P × Q` on which `f` is
constant, with `2 ^ |U| ≤ |P| · 2 ^ #{j : support j ∩ U ≠ ∅}` and symmetrically for `Q`. -/
theorem exists_rectangle_of_cut_internal (C : Program n s) {f : Cslib.BooleanFunction n}
    (hC : C.Computes f) (U : Finset (Fin n)) :
    ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (b : Bool),
      (∀ p ∈ P, ∀ q ∈ Q, f (glue U p q) = b) ∧
      2 ^ U.card ≤ P.card * 2 ^ (Finset.univ.filter fun j => (C.support j ∩ U).Nonempty).card ∧
      2 ^ Uᶜ.card ≤
        Q.card * 2 ^ (Finset.univ.filter fun j => (C.support j ∩ Uᶜ).Nonempty).card := by
  obtain ⟨P, Q, v, hv, hP, hQ⟩ := C.cutInv_all U s le_rfl
  rw [touchBelow_top] at hP hQ
  refine ⟨P, Q, v C.output, fun p hp q hq => ?_, hP, hQ⟩
  rw [← hC, hv p hp q hq C.output C.output.2]

/-- Gates whose support meets `S` are input-reading. -/
theorem card_filter_touch_le_inputGates (C : Program n s) (S : Finset (Fin n)) :
    (Finset.univ.filter fun j => (C.support j ∩ S).Nonempty).card ≤ C.inputGates.card := by
  classical
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [inputGates, Finset.mem_filter, inputWeight_ne_zero_iff]
  exact ⟨Finset.mem_univ _, (hj.2.mono Finset.inter_subset_left).ne_empty⟩

end Program

variable {f : Cslib.BooleanFunction n} {K : ℕ}

/-- **The cut theorem.** If `C` computes a two-sided `K`-rectangle-free function with
`K ≤ 2 ^ k`, then under every split `U` one side has fewer than `k` more coordinates than gates
touching it. -/
theorem TwoSidedRectangleFree.lt_of_split_internal (hf : TwoSidedRectangleFree f K)
    {C : Program n s} (hC : C.Computes f) (U : Finset (Fin n)) {k : ℕ} (hK : K ≤ 2 ^ k) :
    U.card < (Finset.univ.filter fun j => (C.support j ∩ U).Nonempty).card + k ∨
    Uᶜ.card < (Finset.univ.filter fun j => (C.support j ∩ Uᶜ).Nonempty).card + k := by
  obtain ⟨P, Q, b, hb, hP, hQ⟩ := C.exists_rectangle_of_cut_internal hC U
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have hPK : K ≤ P.card := le_card_of_pow_le_internal hP h1 hK
  have hQK : K ≤ Q.card := le_card_of_pow_le_internal hQ h2 hK
  rcases hf U P Q b hb with h | h <;> omega

/-- **The cut bound.** If `C` computes a two-sided `K`-rectangle-free function with
`K ≤ 2 ^ k`, then `n ≤ 2 (s_in + k)`. -/
theorem TwoSidedRectangleFree.le_two_mul_add_internal (hf : TwoSidedRectangleFree f K)
    {C : Program n s} (hC : C.Computes f) {k : ℕ} (hK : K ≤ 2 ^ k) :
    n ≤ 2 * (C.inputGates.card + k) := by
  classical
  let U : Finset (Fin n) :=
    (Finset.univ : Finset (Fin (n / 2))).map (Fin.castLEEmb (Nat.div_le_self n 2))
  have hU : U.card = n / 2 := by simp [U]
  have hUc : Uᶜ.card = n - n / 2 := by rw [Finset.card_compl, Fintype.card_fin, hU]
  have h1 := C.card_filter_touch_le_inputGates U
  have h2 := C.card_filter_touch_le_inputGates Uᶜ
  rcases hf.lt_of_split_internal hC U hK with h | h <;> omega

end Algebraic.Threshold

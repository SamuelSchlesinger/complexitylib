/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Defs
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Program
import Mathlib.Tactic.Ring

/-!
# The split lemma for threshold programs

Fix a split of the coordinates into `U` and its complement, and suppose every gate of a
threshold program reads inputs from one side only (`C.support j ⊆ U` or `C.support j ⊆ Uᶜ`).
Processing the gates in order while maintaining a rectangle `P × Q` on which every earlier gate
is constant, a gate reading only `U` is a function of `p` alone on the rectangle, so splitting
`P` by its value and keeping the larger half costs a factor `2` on `P`; a gate whose support
lies in a fixed set `A ⊆ U` on which all of `P` agrees is constant and costs nothing. The second
side is symmetric with `B ⊆ Uᶜ`.

* `exists_rectangle_of_split_internal`: starting from the inputs vanishing on `A` and on `B`,
  the final rectangle has `f` constant, with
  `2 ^ (|U| - |A|) ≤ |P| · 2 ^ #{j : support j ⊆ U, support j ⊄ A}` and symmetrically for `Q`.
-/

public section

namespace Algebraic.Threshold

open Cutwidth

variable {n s : ℕ}

theorem weightedSum_congr_internal (w : Fin n → ℝ) {x y : Fin n → Bool}
    (h : ∀ i, w i ≠ 0 → x i = y i) : weightedSum w x = weightedSum w y := by
  unfold weightedSum
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hw : w i = 0
  · simp [hw]
  · rw [h i hw]

theorem weightedSum_eq_zero_internal (w : Fin n → ℝ) {x : Fin n → Bool}
    (h : ∀ i, w i ≠ 0 → x i = false) : weightedSum w x = 0 := by
  rw [weightedSum_congr_internal w (y := fun _ => false) h]
  simp [weightedSum]

namespace Program

theorem mem_support_internal (C : Program n s) (j : Fin s) (i : Fin n) :
    i ∈ C.support j ↔ C.inputWeight j i ≠ 0 := by
  simp [support]

theorem eval_eq_of_lt_internal (C : Program n s) (x : Fin n → Bool) (v : Fin s → Bool)
    (j : Fin s) (hv : ∀ k, k < j → C.eval x k = v k) :
    C.eval x j = decide (0 ≤ weightedSum (C.inputWeight j) x +
      ((∑ k : Fin s, if k < j then C.gateWeight j k * (v k).toNat else 0) + C.bias j)) := by
  rw [eval_eq_internal, add_assoc]
  have hsum : (∑ k : Fin s, if k < j then C.gateWeight j k * (C.eval x k).toNat else 0) =
      ∑ k : Fin s, if k < j then C.gateWeight j k * (v k).toNat else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rw [hv k hk]
    · rfl
  rw [hsum]

/-- A gate whose support lies in `U` reads a glued input through `p` alone. -/
theorem weightedSum_glue_left_internal (C : Program n s) {j : Fin s} {U : Finset (Fin n)}
    (hU : C.support j ⊆ U) (p : U → Bool) (q q' : ↥Uᶜ → Bool) :
    weightedSum (C.inputWeight j) (glue U p q) = weightedSum (C.inputWeight j) (glue U p q') :=
  weightedSum_congr_internal _ fun i hi => by
    have hiU : i ∈ U := hU ((C.mem_support_internal j i).mpr hi)
    simp [glue, hiU]

/-- A gate whose support lies in `Uᶜ` reads a glued input through `q` alone. -/
theorem weightedSum_glue_right_internal (C : Program n s) {j : Fin s} {U : Finset (Fin n)}
    (hU : C.support j ⊆ Uᶜ) (p p' : U → Bool) (q : ↥Uᶜ → Bool) :
    weightedSum (C.inputWeight j) (glue U p q) = weightedSum (C.inputWeight j) (glue U p' q) :=
  weightedSum_congr_internal _ fun i hi => by
    have hiU : i ∉ U := Finset.mem_compl.mp (hU ((C.mem_support_internal j i).mpr hi))
    simp [glue, hiU]

/-- The number of gates below `m` whose support lies in `S` but not in `T`. -/
noncomputable def countBelow (C : Program n s) (S T : Finset (Fin n)) (m : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin s => j.1 < m ∧ C.support j ⊆ S ∧ ¬ C.support j ⊆ T).card

private theorem filter_lt_succ_card (pred : Fin s → Prop) [DecidablePred pred] {m : ℕ}
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

theorem countBelow_succ (C : Program n s) (S T : Finset (Fin n)) {m : ℕ} (j₀ : Fin s)
    (hj₀ : j₀.1 = m) :
    C.countBelow S T (m + 1) = C.countBelow S T m +
      if C.support j₀ ⊆ S ∧ ¬ C.support j₀ ⊆ T then 1 else 0 :=
  filter_lt_succ_card (fun j => C.support j ⊆ S ∧ ¬ C.support j ⊆ T) j₀ hj₀

theorem countBelow_zero (C : Program n s) (S T : Finset (Fin n)) : C.countBelow S T 0 = 0 := by
  simp [countBelow]

theorem countBelow_top (C : Program n s) (S T : Finset (Fin n)) :
    C.countBelow S T s =
      (Finset.univ.filter fun j => C.support j ⊆ S ∧ ¬ C.support j ⊆ T).card := by
  unfold countBelow
  congr 1
  ext j
  simp

end Program

/-- Some side of a split by a Boolean function keeps at least half of a finite set. -/
theorem exists_half_internal {α : Type*} (P : Finset α) (g : α → Bool) :
    ∃ b : Bool, P.card ≤ 2 * (P.filter fun p => g p = b).card := by
  have h := Finset.card_filter_add_card_filter_not (s := P) (fun p => g p = true)
  have hf : (P.filter fun p => ¬ g p = true) = P.filter fun p => g p = false := by
    ext p
    simp
  rw [hf] at h
  by_contra hno
  push Not at hno
  have h1 := hno true
  have h2 := hno false
  omega

/-- The assignments to `S` vanishing on `A ⊆ S` number `2 ^ (|S| - |A|)`. -/
theorem exists_initial_internal (S A : Finset (Fin n)) (hA : A ⊆ S) :
    ∃ P : Finset (S → Bool), 2 ^ (S.card - A.card) ≤ P.card ∧
      ∀ p ∈ P, ∀ i : S, (i : Fin n) ∈ A → p i = false := by
  classical
  let ext : (↥(S \ A) → Bool) → (S → Bool) := fun g i =>
    if h : (i : Fin n) ∈ S \ A then g ⟨i, h⟩ else false
  have hinj : Function.Injective ext := by
    intro g g' hgg
    funext i
    have := congrFun hgg ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩
    simp only [ext] at this
    rwa [dite_eq_left i.2, dite_eq_left i.2] at this
  refine ⟨Finset.univ.image ext, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_coe, Finset.card_sdiff_of_subset hA]
  · intro p hp i hi
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hp
    simp [ext, hi]

namespace Program

/-- The invariant after the first `m` gates: a rectangle `P × Q`, with `P` vanishing on `A`
and `Q` vanishing on `B`, on which every gate below `m` takes the value `v`, and whose sides
have lost at most a factor `2` per counted gate. -/
def SplitInv (C : Program n s) (U A B : Finset (Fin n)) (m : ℕ) : Prop :=
  ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (v : Fin s → Bool),
    (∀ p ∈ P, ∀ i : U, (i : Fin n) ∈ A → p i = false) ∧
    (∀ q ∈ Q, ∀ i : ↥Uᶜ, (i : Fin n) ∈ B → q i = false) ∧
    (∀ p ∈ P, ∀ q ∈ Q, ∀ k : Fin s, k.1 < m → C.eval (glue U p q) k = v k) ∧
    2 ^ (U.card - A.card) ≤ P.card * 2 ^ C.countBelow U A m ∧
    2 ^ (Uᶜ.card - B.card) ≤ Q.card * 2 ^ C.countBelow Uᶜ B m

theorem splitInv_zero (C : Program n s) {U A B : Finset (Fin n)} (hA : A ⊆ U) (hB : B ⊆ Uᶜ) :
    C.SplitInv U A B 0 := by
  obtain ⟨P, hP, hPA⟩ := exists_initial_internal U A hA
  obtain ⟨Q, hQ, hQB⟩ := exists_initial_internal Uᶜ B hB
  refine ⟨P, Q, fun _ => false, hPA, hQB, fun p _ q _ k hk => absurd hk (Nat.not_lt_zero _),
    ?_, ?_⟩
  · simpa [countBelow_zero] using hP
  · simpa [countBelow_zero] using hQ

theorem splitInv_succ (C : Program n s) {U A B : Finset (Fin n)} (hA : A ⊆ U) (hB : B ⊆ Uᶜ)
    (hsplit : ∀ j, C.support j ⊆ U ∨ C.support j ⊆ Uᶜ) {m : ℕ} (hm : m < s)
    (h : C.SplitInv U A B m) : C.SplitInv U A B (m + 1) := by
  classical
  obtain ⟨P, Q, v, hPA, hQB, hv, hP, hQ⟩ := h
  set j₀ : Fin s := ⟨m, hm⟩ with hj₀
  have hgate : ∀ p ∈ P, ∀ q ∈ Q, C.eval (glue U p q) j₀ =
      decide (0 ≤ weightedSum (C.inputWeight j₀) (glue U p q) +
        ((∑ k : Fin s, if k < j₀ then C.gateWeight j₀ k * (v k).toNat else 0) + C.bias j₀)) :=
    fun p hp q hq => C.eval_eq_of_lt_internal (glue U p q) v j₀
      fun k hk => hv p hp q hq k (Fin.lt_def.mp hk)
  set c : ℝ := (∑ k : Fin s, if k < j₀ then C.gateWeight j₀ k * (v k).toNat else 0) + C.bias j₀
    with hc
  have hcU := C.countBelow_succ U A j₀ rfl
  have hcB := C.countBelow_succ Uᶜ B j₀ rfl
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
  -- A support inside both sides is empty, hence inside every set.
  have hboth : C.support j₀ ⊆ U → C.support j₀ ⊆ Uᶜ → ∀ T : Finset (Fin n), C.support j₀ ⊆ T :=
    fun h1 h2 T i hi => (Finset.mem_compl.mp (h2 hi) (h1 hi)).elim
  rcases hsplit j₀ with hU | hUc
  · have hcB' : C.countBelow Uᶜ B (m + 1) = C.countBelow Uᶜ B m := by
      rw [hcB, ite_eq_right fun h => h.2 (hboth hU h.1 B), add_zero]
    by_cases hAsub : C.support j₀ ⊆ A
    · -- The gate is constant on the rectangle.
      have hzero : ∀ p ∈ P, ∀ q, weightedSum (C.inputWeight j₀) (glue U p q) = 0 := by
        intro p hp q
        refine weightedSum_eq_zero_internal _ fun i hi => ?_
        have hiA : i ∈ A := hAsub ((C.mem_support_internal j₀ i).mpr hi)
        have hiU : i ∈ U := hA hiA
        simp only [glue, hiU, dite_true]
        exact hPA p hp ⟨i, hiU⟩ hiA
      have hcU' : C.countBelow U A (m + 1) = C.countBelow U A m := by
        rw [hcU, ite_eq_right fun h => h.2 hAsub, add_zero]
      refine ⟨P, Q, Function.update v j₀ (decide (0 ≤ c)), hPA, hQB,
        hext _ P Q subset_rfl subset_rfl fun p hp q hq => ?_, by rwa [hcU'], by rwa [hcB']⟩
      rw [hgate p hp q hq, hzero p hp q, zero_add]
    · -- Split `P` by the value of the gate and keep the larger half.
      let g : (U → Bool) → Bool := fun p =>
        decide (0 ≤ weightedSum (C.inputWeight j₀) (glue U p fun _ => false) + c)
      obtain ⟨b, hb⟩ := exists_half_internal P g
      have hcU' : C.countBelow U A (m + 1) = C.countBelow U A m + 1 := by
        rw [hcU, ite_eq_left ⟨hU, hAsub⟩]
      refine ⟨P.filter fun p => g p = b, Q, Function.update v j₀ b,
        fun p hp => hPA p (Finset.mem_filter.mp hp).1, hQB,
        hext b _ Q (Finset.filter_subset _ _) subset_rfl fun p hp q hq => ?_, ?_, by rwa [hcB']⟩
      · obtain ⟨hp, hgp⟩ := Finset.mem_filter.mp hp
        rw [hgate p hp q hq, C.weightedSum_glue_left_internal hU p q fun _ => false]
        exact hgp
      · rw [hcU', pow_succ]
        calc 2 ^ (U.card - A.card) ≤ P.card * 2 ^ C.countBelow U A m := hP
          _ ≤ 2 * (P.filter fun p => g p = b).card * 2 ^ C.countBelow U A m :=
            Nat.mul_le_mul_right _ hb
          _ = (P.filter fun p => g p = b).card * (2 ^ C.countBelow U A m * 2) := by ring
  · have hcU' : C.countBelow U A (m + 1) = C.countBelow U A m := by
      rw [hcU, ite_eq_right fun h => h.2 (hboth h.1 hUc A), add_zero]
    by_cases hBsub : C.support j₀ ⊆ B
    · -- The gate is constant on the rectangle.
      have hzero : ∀ p, ∀ q ∈ Q, weightedSum (C.inputWeight j₀) (glue U p q) = 0 := by
        intro p q hq
        refine weightedSum_eq_zero_internal _ fun i hi => ?_
        have hiB : i ∈ B := hBsub ((C.mem_support_internal j₀ i).mpr hi)
        have hiU : i ∉ U := Finset.mem_compl.mp (hB hiB)
        simp only [glue, hiU, dite_false]
        exact hQB q hq ⟨i, Finset.mem_compl.mpr hiU⟩ hiB
      have hcB' : C.countBelow Uᶜ B (m + 1) = C.countBelow Uᶜ B m := by
        rw [hcB, ite_eq_right fun h => h.2 hBsub, add_zero]
      refine ⟨P, Q, Function.update v j₀ (decide (0 ≤ c)), hPA, hQB,
        hext _ P Q subset_rfl subset_rfl fun p hp q hq => ?_, by rwa [hcU'], by rwa [hcB']⟩
      rw [hgate p hp q hq, hzero p q hq, zero_add]
    · -- Split `Q` by the value of the gate and keep the larger half.
      let g : (↥Uᶜ → Bool) → Bool := fun q =>
        decide (0 ≤ weightedSum (C.inputWeight j₀) (glue U (fun _ => false) q) + c)
      obtain ⟨b, hb⟩ := exists_half_internal Q g
      have hcB' : C.countBelow Uᶜ B (m + 1) = C.countBelow Uᶜ B m + 1 := by
        rw [hcB, ite_eq_left ⟨hUc, hBsub⟩]
      refine ⟨P, Q.filter fun q => g q = b, Function.update v j₀ b, hPA,
        fun q hq => hQB q (Finset.mem_filter.mp hq).1,
        hext b P _ subset_rfl (Finset.filter_subset _ _) fun p hp q hq => ?_, by rwa [hcU'], ?_⟩
      · obtain ⟨hq, hgq⟩ := Finset.mem_filter.mp hq
        rw [hgate p hp q hq, C.weightedSum_glue_right_internal hUc p (fun _ => false) q]
        exact hgq
      · rw [hcB', pow_succ]
        calc 2 ^ (Uᶜ.card - B.card) ≤ Q.card * 2 ^ C.countBelow Uᶜ B m := hQ
          _ ≤ 2 * (Q.filter fun q => g q = b).card * 2 ^ C.countBelow Uᶜ B m :=
            Nat.mul_le_mul_right _ hb
          _ = (Q.filter fun q => g q = b).card * (2 ^ C.countBelow Uᶜ B m * 2) := by ring

theorem splitInv_all (C : Program n s) {U A B : Finset (Fin n)} (hA : A ⊆ U) (hB : B ⊆ Uᶜ)
    (hsplit : ∀ j, C.support j ⊆ U ∨ C.support j ⊆ Uᶜ) : ∀ m ≤ s, C.SplitInv U A B m := by
  intro m hm
  induction m with
  | zero => exact C.splitInv_zero hA hB
  | succ m ih => exact C.splitInv_succ hA hB hsplit (by omega) (ih (by omega))

/-- **The split lemma.** If every gate of `C` reads inputs from `U` only or from `Uᶜ` only,
then for all `A ⊆ U` and `B ⊆ Uᶜ` there is a rectangle `P × Q` on which `f` is constant, with
`2 ^ (|U| - |A|) ≤ |P| · 2 ^ #{j : support j ⊆ U, support j ⊄ A}` and
`2 ^ (|Uᶜ| - |B|) ≤ |Q| · 2 ^ #{j : support j ⊆ Uᶜ, support j ⊄ B}`. -/
theorem exists_rectangle_of_split_internal (C : Program n s) {f : Cslib.BooleanFunction n}
    (hC : C.Computes f) (U A B : Finset (Fin n)) (hA : A ⊆ U) (hB : B ⊆ Uᶜ)
    (hsplit : ∀ j, C.support j ⊆ U ∨ C.support j ⊆ Uᶜ) :
    ∃ (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) (b : Bool),
      (∀ p ∈ P, ∀ q ∈ Q, f (glue U p q) = b) ∧
      2 ^ (U.card - A.card) ≤ P.card *
        2 ^ (Finset.univ.filter fun j => C.support j ⊆ U ∧ ¬ C.support j ⊆ A).card ∧
      2 ^ (Uᶜ.card - B.card) ≤ Q.card *
        2 ^ (Finset.univ.filter fun j => C.support j ⊆ Uᶜ ∧ ¬ C.support j ⊆ B).card := by
  obtain ⟨P, Q, v, -, -, hv, hP, hQ⟩ := C.splitInv_all hA hB hsplit s le_rfl
  rw [countBelow_top] at hP hQ
  refine ⟨P, Q, v C.output, fun p hp q hq => ?_, hP, hQ⟩
  rw [← hC, hv p hp q hq C.output C.output.2]

end Program

end Algebraic.Threshold

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Split
import Complexitylib.Algebraic.LowerBound.Threshold.Internal.Program
import Mathlib.Tactic.Ring

/-!
# The excess bound for threshold programs

Fix a set `F` of inputs and a family `𝓑` of pairwise disjoint blocks covering the remaining
inputs, such that every gate either reads inputs from `F` only or has its residual support
(outside `F`) inside a single block. Write `e_b` for the number of gates whose nonempty residual
support lies in the block `b`, and `φ_b := |b| - e_b` for the *excess* of the block. If every
excess is at most `M` and the program computes a two-sided `K`-rectangle-free function with
`K ≤ 2 ^ k`, then `n < |F| + s_in + M + 2k`.

The proof disconnects the inputs of `F` (`Program.restrictInputs`), which turns the residual
supports into the supports of a program computing the restriction of `f` with the inputs of `F`
fixed to `false`. The blocks then split into two groups of excess at least `k` each
(`exists_subset_sum_ge_internal`), and the split lemma applied to the union `U` of one group,
with the saturated blocks (`φ_b = 0`) fixed, yields a rectangle `P × Q` for the restricted
function. Fixing the coordinates of `F ⊆ Uᶜ` to `false` on the `Q` side (`fixFalseRight`)
gives a rectangle for `f` itself, shrinking `Q` by a factor of at most `2 ^ |F|`
(`card_le_card_image_fixFalseRight`), which the count of `Uᶜ` absorbs. Both sides then have at
least `2 ^ k` elements.
-/

public section

namespace Algebraic.Threshold

open Cutwidth

variable {n s : ℕ}

/-- **Subset sum.** Items of value at most `M` with total value at least `2k + M` split into two
groups of value at least `k` each. -/
theorem exists_subset_sum_ge_internal {ι : Type*} [DecidableEq ι] (𝓑 : Finset ι) (φ : ι → ℕ)
    (M k : ℕ) (hφ : ∀ b ∈ 𝓑, φ b ≤ M) (htot : 2 * k + M ≤ ∑ b ∈ 𝓑, φ b) :
    ∃ 𝒢 ⊆ 𝓑, k ≤ ∑ b ∈ 𝒢, φ b ∧ k ≤ ∑ b ∈ 𝓑 \ 𝒢, φ b := by
  -- Adding items one at a time, the partial sum first reaches `k` below `k + M`.
  have key : ∀ 𝓑 : Finset ι, (∀ b ∈ 𝓑, φ b ≤ M) → k ≤ ∑ b ∈ 𝓑, φ b →
      ∃ 𝒢 ⊆ 𝓑, k ≤ ∑ b ∈ 𝒢, φ b ∧ ∑ b ∈ 𝒢, φ b ≤ k + M - 1 := by
    intro 𝓑
    induction 𝓑 using Finset.induction_on with
    | empty =>
      intro _ hk
      rw [Finset.sum_empty] at hk
      exact ⟨∅, Finset.Subset.refl _, by simpa using hk, by simp⟩
    | insert a t ha ih =>
      intro hφ hk
      rw [Finset.sum_insert ha] at hk
      by_cases hkt : k ≤ ∑ b ∈ t, φ b
      · obtain ⟨𝒢, h𝒢, h1, h2⟩ := ih (fun b hb => hφ b (Finset.mem_insert_of_mem hb)) hkt
        exact ⟨𝒢, h𝒢.trans (Finset.subset_insert _ _), h1, h2⟩
      · refine ⟨insert a t, Finset.Subset.refl _, ?_, ?_⟩
        · rw [Finset.sum_insert ha]
          exact hk
        · rw [Finset.sum_insert ha]
          have := hφ a (Finset.mem_insert_self _ _)
          omega
  obtain ⟨𝒢, h𝒢, h1, h2⟩ := key 𝓑 hφ (by omega)
  refine ⟨𝒢, h𝒢, h1, ?_⟩
  have := Finset.sum_sdiff (f := φ) h𝒢
  omega

/-- The arithmetic closing step of a split: from `2 ^ d ≤ P · 2 ^ g` with `k + g ≤ d` and
`K ≤ 2 ^ k`, the side `P` has at least `K` elements. -/
theorem le_of_two_pow_le_mul_internal {P g d k K : ℕ} (hP : 2 ^ d ≤ P * 2 ^ g) (hd : k + g ≤ d)
    (hK : K ≤ 2 ^ k) : K ≤ P := by
  have h1 : 2 ^ (k + g) ≤ P * 2 ^ g :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hd) hP
  rw [pow_add] at h1
  exact le_trans hK (le_of_mul_le_mul_right h1 (Nat.two_pow_pos g))

/-- The closing step when the side `Q` is first projected onto `Q'` with fibers of size at most
`2 ^ m`. -/
theorem le_of_two_pow_le_mul_image_internal {Q Q' g d k K m : ℕ} (hQ : 2 ^ d ≤ Q * 2 ^ g)
    (hQ' : Q ≤ 2 ^ m * Q') (hd : k + (m + g) ≤ d) (hK : K ≤ 2 ^ k) : K ≤ Q' := by
  refine le_of_two_pow_le_mul_internal (g := m + g) ?_ hd hK
  calc 2 ^ d ≤ Q * 2 ^ g := hQ
    _ ≤ (2 ^ m * Q') * 2 ^ g := Nat.mul_le_mul_right _ hQ'
    _ = Q' * 2 ^ (m + g) := by rw [pow_add]; ring

/-- Splitting a sum of sizes by saturation: the saturated items (`c ≤ e`) contribute their size,
the unsaturated ones their excess `c - e` plus `e`. -/
theorem sum_eq_sum_filter_add_sum_tsub_add_sum_internal {ι : Type*} (𝓗 : Finset ι)
    (c e : ι → ℕ) :
    ∑ b ∈ 𝓗, c b = ∑ b ∈ 𝓗.filter (fun b => c b ≤ e b), c b + ∑ b ∈ 𝓗, (c b - e b) +
      ∑ b ∈ 𝓗.filter (fun b => ¬ c b ≤ e b), e b := by
  rw [← Finset.sum_filter_add_sum_filter_not 𝓗 (fun b => c b ≤ e b) c,
    ← Finset.sum_filter_add_sum_filter_not 𝓗 (fun b => c b ≤ e b) (fun b => c b - e b)]
  have h0 : ∑ b ∈ 𝓗.filter (fun b => c b ≤ e b), (c b - e b) = 0 :=
    Finset.sum_eq_zero fun b hb => Nat.sub_eq_zero_of_le (Finset.mem_filter.mp hb).2
  have h1 : ∑ b ∈ 𝓗.filter (fun b => ¬ c b ≤ e b), c b =
      ∑ b ∈ 𝓗.filter (fun b => ¬ c b ≤ e b), ((c b - e b) + e b) :=
    Finset.sum_congr rfl fun b hb =>
      (Nat.sub_add_cancel (le_of_lt (not_le.mp (Finset.mem_filter.mp hb).2))).symm
  rw [h0, h1, Finset.sum_add_distrib]
  omega

/-- The input `x` with the coordinates in `F` fixed to `false`. -/
def fixFalse (F : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ F then false else x i

/-- The second side `q` of a split with the coordinates in `F ⊆ Uᶜ` fixed to `false`. -/
def fixFalseRight (U F : Finset (Fin n)) (q : ↥Uᶜ → Bool) : ↥Uᶜ → Bool :=
  fun i => if (i : Fin n) ∈ F then false else q i

theorem fixFalse_glue (U F : Finset (Fin n)) (hFU : Disjoint F U) (p : U → Bool)
    (q : ↥Uᶜ → Bool) : fixFalse F (glue U p q) = glue U p (fixFalseRight U F q) := by
  funext i
  simp only [fixFalse, glue, fixFalseRight]
  by_cases hi : i ∈ U
  · have hiF : i ∉ F := Finset.disjoint_right.mp hFU hi
    simp [hi, hiF]
  · simp [hi]

/-- Fixing the coordinates of `F ⊆ Uᶜ` to `false` has fibers of size at most `2 ^ |F|`. -/
theorem card_le_card_image_fixFalseRight (U F : Finset (Fin n)) (hFU : Disjoint F U)
    (Q : Finset (↥Uᶜ → Bool)) :
    Q.card ≤ 2 ^ F.card * (Q.image (fixFalseRight U F)).card := by
  refine Finset.card_le_mul_card_image Q (2 ^ F.card) fun a _ => ?_
  have hFc : ∀ i ∈ F, i ∈ Uᶜ := fun i hi =>
    Finset.mem_compl.mpr (Finset.disjoint_left.mp hFU hi)
  have h := Finset.card_le_card_of_injOn (s := Q.filter fun q => fixFalseRight U F q = a)
    (t := (Finset.univ : Finset (F → Bool))) (fun q (i : F) => q ⟨i.1, hFc i.1 i.2⟩)
    (fun _ _ => Finset.mem_univ _) ?_
  · rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at h
  · intro q hq q' hq' heq
    have hq := (Finset.mem_filter.mp hq).2
    have hq' := (Finset.mem_filter.mp hq').2
    funext i
    by_cases hi : (i : Fin n) ∈ F
    · exact congrFun heq ⟨i.1, hi⟩
    · have := congrFun (hq.trans hq'.symm) i
      simpa [fixFalseRight, hi] using this

namespace Program

/-- The program `C` with the inputs of `F` disconnected: their weights are set to `0` in every
gate. On inputs vanishing on `F`, it evaluates as `C`. -/
noncomputable def restrictInputs (C : Program n s) (F : Finset (Fin n)) : Program n s where
  inputWeight j i := if i ∈ F then 0 else C.inputWeight j i
  gateWeight := C.gateWeight
  bias := C.bias
  output := C.output

theorem support_restrictInputs (C : Program n s) (F : Finset (Fin n)) (j : Fin s) :
    (C.restrictInputs F).support j = C.support j \ F := by
  ext i
  simp only [mem_support_internal, restrictInputs, Finset.mem_sdiff]
  by_cases hi : i ∈ F <;> simp [hi]

theorem weightedSum_restrictInputs (C : Program n s) (F : Finset (Fin n)) (j : Fin s)
    (x : Fin n → Bool) :
    weightedSum ((C.restrictInputs F).inputWeight j) x =
      weightedSum (C.inputWeight j) (fixFalse F x) := by
  unfold weightedSum
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [restrictInputs, fixFalse]
  split_ifs <;> simp

theorem evalFrom_restrictInputs (C : Program n s) (F : Finset (Fin n)) (fixed : Finset (Fin s))
    (η : Fin s → Bool) (z : Fin s → ℝ) :
    (C.restrictInputs F).evalFrom fixed η z = C.evalFrom fixed η z := by
  funext j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    rw [evalFrom_eq, evalFrom_eq]
    have hsum : (∑ k : Fin s, if k < j then
        (C.restrictInputs F).gateWeight j k * ((C.restrictInputs F).evalFrom fixed η z k).toNat
          else 0) =
        ∑ k : Fin s, if k < j then C.gateWeight j k * (C.evalFrom fixed η z k).toNat else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hk
      · rw [ih k hk]
        rfl
      · rfl
    rw [hsum]
    rfl

theorem eval_restrictInputs (C : Program n s) (F : Finset (Fin n)) (x : Fin n → Bool) :
    (C.restrictInputs F).eval x = C.eval (fixFalse F x) := by
  unfold eval
  rw [evalFrom_restrictInputs]
  congr 1
  funext j
  exact C.weightedSum_restrictInputs F j x

theorem computes_restrictInputs (C : Program n s) {f : Cslib.BooleanFunction n}
    (hC : C.Computes f) (F : Finset (Fin n)) :
    (C.restrictInputs F).Computes fun x => f (fixFalse F x) := by
  intro x
  rw [eval_restrictInputs]
  exact hC _


/-- The gates whose residual support outside `F` is nonempty and lies in `b`. -/
noncomputable def residualGates (C : Program n s) (F b : Finset (Fin n)) : Finset (Fin s) :=
  Finset.univ.filter fun j => ¬ C.support j ⊆ F ∧ C.support j \ F ⊆ b

theorem mem_residualGates (C : Program n s) (F b : Finset (Fin n)) (j : Fin s) :
    j ∈ C.residualGates F b ↔ ¬ C.support j ⊆ F ∧ C.support j \ F ⊆ b := by
  simp [residualGates]

theorem residualGates_subset_inputGates (C : Program n s) (F b : Finset (Fin n)) :
    C.residualGates F b ⊆ C.inputGates := by
  intro j hj
  rw [mem_residualGates] at hj
  rw [inputGates, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun h0 => hj.1 fun i hi => ?_⟩
  rw [mem_support_internal] at hi
  exact absurd (congrFun h0 i) hi

theorem disjoint_residualGates (C : Program n s) (F : Finset (Fin n)) {b b' : Finset (Fin n)}
    (hbb' : Disjoint b b') : Disjoint (C.residualGates F b) (C.residualGates F b') := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  rw [mem_residualGates] at hj hj'
  apply hj.1
  rw [← Finset.sdiff_eq_empty_iff_subset, Finset.eq_empty_iff_forall_notMem]
  intro i hi
  exact Finset.disjoint_left.mp hbb' (hj.2 hi) (hj'.2 hi)

/-- Over pairwise disjoint blocks, the residual gates number at most the input gates. -/
theorem sum_card_residualGates_le (C : Program n s) (F : Finset (Fin n))
    (𝓑 : Finset (Finset (Fin n))) (hdisj : (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id) :
    ∑ b ∈ 𝓑, (C.residualGates F b).card ≤ C.inputGates.card := by
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_card
      (Finset.biUnion_subset.mpr fun b _ => C.residualGates_subset_inputGates F b)
  · intro b hb b' hb' hne
    exact C.disjoint_residualGates F (hdisj hb hb' hne)

/-- The gates of the disconnected program counted on the side `W` of a split, with the set `X`
fixed, lie in the unsaturated blocks of the group `𝓗` meeting `W`. -/
theorem card_filter_le_sum_residualGates (C : Program n s) (F : Finset (Fin n))
    (𝓑 𝓗 : Finset (Finset (Fin n)))
    (hblocks : ∀ j, C.support j ⊆ F ∨ ∃ b ∈ 𝓑, C.support j \ F ⊆ b) (W X : Finset (Fin n))
    (hW : ∀ b ∈ 𝓑, ∀ i ∈ b, i ∈ W → b ∈ 𝓗)
    (hX : ∀ b ∈ 𝓗, b.card ≤ (C.residualGates F b).card → b ⊆ X) :
    (Finset.univ.filter fun j =>
        (C.restrictInputs F).support j ⊆ W ∧ ¬ (C.restrictInputs F).support j ⊆ X).card ≤
      ∑ b ∈ 𝓗.filter (fun b => ¬ b.card ≤ (C.residualGates F b).card),
        (C.residualGates F b).card := by
  refine le_trans (Finset.card_le_card (t := (𝓗.filter
    fun b => ¬ b.card ≤ (C.residualGates F b).card).biUnion (C.residualGates F)) ?_)
    Finset.card_biUnion_le
  intro j hj
  rw [Finset.mem_filter, support_restrictInputs] at hj
  obtain ⟨-, hjW, hjX⟩ := hj
  have hne : ¬ C.support j ⊆ F := fun h => hjX (by
    rw [Finset.sdiff_eq_empty_iff_subset.mpr h]
    exact Finset.empty_subset _)
  obtain ⟨b, hb, hsub⟩ := (hblocks j).resolve_left hne
  obtain ⟨i, hi⟩ :=
    Finset.nonempty_iff_ne_empty.mpr (mt Finset.sdiff_eq_empty_iff_subset.mp hne)
  have hbH : b ∈ 𝓗 := hW b hb i (hsub hi) (hjW hi)
  rw [Finset.mem_biUnion]
  refine ⟨b, Finset.mem_filter.mpr ⟨hbH, fun hsat => hjX (hsub.trans (hX b hbH hsat))⟩, ?_⟩
  exact (C.mem_residualGates F b j).mpr ⟨hne, hsub⟩

end Program

/-- **The excess bound.** Let `F` be a set of inputs and `𝓑` a family of pairwise disjoint
blocks covering the inputs outside `F`, such that every gate reads inputs from `F` only or has
its residual support outside `F` inside a single block. If every block `b` has excess
`|b| - e_b ≤ M`, where `e_b` counts the gates with nonempty residual support inside `b`, and the
program computes a two-sided `K`-rectangle-free function with `K ≤ 2 ^ k`, then
`n < |F| + s_in + M + 2k`. -/
theorem TwoSidedRectangleFree.lt_of_blocks_internal {f : Cslib.BooleanFunction n} {K : ℕ}
    (hf : TwoSidedRectangleFree f K) {C : Program n s} (hC : C.Computes f) (F : Finset (Fin n))
    (𝓑 : Finset (Finset (Fin n))) (hdisj : (𝓑 : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hcover : ∀ i, i ∉ F → ∃ b ∈ 𝓑, i ∈ b) (hF : ∀ b ∈ 𝓑, Disjoint b F)
    (hblocks : ∀ j, C.support j ⊆ F ∨ ∃ b ∈ 𝓑, C.support j \ F ⊆ b) (M : ℕ)
    (hM : ∀ b ∈ 𝓑, b.card ≤
      (Finset.univ.filter fun j => ¬ C.support j ⊆ F ∧ C.support j \ F ⊆ b).card + M)
    {k : ℕ} (hK : K ≤ 2 ^ k) :
    n < F.card + C.inputGates.card + M + 2 * k := by
  by_contra hn
  push Not at hn
  have hM' : ∀ b ∈ 𝓑, b.card ≤ (C.residualGates F b).card + M := hM
  -- The blocks cover `Fᶜ`.
  have hbU : 𝓑.biUnion id = Fᶜ := by
    ext i
    simp only [Finset.mem_biUnion, id, Finset.mem_compl]
    constructor
    · rintro ⟨b, hb, hi⟩
      exact Finset.disjoint_left.mp (hF b hb) hi
    · exact hcover i
  have hFn : F.card ≤ n := by simpa using Finset.card_le_univ F
  have hsumcard : ∑ b ∈ 𝓑, b.card = n - F.card := by
    calc ∑ b ∈ 𝓑, b.card = (𝓑.biUnion id).card := (Finset.card_biUnion hdisj).symm
      _ = n - F.card := by rw [hbU, Finset.card_compl, Fintype.card_fin]
  -- The residual gates number at most the input gates, so the total excess is large.
  have hsume := C.sum_card_residualGates_le F 𝓑 hdisj
  have hφtot : 2 * k + M ≤ ∑ b ∈ 𝓑, (b.card - (C.residualGates F b).card) := by
    have h1 : ∑ b ∈ 𝓑, b.card ≤
        ∑ b ∈ 𝓑, ((b.card - (C.residualGates F b).card) + (C.residualGates F b).card) :=
      Finset.sum_le_sum fun b _ => le_tsub_add
    rw [Finset.sum_add_distrib] at h1
    omega
  obtain ⟨𝒢, h𝒢, hk1, hk2⟩ := exists_subset_sum_ge_internal 𝓑
    (fun b => b.card - (C.residualGates F b).card) M k
    (fun b hb => by
      show b.card - (C.residualGates F b).card ≤ M
      have := hM' b hb
      omega) hφtot
  -- The split: the blocks of `𝒢` on one side, with the saturated blocks and `F` fixed.
  set U := 𝒢.biUnion id with hU
  set A := (𝒢.filter fun b => b.card ≤ (C.residualGates F b).card).biUnion id with hA
  set B := ((𝓑 \ 𝒢).filter fun b => b.card ≤ (C.residualGates F b).card).biUnion id with hB
  have hdisjU : ∀ b ∈ 𝓑, b ∉ 𝒢 → Disjoint b U := by
    intro b hb hbG
    rw [hU, Finset.disjoint_biUnion_right]
    intro b' hb'
    exact hdisj hb (h𝒢 hb') fun h => hbG (h ▸ hb')
  have hFU : Disjoint F U := by
    rw [hU, Finset.disjoint_biUnion_right]
    intro b' hb'
    exact (hF b' (h𝒢 hb')).symm
  have hAU : A ⊆ U :=
    Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _)
  have hBU : B ⊆ Uᶜ := by
    rw [hB, Finset.subset_compl_iff_disjoint_right, Finset.disjoint_biUnion_left]
    intro b hb
    have hb' := Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1
    exact hdisjU b hb'.1 hb'.2
  have hsplit : ∀ j, (C.restrictInputs F).support j ⊆ U ∨
      (C.restrictInputs F).support j ⊆ Uᶜ := by
    intro j
    rw [Program.support_restrictInputs]
    rcases hblocks j with h | ⟨b, hb, hsub⟩
    · left
      rw [Finset.sdiff_eq_empty_iff_subset.mpr h]
      exact Finset.empty_subset _
    · by_cases hbG : b ∈ 𝒢
      · exact Or.inl (hsub.trans (Finset.subset_biUnion_of_mem id hbG))
      · exact Or.inr
          (hsub.trans (Finset.subset_compl_iff_disjoint_right.mpr (hdisjU b hb hbG)))
  obtain ⟨P, Q, b₀, hb₀, hP, hQ⟩ := (C.restrictInputs F).exists_rectangle_of_split_internal
    (C.computes_restrictInputs hC F) U A B hAU hBU hsplit
  -- Fixing `F` to `false` on the second side gives a rectangle on which `f` is constant.
  have hconst : ∀ p ∈ P, ∀ q ∈ Q.image (fixFalseRight U F), f (glue U p q) = b₀ := by
    intro p hp q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
    rw [← fixFalse_glue U F hFU]
    exact hb₀ p hp q₀ hq₀
  -- The `P` side.
  have hUcard : U.card = ∑ b ∈ 𝒢, b.card :=
    Finset.card_biUnion (hdisj.subset (Finset.coe_subset.mpr h𝒢))
  have hAcard : A.card = ∑ b ∈ 𝒢.filter (fun b => b.card ≤ (C.residualGates F b).card), b.card :=
    Finset.card_biUnion (hdisj.subset
      (Finset.coe_subset.mpr ((Finset.filter_subset _ _).trans h𝒢)))
  have hgP := C.card_filter_le_sum_residualGates F 𝓑 𝒢 hblocks U A
    (fun b hb i hi hiU => by
      by_contra hbG
      exact Finset.disjoint_left.mp (hdisjU b hb hbG) hi hiU)
    (fun b hb hsat => Finset.subset_biUnion_of_mem id (Finset.mem_filter.mpr ⟨hb, hsat⟩))
  have hdecompP := sum_eq_sum_filter_add_sum_tsub_add_sum_internal 𝒢 Finset.card
    fun b => (C.residualGates F b).card
  have hPK : K ≤ P.card := by
    refine le_of_two_pow_le_mul_internal hP (le_trans (Nat.add_le_add_left hgP k) ?_) hK
    omega
  -- The `Q` side.
  have hUc : Uᶜ.card = n - U.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hsplitsum : ∑ b ∈ 𝓑 \ 𝒢, b.card + ∑ b ∈ 𝒢, b.card = ∑ b ∈ 𝓑, b.card :=
    Finset.sum_sdiff h𝒢
  have hBcard : B.card =
      ∑ b ∈ (𝓑 \ 𝒢).filter (fun b => b.card ≤ (C.residualGates F b).card), b.card :=
    Finset.card_biUnion (hdisj.subset
      (Finset.coe_subset.mpr ((Finset.filter_subset _ _).trans Finset.sdiff_subset)))
  have hgQ := C.card_filter_le_sum_residualGates F 𝓑 (𝓑 \ 𝒢) hblocks Uᶜ B
    (fun b hb i hi hiU => Finset.mem_sdiff.mpr ⟨hb, fun hbG =>
      Finset.mem_compl.mp hiU (Finset.subset_biUnion_of_mem id hbG hi)⟩)
    (fun b hb hsat => Finset.subset_biUnion_of_mem id (Finset.mem_filter.mpr ⟨hb, hsat⟩))
  have hdecompQ := sum_eq_sum_filter_add_sum_tsub_add_sum_internal (𝓑 \ 𝒢) Finset.card
    fun b => (C.residualGates F b).card
  have hfiber := card_le_card_image_fixFalseRight U F hFU Q
  have hQK : K ≤ (Q.image (fixFalseRight U F)).card := by
    refine le_of_two_pow_le_mul_image_internal hQ hfiber
      (le_trans (Nat.add_le_add_left (Nat.add_le_add_left hgQ F.card) k) ?_) hK
    omega
  rcases hf U P _ b₀ hconst with h | h <;> omega

end Algebraic.Threshold

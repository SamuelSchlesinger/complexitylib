/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DepthThree.Defs
public import Complexitylib.Circuits.KCNF.Basic
public import Complexitylib.Circuits.Frontier.Rectangle
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Complexitylib.Circuits.KCNF.SubcubeFree
import Mathlib.Tactic

/-!
# Depth-three lower bounds from subcube-free accepted sets -- proofs

Internal proofs for `Complexitylib.Circuits.DepthThree`.

Every function has a `Σ₃^1` formula (an OR of minterms), so `Σ₃^k(f)` is attained for `k ≥ 1`.
De Morgan duality identifies `Π₃^k(f)` with `Σ₃^k(¬f)`. If `f = F_1 ∨ … ∨ F_t`, every `F_i`
accepts only inputs of `f`, so none of them contains a subcube of dimension `D` when `f` does not,
and Theorem A bounds `|f⁻¹(1)| ≤ t · 2 ^ ((1 - 1/k + ε) N + C D)`. A subcube of dimension `2 m`
with `2 ^ m ≥ K` splits into a rectangle with both sides of size `2 ^ m`, so a `K`-rectangle-free
set contains no such subcube.
-/

@[expose] public section

namespace Complexity

open Finset Filter Asymptotics

namespace DepthThree

variable {N : ℕ}

/-- The CNF accepting exactly `x`: one unit clause per variable. -/
def minterm (x : BitString N) : CNF N :=
  ⟨(List.finRange N).map fun i => [⟨i, x i⟩]⟩

theorem eval_minterm_eq_true_iff (x y : BitString N) : (minterm x).eval y = true ↔ y = x := by
  rw [funext_iff]
  simp only [minterm, CNF.eval, List.all_map, List.all_eq_true, List.mem_finRange,
    Function.comp_apply, List.any_cons, List.any_nil, Bool.or_false, true_implies,
    Literal.eval_eq_true_iff]

theorem width_minterm_le (x : BitString N) : (minterm x).width ≤ 1 := by
  rw [CNF.width_le_iff]
  intro clause hclause
  simp only [minterm, List.mem_map, List.mem_finRange, true_and] at hclause
  obtain ⟨i, rfl⟩ := hclause
  simp

/-- Every function has a `Σ₃^k` formula for `k ≥ 1`: the OR of the minterms of its accepted
inputs. -/
theorem exists_isSigmaThree {k : ℕ} (hk : 1 ≤ k) (f : BitString N → Bool) :
    ∃ Fs, IsSigmaThree k f Fs := by
  refine ⟨(univ.filter fun x => f x = true).toList.map minterm,
    fun F hF => ?_, fun y => ?_⟩
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hF
    exact (width_minterm_le x).trans hk
  · rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [List.mem_map, mem_toList, mem_filter, mem_univ, true_and]
    constructor
    · intro hy
      exact ⟨minterm y, ⟨y, hy, rfl⟩, (eval_minterm_eq_true_iff y y).mpr rfl⟩
    · rintro ⟨F, ⟨x, hx, rfl⟩, hFy⟩
      rw [(eval_minterm_eq_true_iff x y).mp hFy]
      exact hx

theorem sigmaThreeSize_spec {k : ℕ} (hk : 1 ≤ k) (f : BitString N → Bool) :
    ∃ Fs, IsSigmaThree k f Fs ∧ Fs.length = sigmaThreeSize k f := by
  obtain ⟨Fs, hFs⟩ := exists_isSigmaThree hk f
  exact Nat.sInf_mem (s := {t | ∃ Fs, IsSigmaThree k f Fs ∧ Fs.length = t})
    ⟨Fs.length, Fs, hFs, rfl⟩

theorem sigmaThreeSize_le {k : ℕ} {f : BitString N → Bool} {Fs : List (CNF N)}
    (h : IsSigmaThree k f Fs) : sigmaThreeSize k f ≤ Fs.length :=
  Nat.sInf_le ⟨Fs, h, rfl⟩

/-- De Morgan duality: an AND of DNFs computes `f` exactly when the OR of their negations, which
are CNFs of the same widths, computes `¬f`. -/
theorem isPiThree_iff {k : ℕ} {f : BitString N → Bool} (Gs : List (DNF N)) :
    IsPiThree k f Gs ↔ IsSigmaThree k (fun x => !f x) (Gs.map DNF.neg) := by
  unfold IsPiThree IsSigmaThree
  refine and_congr ?_ (forall_congr' fun x => ?_)
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      DNF.width_neg]
  · rw [List.any_map]
    simp only [Function.comp_def, DNF.eval_neg, List.any_eq_not_all_not, Bool.not_not]
    cases f x <;> cases Gs.all fun G => G.eval x <;> simp

theorem piThreeSize_eq_sigmaThreeSize_not (k : ℕ) (f : BitString N → Bool) :
    piThreeSize k f = sigmaThreeSize k (fun x => !f x) := by
  unfold piThreeSize sigmaThreeSize
  congr 1
  ext t
  constructor
  · rintro ⟨Gs, hGs, rfl⟩
    exact ⟨Gs.map DNF.neg, (isPiThree_iff Gs).mp hGs, List.length_map _⟩
  · rintro ⟨Fs, hFs, rfl⟩
    refine ⟨Fs.map CNF.neg, (isPiThree_iff _).mpr ?_, List.length_map _⟩
    rwa [List.map_map, show DNF.neg ∘ CNF.neg = id from funext CNF.neg_neg, List.map_id]

/-- **The finite bound.** For `k ≥ 1` and `ε > 0` there is `C ≥ 0` such that every OR of `t`
CNFs of width at most `k` computing a function whose accepted inputs contain no subcube of
dimension `D` has `|f⁻¹(1)| ≤ t · 2 ^ ((1 - 1/k + ε) N + C D)`. -/
theorem card_accepting_le (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (f : BitString N → Bool) (D : ℕ) (Fs : List (CNF N)),
      IsSigmaThree k f Fs → ¬ ContainsSubcube {x | f x = true} D →
      ((univ.filter fun x => f x = true).card : ℝ) ≤
        Fs.length * 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨C, hC, hA⟩ := CNF.card_accepting_le_of_not_containsSubcube k hk hε
  refine ⟨C, hC, fun N f D Fs hFs hfree => ?_⟩
  set E := (1 - 1 / (k : ℝ) + ε) * N + C * D
  have hsub : (univ.filter fun x => f x = true) ⊆
      Fs.toFinset.biUnion fun F => univ.filter fun x => F.eval x = true := by
    intro x hx
    have hfx := (mem_filter.mp hx).2
    rw [hFs.2 x, List.any_eq_true] at hfx
    obtain ⟨F, hF, hFx⟩ := hfx
    exact mem_biUnion.mpr ⟨F, List.mem_toFinset.mpr hF, mem_filter.mpr ⟨mem_univ _, hFx⟩⟩
  have hpiece : ∀ F ∈ Fs.toFinset,
      ((univ.filter fun x => F.eval x = true).card : ℝ) ≤ 2 ^ E := by
    intro F hF
    have hF' := List.mem_toFinset.mp hF
    refine hA N F D (hFs.1 F hF') fun h => hfree (h.mono fun x hx => ?_)
    have hx' : F.eval x = true := hx
    show f x = true
    rw [hFs.2 x, List.any_eq_true]
    exact ⟨F, hF', hx'⟩
  calc ((univ.filter fun x => f x = true).card : ℝ)
      ≤ ((Fs.toFinset.biUnion fun F => univ.filter fun x => F.eval x = true).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ F ∈ Fs.toFinset, ((univ.filter fun x => F.eval x = true).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _F ∈ Fs.toFinset, (2 : ℝ) ^ E := sum_le_sum hpiece
    _ = (Fs.toFinset.card : ℝ) * 2 ^ E := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Fs.length * 2 ^ E := by
        gcongr
        exact_mod_cast List.toFinset_card_le Fs

theorem ncard_setOf_eq_card_filter (f : BitString N → Bool) :
    {x | f x = true}.ncard = (univ.filter fun x => f x = true).card := by
  rw [← Set.ncard_coe_finset, coe_filter]
  simp

/-- **The asymptotic bound.** Let `f` be a family of Boolean functions whose accepted sets
eventually contain no subcube of dimension `D n = o(n)` and have logarithmic density deficit
`o(n)`. Then for every `k ≥ 1` and `ε > 0`, eventually `Σ₃^k(f n) ≥ 2 ^ ((1/k - ε) n)`. -/
theorem eventually_le_sigmaThreeSize {f : (n : ℕ) → BitString n → Bool} {D : ℕ → ℕ}
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hfree : ∀ᶠ n in atTop, ¬ ContainsSubcube {x | f n x = true} (D n))
    (hdense : (fun n : ℕ => (n : ℝ) * Real.log 2 - Real.log {x | f n x = true}.ncard)
      =o[atTop] (fun n => (n : ℝ)))
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤ sigmaThreeSize k (f n) := by
  obtain ⟨C, hC, hA⟩ := card_accepting_le k hk (ε := ε / 3) (by positivity)
  set δ := min (ε / 3) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : ∀ᶠ n : ℕ in atTop, C * D n ≤ ε / 3 * n := by
    have hc : 0 < ε / (3 * (C + 1)) := by positivity
    filter_upwards [hD.bound hc] with n hn
    simp only [Real.norm_natCast] at hn
    calc C * D n ≤ C * (ε / (3 * (C + 1)) * n) := mul_le_mul_of_nonneg_left hn hC
      _ ≤ ε / 3 * n := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n)
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have h2 : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log 2 - Real.log {x | f n x = true}.ncard ≤ δ * Real.log 2 * n := by
    filter_upwards [hdense.bound (mul_pos hδ0 hlog2)] with n hn
    simp only [Real.norm_natCast] at hn
    exact (le_abs_self _).trans hn
  filter_upwards [h1, h2, hfree, eventually_ge_atTop 1] with n h1 h2 hfree hn
  rw [ncard_setOf_eq_card_filter] at h2
  set s := (univ.filter fun x => f n x = true).card
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the accepted set is dense
  have hlogs : (1 - δ) * n * Real.log 2 ≤ Real.log s := by nlinarith
  have hspos : (0 : ℝ) < s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero] at hlogs
      have : δ ≤ 1 / 2 := min_le_right _ _
      have : 0 < (1 - δ) * n * Real.log 2 :=
        mul_pos (mul_pos (by linarith) (by linarith)) hlog2
      linarith
    · exact_mod_cast hpos
  have hsbig : (2 : ℝ) ^ ((1 - δ) * n) ≤ s := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log hspos]
    exact Real.exp_le_exp.mpr (by linarith)
  -- a minimal formula
  obtain ⟨Fs, hFs, hlen⟩ := sigmaThreeSize_spec hk (f n)
  have hbound := hA n (f n) (D n) Fs hFs hfree
  rw [hlen] at hbound
  set E := (1 - 1 / (k : ℝ) + ε / 3) * n + C * D n
  have hlow : (2 : ℝ) ^ ((1 - δ) * n - E) ≤ sigmaThreeSize k (f n) := by
    rw [Real.rpow_sub (by norm_num), div_le_iff₀ (by positivity)]
    exact hsbig.trans hbound
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hlow
  have : δ ≤ ε / 3 := min_le_left _ _
  simp only [E]
  nlinarith

/-- **Rectangle-free sets contain no large subcubes.** If `K ≤ 2 ^ m`, a `K`-rectangle-free set
of inputs contains no subcube of dimension `2 m`: such a subcube splits into a rectangle with both
sides of size `2 ^ m`. -/
theorem not_containsSubcube_of_rectangleFree {S : Set (BitString N)} {K m : ℕ}
    (hS : Frontier.RectangleFree S K) (hK : K ≤ 2 ^ m) : ¬ ContainsSubcube S (2 * m) := by
  rintro ⟨a, J, hJ, hsub⟩
  obtain ⟨J₁, hJ₁J, hJ₁⟩ := exists_subset_card_eq (s := J) (n := m) (by omega)
  set J₂ := J \ J₁
  have hJ₂ : J₂.card = m := by rw [card_sdiff_of_subset hJ₁J]; omega
  set X : Set (Fin N) := (J₁ : Set (Fin N))
  let A : Set (X → Bool) :=
    (fun T : Finset (Fin N) => X.domRestrict (a.flipOn T)) '' (J₁.powerset : Set (Finset (Fin N)))
  let B : Set (↥Xᶜ → Bool) :=
    (fun T : Finset (Fin N) => Xᶜ.domRestrict (a.flipOn T)) '' (J₂.powerset : Set (Finset (Fin N)))
  have hrect : Frontier.rectangle X A B ⊆ S := by
    rintro x ⟨⟨T₁, hT₁, hx₁⟩, ⟨T₂, hT₂, hx₂⟩⟩
    have hT₁J : T₁ ⊆ J₁ := mem_powerset.mp hT₁
    have hT₂J : T₂ ⊆ J₂ := mem_powerset.mp hT₂
    have hx : x = a.flipOn (T₁ ∪ T₂) := by
      funext i
      by_cases hi : i ∈ J₁
      · have := congrFun hx₁ ⟨i, hi⟩
        simp only [Set.domRestrict_apply] at this
        rw [← this]
        refine BitString.flipOn_apply_eq_of_iff ⟨fun h => mem_union_left _ h, fun h => ?_⟩
        rcases mem_union.mp h with h | h
        · exact h
        · exact absurd hi (mem_sdiff.mp (hT₂J h)).2
      · have := congrFun hx₂ ⟨i, hi⟩
        simp only [Set.domRestrict_apply] at this
        rw [← this]
        refine BitString.flipOn_apply_eq_of_iff ⟨fun h => mem_union_right _ h, fun h => ?_⟩
        rcases mem_union.mp h with h | h
        · exact absurd (hT₁J h) hi
        · exact h
    rw [hx]
    exact hsub _ (union_subset (hT₁J.trans hJ₁J) (hT₂J.trans sdiff_subset))
  have hinj : ∀ (Y : Set (Fin N)) (L : Finset (Fin N)), (↑L : Set (Fin N)) ⊆ Y →
      Set.InjOn (fun T : Finset (Fin N) => Y.domRestrict (a.flipOn T))
        (L.powerset : Set (Finset (Fin N))) := by
    intro Y L hLY T hT T' hT' h
    have hT : T ⊆ L := mem_powerset.mp hT
    have hT' : T' ⊆ L := mem_powerset.mp hT'
    ext i
    by_cases hiL : i ∈ L
    · have := congrFun h ⟨i, hLY hiL⟩
      simp only [Set.domRestrict_apply, BitString.flipOn_apply] at this
      by_cases hi : i ∈ T <;> by_cases hi' : i ∈ T' <;> simp_all
    · exact ⟨fun h => absurd (hT h) hiL, fun h => absurd (hT' h) hiL⟩
  have hA : A.ncard = 2 ^ m := by
    rw [(hinj X J₁ subset_rfl).ncard_image, Set.ncard_coe_finset, card_powerset,
      hJ₁]
  have hB : B.ncard = 2 ^ m := by
    have hsubX : (↑J₂ : Set (Fin N)) ⊆ Xᶜ := fun i hi => (mem_sdiff.mp hi).2
    rw [(hinj Xᶜ J₂ hsubX).ncard_image, Set.ncard_coe_finset, card_powerset, hJ₂]
  rcases hS X A B hrect with h | h <;> omega

/-- `⌈log₂ K⌉ ≤ log₂ K + 1`. -/
theorem clog_le_logb_add_one (K : ℕ) : (Nat.clog 2 K : ℝ) ≤ Real.logb 2 K + 1 := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · rw [Nat.clog_of_right_le_one (by omega)]
    have : 0 ≤ Real.logb 2 K := by
      rcases Nat.lt_or_ge K 1 with h0 | h1
      · simp [show K = 0 by omega]
      · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h1)
    push_cast
    linarith
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := K) (by omega)
    have hpos : 0 < Nat.clog 2 K := Nat.clog_pos (by norm_num) (by omega)
    have hlt' : ((2 : ℝ) ^ ((Nat.clog 2 K - 1 : ℕ) : ℝ)) < K := by
      rw [Real.rpow_natCast]
      exact_mod_cast hlt
    have := (Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)).mpr hlt'
    have hcast : ((Nat.clog 2 K - 1 : ℕ) : ℝ) = (Nat.clog 2 K : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    linarith

/-- If `log K = o(n)`, then `2 ⌈log₂ K⌉ = o(n)`. -/
theorem isLittleO_two_mul_clog {K : ℕ → ℕ}
    (hK : (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ))) :
    (fun n => ((2 * Nat.clog 2 (K n) : ℕ) : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine IsLittleO.of_bound fun c hc => ?_
  filter_upwards [hK.bound (show 0 < c * Real.log 2 / 4 by positivity),
    eventually_ge_atTop ⌈4 / c⌉₊] with n hn hn4
  simp only [Real.norm_eq_abs, Nat.abs_cast] at hn ⊢
  have hn4' : 4 / c ≤ n := (Nat.ceil_le).mp hn4
  have hclog := clog_le_logb_add_one (K n)
  have hlogb : Real.logb 2 (K n) ≤ c * n / 4 := by
    rw [Real.logb, div_le_iff₀ hlog2]
    have := (le_abs_self _).trans hn
    nlinarith
  have hcn : 4 ≤ c * n := by
    rwa [div_le_iff₀ hc, mul_comm] at hn4'
  push_cast
  linarith

end DepthThree

end Complexity

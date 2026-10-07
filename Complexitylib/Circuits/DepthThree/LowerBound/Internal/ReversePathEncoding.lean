/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionExpansion
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.ReversePathRecurrence
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.ReversePathWeights
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Tauto

/-!
# Unrestricted depth-three lower bound: reverse path encoding

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/ReversePathEncoding.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open Finset
open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [DecidableEq V] [instDecidableEqI : DecidableEq I]
  [instFintypeI : Fintype I]

/-- Live coordinates remaining after the path's revealed set is removed. -/
def pathRemainder (scope : I → Finset V) (T : Finset V) (P : List I) : Finset V :=
  T \ revealed scope T P

omit [Fintype I] in
@[simp] theorem pathRemainder_nil
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]

    (scope : I → Finset V) (T : Finset V) :
    pathRemainder scope T [] = T := by simp [pathRemainder]
omit [DecidableEq I] in
theorem coveredCount_eq_reverseEligible
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]

    [instFintypeI : Fintype I]
    (scope : I → Finset V) (T U : Finset V)
    (violation : I → Bool) :
    coveredCount scope T violation U = (reverseEligible scope violation (T \ U)).card := by
  classical
  unfold coveredCount reverseEligible
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, residual,
    Finset.disjoint_iff_inter_eq_empty]
  simp only [Finset.mem_filter_univ, and_comm]
/-- The path weight including its covered-coordinate contribution. -/
def coveredPathWeight (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (P : List I) : ℝ :=
  ∏ h : Fin P.length,
    (coveredCount scope T violation (revealed scope T (P.take (h.val + 1))) : ℝ)⁻¹

@[simp] theorem coveredPathWeight_nil (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) : coveredPathWeight scope T violation [] = 1 := by
  simp [coveredPathWeight]

theorem coveredPathWeight_nonneg (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (P : List I) : 0 ≤ coveredPathWeight scope T violation P :=
  prod_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem coveredPathWeight_snoc (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (P : List I) (i : I) :
    coveredPathWeight scope T violation (P ++ [i]) =
      coveredPathWeight scope T violation P *
        (coveredCount scope T violation (revealed scope T (P ++ [i])) : ℝ)⁻¹ := by
  unfold coveredPathWeight
  rw [Fin.prod_univ_eq_prod_range
      (fun h : ℕ => (coveredCount scope T violation
        (revealed scope T ((P ++ [i]).take (h + 1))) : ℝ)⁻¹) (P ++ [i]).length,
    Fin.prod_univ_eq_prod_range
      (fun h : ℕ => (coveredCount scope T violation
        (revealed scope T (P.take (h + 1))) : ℝ)⁻¹) P.length]
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · apply prod_congr rfl
    intro h hh
    rw [List.take_append_of_le_length (Nat.succ_le_of_lt (Finset.mem_range.mp hh))]
  · rw [List.take_of_length_le (by simp)]

omit [Fintype I] in
theorem remainder_snoc_union_block
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]

    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    pathRemainder scope T (P ++ [i]) ∪ residual scope T (revealed scope T P) i =
      pathRemainder scope T P := by
  ext v
  simp only [pathRemainder, revealed_snoc, residual,
    mem_union, mem_sdiff, mem_inter]
  tauto
omit [Fintype I] in
theorem remainder_snoc_disjoint_block
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]

    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    Disjoint (pathRemainder scope T (P ++ [i]))
      (residual scope T (revealed scope T P) i) := by
  apply disjoint_left.mpr
  intro v hR hD
  simp only [pathRemainder, revealed_snoc, mem_sdiff, mem_union, mem_inter] at hR
  simp only [residual, mem_inter, mem_sdiff] at hD
  exact hR.2 (Or.inr ⟨hD.1, hD.2.1⟩)
omit [Fintype I] in
theorem scope_disjoint_remainder_snoc
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]

    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) : Disjoint (scope i) (pathRemainder scope T (P ++ [i])) := by
  apply disjoint_left.mpr
  intro v hi hR
  simp only [pathRemainder, revealed_snoc, mem_sdiff, mem_union, mem_inter] at hR
  exact hR.2 (Or.inr ⟨hi, hR.1⟩)
/-- Encode a forward path for the reverse reconstruction argument. -/
def reverseEncode (scope : I → Finset V) (T : Finset V) (P : List I) :
    List (I × Finset V) :=
  P.reverseRecOn [] fun Q i rec =>
    (i, residual scope T (revealed scope T Q) i) :: rec

omit [Fintype I] in
@[simp] theorem reverseEncode_nil
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]

    (scope : I → Finset V) (T : Finset V) :
    reverseEncode scope T [] = [] := by simp [reverseEncode]
omit [Fintype I] in
@[simp] theorem reverseEncode_snoc
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]

    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    reverseEncode scope T (P ++ [i]) =
      (i, residual scope T (revealed scope T P) i) :: reverseEncode scope T P := by
  simp [reverseEncode]
/-- The starting data used to reconstruct an encoded path in reverse. -/
def reverseStart (R : Finset V) (L : List (I × Finset V)) : Finset V :=
  L.foldl (fun S q => S ∪ q.2) R

omit [DecidableEq I] [Fintype I] in
@[simp] theorem reverseStart_nil
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]


    (R : Finset V) : reverseStart R ([] : List (I × Finset V)) = R := rfl
omit [DecidableEq I] [Fintype I] in
@[simp] theorem reverseStart_cons
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]


    (R : Finset V) (i : I) (D : Finset V)
    (L : List (I × Finset V)) :
    reverseStart R ((i,D) :: L) = reverseStart (R ∪ D) L := rfl
omit instFintypeI in
theorem reverseStart_encode (scope : I → Finset V) (T : Finset V) (P : List I) :
    reverseStart (pathRemainder scope T P) (reverseEncode scope T P) = T := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P i ih =>
    rw [reverseEncode_snoc, reverseStart_cons, remainder_snoc_union_block]
    exact ih

omit instFintypeI in
theorem reverseEncode_indices (scope : I → Finset V) (T : Finset V) (P : List I) :
    (reverseEncode scope T P).map Prod.fst = P.reverse := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P i ih => simp [ih]

/-- Encode a restriction and path as reverse reconstruction data. -/
def encodePathPair (scope : I → Finset V) (x : Σ _T : Finset V, List I) :
    Σ _R : Finset V, List (I × Finset V) :=
  ⟨pathRemainder scope x.1 x.2, reverseEncode scope x.1 x.2⟩

omit instFintypeI in
theorem encodePathPair_injective (scope : I → Finset V) :
    Function.Injective (encodePathPair scope) := by
  rintro ⟨T,P⟩ ⟨S,Q⟩ h
  have hT := congrArg (fun x : Σ _R : Finset V, List (I × Finset V) =>
    reverseStart x.1 x.2) h
  have hP := congrArg (fun x : Σ _R : Finset V, List (I × Finset V) =>
    (x.2.map Prod.fst).reverse) h
  simp only [encodePathPair, reverseStart_encode] at hT
  simp only [encodePathPair, reverseEncode_indices, List.reverse_reverse] at hP
  subst S
  subst Q
  rfl

/-- The finite family of admissible reverse reconstruction traces. -/
def reverseTraces (scope : I → Finset V) (violation : I → Bool) (b : ℕ) :
    ℕ → Finset V → Finset (List (I × Finset V))
  | 0, _ => {[]}
  | s + 1, R => (reverseEligible scope violation R).biUnion fun i =>
      (reverseBlocks b (scope i)).biUnion fun D =>
        (reverseTraces scope violation b s (R ∪ D)).image fun L => (i,D) :: L

@[simp] theorem mem_reverseTraces_zero (scope : I → Finset V) (violation : I → Bool)
    (b : ℕ) (R : Finset V) (L : List (I × Finset V)) :
    L ∈ reverseTraces scope violation b 0 R ↔ L = [] := by
  simp [reverseTraces]

theorem mem_reverseTraces_succ (scope : I → Finset V) (violation : I → Bool)
    (b s : ℕ) (R : Finset V) (L : List (I × Finset V)) :
    L ∈ reverseTraces scope violation b (s+1) R ↔
      ∃ i ∈ reverseEligible scope violation R,
        ∃ D ∈ reverseBlocks b (scope i),
          ∃ M ∈ reverseTraces scope violation b s (R ∪ D), (i,D)::M = L := by
  simp only [reverseTraces, mem_biUnion, mem_image]

theorem reverseEncode_mem (scope : I → Finset V) (violation : I → Bool)
    (b : ℕ) (T : Finset V) {j : ℕ} {P : List I}
    (hP : P ∈ paths scope T b j) (hs : ∀ i ∈ P, violation i = true) :
    reverseEncode scope T P ∈ reverseTraces scope violation b j (pathRemainder scope T P) := by
  induction j generalizing P with
  | zero =>
    have h := (mem_paths_zero scope T b P).mp hP
    subst P
    simp
  | succ j ih =>
    obtain ⟨Q,hQ,i,hi,rfl⟩ := mem_paths_succ.mp hP
    have hsQ : ∀ a ∈ Q, violation a = true := fun a ha => hs a (List.mem_append_left _ ha)
    have hsi : violation i = true := hs i (by simp)
    rw [reverseEncode_snoc]
    apply (mem_reverseTraces_succ scope violation b j _ _).mpr
    refine ⟨i, ?_, residual scope T (revealed scope T Q) i, ?_, reverseEncode scope T Q, ?_, rfl⟩
    · exact (mem_reverseEligible scope violation _ i).mpr
        ⟨hsi, scope_disjoint_remainder_snoc scope T Q i⟩
    · exact (mem_reverseBlocks b _ _).mpr
        ⟨Finset.inter_subset_left, (mem_hardIndices scope T b _ i).mp hi⟩
    · rw [remainder_snoc_union_block]
      exact ih hQ hsQ

/-- The product weight of a reverse reconstruction trace. -/
def reverseTraceWeight (α : ℝ) (scope : I → Finset V) (violation : I → Bool) :
    Finset V → List (I × Finset V) → ℝ
  | _, [] => 1
  | R, (_,D)::L => reverseChoiceWeight α scope violation R D *
      reverseTraceWeight α scope violation (R ∪ D) L

omit instDecidableEqI in
theorem reverseTraceWeight_nonneg {α : ℝ} (hα : 0 ≤ α)
    (scope : I → Finset V) (violation : I → Bool) (R : Finset V)
    (L : List (I × Finset V)) : 0 ≤ reverseTraceWeight α scope violation R L := by
  induction L generalizing R with
  | nil => simp [reverseTraceWeight]
  | cons q L ih =>
    rcases q with ⟨i,D⟩
    exact mul_nonneg (reverseChoiceWeight_nonneg hα scope violation R D) (ih (R ∪ D))

theorem sum_reverseTraces_succ (scope : I → Finset V) (violation : I → Bool)
    (b s : ℕ) (R : Finset V) (f : List (I × Finset V) → ℝ) :
    (∑ L ∈ reverseTraces scope violation b (s+1) R, f L) =
      ∑ i ∈ reverseEligible scope violation R, ∑ D ∈ reverseBlocks b (scope i),
        ∑ L ∈ reverseTraces scope violation b s (R ∪ D), f ((i,D)::L) := by
  have hi : Set.PairwiseDisjoint (↑(reverseEligible scope violation R) : Set I)
      (fun i => (reverseBlocks b (scope i)).biUnion fun D =>
        (reverseTraces scope violation b s (R ∪ D)).image fun L => (i,D)::L) := by
    intro i hi k hk hik
    apply disjoint_left.mpr
    intro L hL hM
    obtain ⟨D,hD,hL⟩ := mem_biUnion.mp hL
    obtain ⟨E,hE,hM⟩ := mem_biUnion.mp hM
    obtain ⟨L',hL',heq⟩ := mem_image.mp hL
    obtain ⟨M',hM',heq'⟩ := mem_image.mp hM
    have hh := List.cons.inj (heq.trans heq'.symm)
    exact hik (congrArg Prod.fst hh.1)
  rw [reverseTraces, sum_biUnion hi]
  apply sum_congr rfl
  intro i hi
  have hD : Set.PairwiseDisjoint (↑(reverseBlocks b (scope i)) : Set (Finset V))
      (fun D => (reverseTraces scope violation b s (R ∪ D)).image fun L => (i,D)::L) := by
    intro D hD E hE hDE
    apply disjoint_left.mpr
    intro L hL hM
    obtain ⟨L',hL',heq⟩ := mem_image.mp hL
    obtain ⟨M',hM',heq'⟩ := mem_image.mp hM
    have hh := List.cons.inj (heq.trans heq'.symm)
    exact hDE (congrArg Prod.snd hh.1)
  rw [sum_biUnion hD]
  apply sum_congr rfl
  intro D hD
  exact sum_image fun L hL M hM h => (List.cons.inj h).2

theorem sum_reverseTraceWeight (α : ℝ) (scope : I → Finset V)
    (violation : I → Bool) (b j : ℕ) (R : Finset V) :
    (∑ L ∈ reverseTraces scope violation b j R, reverseTraceWeight α scope violation R L) =
      reverseTotal α b scope violation j R := by
  induction j generalizing R with
  | zero => simp [reverseTraces, reverseTraceWeight]
  | succ j ih =>
    rw [sum_reverseTraces_succ]
    simp_rw [reverseTraceWeight, ← Finset.mul_sum, ih]
    by_cases h : (reverseEligible scope violation R).Nonempty
    · rw [reverseTotal_succ_of_nonempty α b scope violation j R h,
        Finset.sum_div]
      apply sum_congr rfl
      intro i hi
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro D hD
      unfold reverseChoiceWeight
      ring
    · have he := Finset.not_nonempty_iff_eq_empty.mp h
      rw [reverseTotal_succ_of_empty α b scope violation j R he, he]
      simp

variable [Fintype V]

theorem reverseEncode_weight (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (scope : I → Finset V) (violation : I → Bool) (T : Finset V) (P : List I) :
    bernoulliWeight p T * (2 : ℝ) ^ (revealed scope T P).card *
        coveredPathWeight scope T violation P =
      bernoulliWeight p (pathRemainder scope T P) *
        reverseTraceWeight (2*p/(1-p)) scope violation
          (pathRemainder scope T P) (reverseEncode scope T P) := by
  induction P using List.reverseRecOn with
  | nil => simp [reverseTraceWeight]
  | append_singleton P i ih =>
    let D := residual scope T (revealed scope T P) i
    let R := pathRemainder scope T (P ++ [i])
    have hR : R ∪ D = pathRemainder scope T P := remainder_snoc_union_block scope T P i
    have hdis : Disjoint R D := remainder_snoc_disjoint_block scope T P i
    have hbal := bernoulliWeight_disjoint_union hp0 hp1 R D hdis
    rw [hR] at hbal
    rw [coveredPathWeight_snoc, card_revealed_snoc, pow_add,
      coveredCount_eq_reverseEligible, reverseEncode_snoc]
    change bernoulliWeight p T *
        ((2 : ℝ) ^ (revealed scope T P).card * (2 : ℝ) ^ D.card) *
        (coveredPathWeight scope T violation P *
          ((reverseEligible scope violation R).card : ℝ)⁻¹) =
      bernoulliWeight p R *
        (reverseChoiceWeight (2*p/(1-p)) scope violation R D *
          reverseTraceWeight (2*p/(1-p)) scope violation (R ∪ D) (reverseEncode scope T P))
    rw [hR]
    calc
      _ = (bernoulliWeight p T * (2 : ℝ) ^ (revealed scope T P).card *
          coveredPathWeight scope T violation P) * (2 : ℝ)^D.card *
          ((reverseEligible scope violation R).card : ℝ)⁻¹ := by ring
      _ = (bernoulliWeight p (pathRemainder scope T P) * (2 : ℝ)^D.card) *
          reverseTraceWeight (2*p/(1-p)) scope violation (pathRemainder scope T P)
            (reverseEncode scope T P) * ((reverseEligible scope violation R).card : ℝ)⁻¹ := by
            rw [ih]
            ring
      _ = _ := by rw [hbal]; unfold reverseChoiceWeight; ring

/-- Forward restriction-path pairs having nonzero supported contribution. -/
def supportedForwardPairs (scope : I → Finset V) (violation : I → Bool) (b j : ℕ) :
    Finset (Σ _T : Finset V, List I) :=
  univ.sigma fun T => (paths scope T b j).filter fun P => ∀ i ∈ P, violation i = true

/-- Reverse traces indexed by their starting data. -/
def indexedReverseTraces (scope : I → Finset V) (violation : I → Bool) (b j : ℕ) :
    Finset (Σ _R : Finset V, List (I × Finset V)) :=
  univ.sigma fun R => reverseTraces scope violation b j R

theorem encode_supported_mem (scope : I → Finset V) (violation : I → Bool) (b j : ℕ)
    {x : Σ _T : Finset V, List I} (hx : x ∈ supportedForwardPairs scope violation b j) :
    encodePathPair scope x ∈ indexedReverseTraces scope violation b j := by
  rcases x with ⟨T,P⟩
  have hh := mem_filter.mp (mem_sigma.mp hx).2
  exact mem_sigma.mpr ⟨mem_univ _, reverseEncode_mem scope violation b T hh.1 hh.2⟩

theorem weighted_supported_paths_le (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (b k : ℕ) (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (j : ℕ) :
    (∑ T : Finset V, bernoulliWeight p T *
      ∑ P ∈ paths scope T b j, if ∀ i ∈ P, violation i = true then
        (2 : ℝ) ^ (revealed scope T P).card * coveredPathWeight scope T violation P else 0) ≤
      (reverseTheta (2*p/(1-p)) b k) ^ j := by
  let α : ℝ := 2*p/(1-p)
  have hα : 0 ≤ α := div_nonneg (mul_nonneg (by norm_num) hp0.le) (sub_pos.mpr hp1).le
  let w : (Σ _R : Finset V, List (I × Finset V)) → ℝ := fun x =>
    bernoulliWeight p x.1 * reverseTraceWeight α scope violation x.1 x.2
  have hw : ∀ x, 0 ≤ w x := fun x => mul_nonneg
    (bernoulliWeight_nonneg hp0.le hp1.le x.1) (reverseTraceWeight_nonneg hα scope violation x.1
      x.2)
  have hs : (supportedForwardPairs scope violation b j).image (encodePathPair scope) ⊆
      indexedReverseTraces scope violation b j := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact encode_supported_mem scope violation b j hy
  calc
    _ = ∑ x ∈ supportedForwardPairs scope violation b j, w (encodePathPair scope x) := by
      rw [supportedForwardPairs, Finset.sum_sigma]
      apply sum_congr rfl
      intro T hT
      rw [← Finset.sum_filter, Finset.mul_sum]
      apply sum_congr rfl
      intro P hP
      exact (mul_assoc _ _ _).symm.trans (reverseEncode_weight p hp0 hp1 scope violation T P)
    _ = ∑ x ∈ (supportedForwardPairs scope violation b j).image (encodePathPair scope), w x := by
      symm
      exact sum_image fun x hx y hy h => encodePathPair_injective scope h
    _ ≤ ∑ x ∈ indexedReverseTraces scope violation b j, w x :=
      sum_le_sum_of_subset_of_nonneg hs (fun x hx hn => hw x)
    _ = ∑ R : Finset V, bernoulliWeight p R * reverseTotal α b scope violation j R := by
      rw [indexedReverseTraces, Finset.sum_sigma]
      apply sum_congr rfl
      intro R hR
      change (∑ L ∈ reverseTraces scope violation b j R,
        bernoulliWeight p R * reverseTraceWeight α scope violation R L) = _
      rw [← Finset.mul_sum, sum_reverseTraceWeight]
    _ ≤ ∑ R : Finset V, bernoulliWeight p R * (reverseTheta α b k)^j := by
      apply sum_le_sum
      intro R hR
      exact mul_le_mul_of_nonneg_left
        (reverseTotal_le_theta_pow hα b k scope hscope violation j R)
        (bernoulliWeight_nonneg hp0.le hp1.le R)
    _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

end DepthThreeLowerBound

end

end Complexity

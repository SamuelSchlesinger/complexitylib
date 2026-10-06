/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts
public import Complexitylib.Circuits.Frontier.AverageCase.Extractor
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
import Mathlib.Tactic.Linarith

/-!
# Bridges to the cutwidth development

This module is maintained in the library; `scripts/sync_frontier.py` mirrors the rest of
`Complexitylib/Circuits/Frontier/` from the frontier-method development and leaves it alone.
It connects the frontier method to the Boolean cutwidth development of
`Algebraic.LowerBound.Cutwidth`:

* `LayoutBound.of_orderingBound`: the ordering hypothesis
  `Algebraic.Cutwidth.Multigraph.OrderingBound A η C` at every slack gives `LayoutBound 3 A`.
  Numbering the vertices in the given order gives a layout, `(|E| - |V|)⁺` is at most the
  cycle rank, and `3 log₂ |V| ≤ η |V| + K`. Every ordering coefficient proved for the cutwidth
  development therefore transfers; `layoutBound_of_orderingBound_frontier` recovers
  `layoutBound_gaussian` this way.
* `gaussianCoefficient_eq_frontierCoefficient`: the two developments' Gaussian coefficients
  are the same number.
* `rectangleFree_setOf`: Boolean rectangle-freeness of a function is rectangle-freeness of
  its accepted set.
* `flatSumsetBias_of_flatSumsetExtractor`: a flat-source sumset extractor with error `ν`
  has signed sumset bias `2 ν`.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Filter Asymptotics

/-- `3 log₂ N` is at most `η N` plus a constant. -/
private theorem exists_three_logb_le {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ N : ℕ, 3 * Real.logb 2 N ≤ η * N + K := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (Algebraic.Cutwidth.eventually_mul_logb_add_lt 3 0 hη)
  refine ⟨3 * Real.logb 2 (max N₀ 1 : ℕ), fun N => ?_⟩
  have hK : 0 ≤ Real.logb 2 (max N₀ 1 : ℕ) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast le_max_right N₀ 1)
  rcases le_or_gt N₀ N with hN | hN
  · have := hN₀ N hN
    nlinarith
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp only [CharP.cast_eq_zero, Real.logb_zero, mul_zero, zero_add]
    positivity
  have : Real.logb 2 N ≤ Real.logb 2 (max N₀ 1 : ℕ) :=
    Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hpos)
      (by exact_mod_cast hN.le.trans (le_max_left N₀ 1))
  have : 0 ≤ η * N := by positivity
  nlinarith

/-- **From vertex orderings to layouts.** The ordering hypothesis of the cutwidth development
at every positive slack gives the layout hypothesis for maximum degree three, with the same
coefficient. -/
theorem LayoutBound.of_orderingBound {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Algebraic.Cutwidth.Multigraph.OrderingBound A η C) :
    LayoutBound 3 A := by
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  obtain ⟨K, hK⟩ := exists_three_logb_le hη
  refine ⟨C + K, fun V E _ _ G hconn hloop hdeg => ?_⟩
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let G' : Algebraic.Cutwidth.Multigraph V E := ⟨G.src, G.tgt⟩
  have hedges (v : V) : ((G'.edgesAt v : Finset E) : Set E) = G.edgesAt v := by
    ext e
    simp [Algebraic.Cutwidth.Multigraph.mem_edgesAt, Algebraic.Cutwidth.Multigraph.Incident,
      Multigraph.edgesAt, Multigraph.Incident, G']
  have hdeg' : G'.MaxDegreeLE 3 := fun v => by
    rw [Algebraic.Cutwidth.Multigraph.degree, ← Set.ncard_coe_finset, hedges]
    exact hdeg v
  obtain ⟨hlin, hord⟩ := hC V E G' hloop hdeg' hconn
  obtain ⟨π, hπ⟩ := Layout.exists_monotone (α := V) (f := id) Function.injective_id
  refine ⟨π, fun t => ?_⟩
  let L : Finset V := Finset.univ.filter fun v => (π v : ℕ) < t
  have hL : IsLowerSet (L : Set V) := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, L] at ha ⊢
    exact lt_of_le_of_lt (Fin.le_iff_val_le_val.mp (hπ b a hba)) ha
  have hcut : (G.cut (π.initial t)).ncard = (G'.cut L).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext e
    simp [Algebraic.Cutwidth.Multigraph.mem_cut, Multigraph.mem_cut, Layout.mem_initial, L, G']
  have hβ : max ((Fintype.card E : ℝ) - Fintype.card V) 0 ≤ G.cycleRank := by
    refine max_le ?_ (Nat.cast_nonneg _)
    have : Fintype.card E + 1 ≤ G.cycleRank + Fintype.card V := by
      rw [Multigraph.cycleRank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      omega
    have : (Fintype.card E : ℝ) + 1 ≤ G.cycleRank + Fintype.card V := by exact_mod_cast this
    linarith
  have hord := hord L hL
  have hlog := hK (Fintype.card V)
  have : (A + η) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 ≤ (A + η) * G.cycleRank :=
    mul_le_mul_of_nonneg_left hβ (by linarith)
  rw [hcut, Nat.card_eq_fintype_card]
  linarith

/-- The Gaussian coefficient of the frontier method is the frontier coefficient of the
cutwidth development: both are `(3/(2π)) arccos ((1 + 2√2)/4)`. -/
theorem gaussianCoefficient_eq_frontierCoefficient :
    Gaussian.gaussianCoefficient = Algebraic.Cutwidth.Gaussian.frontierCoefficient :=
  rfl

/-- The cutwidth development's Gaussian ordering bound, transferred, gives the same layout
coefficient as `layoutBound_gaussian`. -/
theorem layoutBound_of_orderingBound_frontier :
    LayoutBound 3 (2 * Gaussian.gaussianCoefficient) :=
  LayoutBound.of_orderingBound (mul_nonneg zero_le_two Gaussian.gaussianCoefficient_pos.le)
    Algebraic.Cutwidth.Multigraph.exists_orderingBound_frontier

/-- **Boolean rectangle-freeness.** A Boolean function that is `K`-rectangle-free in the
sense of the cutwidth development accepts a `K`-rectangle-free set. -/
theorem rectangleFree_setOf {n K : ℕ} {f : Cslib.BooleanFunction n}
    (h : Algebraic.Cutwidth.RectangleFree f K) : RectangleFree {x | f x = true} K := by
  classical
  intro X A B hAB
  let U : Finset (Fin n) := X.toFinset
  have hU (i : Fin n) : i ∈ U ↔ i ∈ X := Set.mem_toFinset
  let left : (X → Bool) → (U → Bool) := fun a i => a ⟨i, (hU i).1 i.2⟩
  let right : (↥Xᶜ → Bool) → (↥Uᶜ → Bool) := fun b i =>
    b ⟨i, fun hi => Finset.mem_compl.1 i.2 ((hU i).2 hi)⟩
  have injL : left.Injective := by
    intro a a' haa'
    funext i
    simpa [left] using congrFun haa' ⟨i, (hU i).2 i.2⟩
  have injR : right.Injective := by
    intro b b' hbb'
    funext i
    simpa [right] using congrFun hbb' ⟨i, Finset.mem_compl.2 fun hi => i.2 ((hU i).1 hi)⟩
  have hglue {a : X → Bool} (ha : a ∈ A) {b : ↥Xᶜ → Bool} (hb : b ∈ B) :
      f (Algebraic.Cutwidth.glue U (left a) (right b)) = true := by
    refine hAB (mem_rectangle.2 ⟨?_, ?_⟩)
    · convert ha using 1
      funext i
      simp [Algebraic.Cutwidth.glue, left, (hU i).2 i.2]
    · convert hb using 1
      funext i
      have hi : (i : Fin n) ∉ U := fun h' => i.2 ((hU i).1 h')
      simp [Algebraic.Cutwidth.glue, right, hi]
  have hrect := h U ((Set.toFinite A).toFinset.image left) ((Set.toFinite B).toFinset.image right)
    (by
      intro p hp q hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      exact hglue ((Set.Finite.mem_toFinset _).1 ha) ((Set.Finite.mem_toFinset _).1 hb))
  rw [Finset.card_image_of_injective _ injL, Finset.card_image_of_injective _ injR] at hrect
  rwa [Set.ncard_eq_toFinset_card A, Set.ncard_eq_toFinset_card B]

/-- The accepted set of a Boolean function has as many elements as its accepting inputs. -/
theorem ncard_setOf_eq_card_accepting {n : ℕ} (f : Cslib.BooleanFunction n) :
    {x | f x = true}.ncard = (Algebraic.Cutwidth.accepting f).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [Algebraic.Cutwidth.mem_accepting]

/-- Signed sums of Boolean signs count the accepted elements twice, minus everything. -/
private theorem sum_boolSign {β : Type*} (T : Finset β) (g : β → Bool) :
    ∑ z ∈ T, boolSign (g z) = 2 * ((T.filter fun z => g z = true).card : ℝ) - T.card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (p := fun z => g z = true)
  simp only [boolSign, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have : ((T.filter fun z => ¬ g z = true).card : ℝ) =
      T.card - (T.filter fun z => g z = true).card := by
    rw [← hsplit]; push_cast; ring
  simp only [Bool.not_eq_true] at this ⊢
  rw [this]
  ring

/-- **Extractors have small signed sumset bias.** A flat-source sumset extractor with error
`ν` has signed sumset bias `2 ν`. -/
theorem flatSumsetBias_of_flatSumsetExtractor {n K : ℕ} {f : Cslib.BooleanFunction n} {ν : ℝ}
    (h : Algebraic.Cutwidth.FlatSumsetExtractor f K ν) : FlatSumsetBias f K (2 * ν) := by
  classical
  intro A B hA hB
  set P := (Set.toFinite A).toFinset
  set Q := (Set.toFinite B).toFinset
  have hPA : P.card = A.ncard := (Set.ncard_eq_toFinset_card A).symm
  have hQB : Q.card = B.ncard := (Set.ncard_eq_toFinset_card B).symm
  obtain ⟨hlo, hhi⟩ := h P Q (hPA ▸ hA) (hQB ▸ hB)
  have hsum : sumOn (fun x => sumOn (fun y => boolSign (f (xorInputs x y))) B) A =
      2 * ((Algebraic.Cutwidth.sumsetOnes f P Q).card : ℝ) - P.card * Q.card := by
    simp only [sumOn]
    rw [← Finset.sum_product' (s := P) (t := Q)
      (f := fun x y => boolSign (f (xorInputs x y))), sum_boolSign, Finset.card_product]
    simp only [Algebraic.Cutwidth.sumsetOnes, Nat.cast_mul]
    rfl
  rw [hsum, ← hPA, ← hQB]
  push_cast
  rw [abs_le]
  constructor <;> nlinarith

end Complexity.Frontier

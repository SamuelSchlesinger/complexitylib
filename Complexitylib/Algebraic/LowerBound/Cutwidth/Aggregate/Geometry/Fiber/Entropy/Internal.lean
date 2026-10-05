/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.LowerBound

/-!
# Mixed message weights with constant coordinates omitted

Narrow and wide primary conjunctions receive their separate costs. Designated
conjunction outputs of a nonliteral permutation are constant message coordinates
and contribute no cost, including in the joint support-graph estimate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Algebraic.Aggregate.Geometry Entropy
open scoped Classical

/-- Reconstruct a message from two weighted classes and the remaining nonconstant bits. -/
noncomputable def keyWeightBoundOfClasses {X : Type*} [Fintype X] {g : ℕ}
    (message : X → Fin g → Bool) (T W O : Finset (Fin g))
    (disjoint : Disjoint T W) (outputs : Disjoint (T ∪ W) O)
    (constant : ∀ i ∈ O, ∀ x, message x i = true) {cost : ℝ}
    (classes : WeightBound (fun x => ((fun i : T => message x i),
      fun i : W => message x i)) cost) :
    WeightBound message
      (cost + ((g : ℝ) - T.card - W.card - O.card) * Real.log 2) := by
  let R := {i : Fin g // i ∉ (T ∪ W) ∪ O}
  have other := WeightBound.pi fun i : R => WeightBound.boolean (fun x => message x i)
  let merge (z : ((T → Bool) × (W → Bool)) × (R → Bool)) (i : Fin g) :=
    if ht : i ∈ T then z.1.1 ⟨i, ht⟩ else
      if hw : i ∈ W then z.1.2 ⟨i, hw⟩ else
        if ho : i ∈ O then true else z.2 ⟨i, by simp [ht, hw, ho]⟩
  have merged := (classes.prod other).map merge
  have remainder : Fintype.card R = g - ((T ∪ W) ∪ O).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_subtype_compl fun i : Fin g => i ∈ (T ∪ W) ∪ O
  have counts : T.card + W.card + O.card + Fintype.card R = g := by
    have bound := Finset.card_le_univ ((T ∪ W) ∪ O)
    rw [Finset.card_union_of_disjoint outputs, Finset.card_union_of_disjoint disjoint,
      Fintype.card_fin] at bound
    rw [remainder, Finset.card_union_of_disjoint outputs,
      Finset.card_union_of_disjoint disjoint]
    lia
  have realCounts : (T.card : ℝ) + W.card + O.card + Fintype.card R = g := by
    exact_mod_cast counts
  convert merged using 1
  · funext x i
    dsimp only [merge]
    split
    · rfl
    · split
      · rfl
      · split
        · exact constant i (by assumption) x
        · rfl
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← realCounts]
    ring

/-- A selected pair supplies the marginal quarter-entropy certificate. -/
noncomputable def keyQuarterWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (i : Fin g) (pair : SelectedPair (p.lines i) U) :
    WeightBound (fun x : U → Bool => key p U (glue U x (fun _ => false)) i)
      (Real.binEntropy (1 / 4)) := by
  apply WeightBound.ofTrueCountLE _ (p := 1 / 4) (by norm_num) (by norm_num)
  have count : (4 : ℝ) * (Finset.univ.filter fun x : U → Bool =>
      key p U (glue U x (fun _ => false)) i = true).card ≤ (2 : ℝ) ^ U.card := by
    exact_mod_cast lineSummary_quarter_of_selectedPair (p.lines i) U pair
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Nat.cast_pow, Nat.cast_ofNat]
  linarith

/-- Actual retained classes have either marginal or joint support-graph weights. -/
noncomputable def retainedClassesWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (graph : Bool) :
    WeightBound (fun x : U → Bool =>
      ((fun i : Joint.retainedTwo p U => key p U (glue U x (fun _ => false)) i),
       fun i : Joint.retainedWide p U => key p U (glue U x (fun _ => false)) i))
      ((Joint.retainedTwo p U).card *
          (if graph then Graph.edgeCost else Real.binEntropy (1 / 4)) +
        (if graph then U.card * Graph.vertexCost else 0) +
        (Joint.retainedWide p U).card * Real.binEntropy (1 / 8)) := by
  have wide : WeightBound (fun x : U → Bool =>
      fun i : Joint.retainedWide p U => key p U (glue U x (fun _ => false)) i)
      ((Joint.retainedWide p U).card * Real.binEntropy (1 / 8)) := by
    have bound := WeightBound.pi fun i : Joint.retainedWide p U =>
      Joint.evalLiteralsEighthWeightBoundOfThreeLe (Finset.mem_filter.mp i.property).2.2
    convert bound using 1
    · funext x i
      exact Joint.key_eq_evalLiterals_of_selectedPair p U i
        (Finset.mem_filter.mp i.property).2.selectedPair x
    · simp
  cases graph with
  | false =>
    have narrow := WeightBound.pi fun i : Joint.retainedTwo p U =>
      keyQuarterWeightBound p U i (Finset.mem_filter.mp i.property).2.selectedPair
    simpa using narrow.prod wide
  | true =>
    have bound := Joint.evalLiteralsFamilyWeightBound
      (fun i : Joint.retainedTwo p U => Joint.lineLiterals (p.lines i) U)
      (fun i => (Joint.two_le_literalVars_iff_selectedPair _ _).mpr
        (Finset.mem_filter.mp i.property).2.selectedPair)
    have narrow : WeightBound (fun x : U → Bool =>
        fun i : Joint.retainedTwo p U => key p U (glue U x (fun _ => false)) i)
        ((Joint.retainedTwo p U).card * Graph.edgeCost + U.card * Graph.vertexCost) := by
      convert bound using 1
      · funext x i
        exact Joint.key_eq_evalLiterals_of_selectedPair p U i
          (Finset.mem_filter.mp i.property).2.selectedPair x
      · simp
    simpa using narrow.prod wide

/-- Full messages omit any known constant coordinates outside the retained classes. -/
noncomputable def retainedKeyWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (O : Finset (Fin g))
    (outside : Disjoint (Joint.retainedTwo p U ∪ Joint.retainedWide p U) O)
    (constant : ∀ i ∈ O, ∀ x : U → Bool,
      key p U (glue U x (fun _ => false)) i = true) (graph : Bool) :
    WeightBound (fun x : U → Bool => key p U (glue U x (fun _ => false)))
      (((g : ℝ) - O.card) * Real.log 2 -
        (Joint.retainedTwo p U).card *
          (if graph then Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2
            else Real.log 2 - Real.binEntropy (1 / 4)) -
        (Joint.retainedWide p U).card * (Real.log 2 - Real.binEntropy (1 / 8)) +
        (if graph then U.card * Graph.vertexCost else 0)) := by
  have bound := keyWeightBoundOfClasses _ _ _ O (Joint.disjoint_retained p U)
    outside constant (retainedClassesWeightBound p U graph)
  convert bound using 1
  cases graph <;> simp only [Bool.false_eq_true, ↓reduceIte, Graph.edgeCost] <;> ring

/-- Adding the one designated-output bit preserves the marginal mixed savings. -/
noncomputable def marginalOutputKeyWeightBound {n g : ℕ} (p : Program signature n g)
    (U : Finset (Fin n)) (out : Wire n g) :
    WeightBound (fun x : U → Bool => outputKey p U out (glue U x (fun _ => false)))
      (((g : ℝ) + 1) * Real.log 2 -
        (Joint.retainedTwo p U).card * (Real.log 2 - Real.binEntropy (1 / 4)) -
        (Joint.retainedWide p U).card * (Real.log 2 - Real.binEntropy (1 / 8))) := by
  have gates := retainedKeyWeightBound p U ∅ (by simp) (by simp) false
  let last (x : U → Bool) :=
    if Algebraic.Aggregate.Capacity.selected U out then
      Wire.elim (glue U x (fun _ => false)) (fun _ => false) out else false
  have full := ((WeightBound.boolean last).prod gates).map
    (fun (z : Bool × (Fin g → Bool)) (i : Fin (g + 1)) =>
      Fin.lastCases (motive := fun _ => Bool) z.1 z.2 i)
  convert full using 1
  · rfl
  · simp only [Finset.card_empty, Nat.cast_zero, sub_zero, Bool.false_eq_true,
      ↓reduceIte, add_zero]
    ring

/-- Separate quarter and eighth costs bound any rectangle-free sending side. -/
theorem sender_le_size_of_marginal_messages {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card) :
    (U.card : ℝ) ≤ c.size + 1 + Real.logb 2 K -
      Entropy.bitSaving * (Joint.retainedTwo c.program U).card -
      Shared.wideSaving * (Joint.retainedWide c.program U).card := by
  have bound := Joint.sender_card_le_of_weight_oneWay hK free freeNot U large
    (circuitOneWaySummary c U) (marginalOutputKeyWeightBound c.program U (c.outputs 0))
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have cost :
      (((c.size : ℝ) + 1) * Real.log 2 -
        (Joint.retainedTwo c.program U).card * (Real.log 2 - Real.binEntropy (1 / 4)) -
        (Joint.retainedWide c.program U).card * (Real.log 2 - Real.binEntropy (1 / 8))) /
        Real.log 2 = c.size + 1 -
          Entropy.bitSaving * (Joint.retainedTwo c.program U).card -
          Shared.wideSaving * (Joint.retainedWide c.program U).card := by
    unfold Entropy.bitSaving Entropy.biasSaving Shared.wideSaving Shared.wideEntropy
    field_simp
  rw [cost] at bound
  linarith

/-- Weighted triple retention applies to the marginal narrow and wide costs. -/
theorem input_le_size_of_triple_marginal {n a K : ℕ} (c : Circuit signature n 1)
    (ha : 3 ≤ a) (han : a ≤ n) (hK : 0 < K)
    (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (large : 2 * K ≤ 2 ^ (n - a)) :
    (a : ℝ) ≤ c.size + 1 + Real.logb 2 K - Joint.tripleRetention n a *
      (Entropy.bitSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
        Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card) := by
  obtain ⟨U, hU, retained⟩ := Joint.exists_subset_retained_weight c.program ha han
    Entropy.bitSaving Shared.wideSaving Entropy.bitSaving_pos.le Shared.wideSaving_pos.le
  have complement : Uᶜ.card = n - a := by
    have total : U.card + Uᶜ.card = n := by simp
    lia
  have bound := sender_le_size_of_marginal_messages c hK free freeNot U
    (by simpa only [complement] using large)
  rw [hU] at bound
  linarith

/-- Full-primary retained pairs are exactly the original exact-two gate class. -/
theorem retainedTwo_univ {n g : ℕ} (p : Program signature n g) :
    Joint.retainedTwo p Finset.univ = Algebraic.Aggregate.Geometry.Shared.exactTwo p := by
  ext i
  simp [Joint.retainedTwo, Joint.RetainedTwo, Algebraic.Aggregate.Geometry.Shared.exactTwo]

/-- Both mixed entropy bounds omit the constant conjunction-output coordinates. -/
theorem permutation_input_le_message_cost {n : ℕ} (c : Circuit signature n n)
    (bijective : Function.Bijective (c.eval interpretation))
    (nonliteral : ∀ i j b, c.outputFunction interpretation i ≠ fun x => b ^^ x j)
    (graph : Bool) :
    (1 - if graph then Joint.overlapPenalty else 0) * n ≤
      c.size - outputConjunctionCount c -
        (if graph then Joint.gateSaving else Entropy.bitSaving) *
          (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card -
        Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card := by
  classical
  let U : Finset (Fin n) := Finset.univ
  let O := outputConjunctions c
  have outside : Disjoint
      (Joint.retainedTwo c.program U ∪ Joint.retainedWide c.program U) O := by
    apply Finset.disjoint_left.mpr
    intro i hi ho
    have empty := primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral i ho
    have pair : SelectedPair (c.program.lines i) U := by
      rcases Finset.mem_union.mp hi with ht | hw
      · exact (Finset.mem_filter.mp ht).2.selectedPair
      · exact (Finset.mem_filter.mp hw).2.selectedPair
    have marked := pair.multiPrimary
    simp [multiPrimary, empty] at marked
  have constant (i : Fin c.size) (hi : i ∈ O) (x : U → Bool) :
      key c.program U (glue U x (fun _ => false)) i = true := by
    exact lineSummary_eq_true_of_primaryInputs_eq_empty _ (Finset.mem_filter.mp hi).2
      (primaryInputs_eq_empty_of_output_conjunction c bijective nonliteral i hi) _
  have certificate := retainedKeyWeightBound c.program U O outside constant graph
  have injective : Function.Injective
      (fun x : U → Bool => key c.program U (glue U x (fun _ => false))) := by
    intro x y h
    have same := key_injective_of_permutation c bijective
      (by intro i j; simpa using nonliteral i j false) h
    funext i
    simpa using congrFun same i.val
  have bound := certificate.log_card_le (K := 1) (by decide) (fun message => by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact injective (hx.trans hy.symm))
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, U,
    Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow, Nat.cast_one, Real.log_one, zero_add, retainedTwo_univ] at bound
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have divided := (le_div_iff₀ logpos).mpr bound
  change (n : ℝ) ≤ _ at divided
  have cost :
      (((c.size : ℝ) - O.card) * Real.log 2 -
        (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card *
          (if graph then Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2
            else Real.log 2 - Real.binEntropy (1 / 4)) -
        (Joint.retainedWide c.program Finset.univ).card *
          (Real.log 2 - Real.binEntropy (1 / 8)) +
        (if graph then n * Graph.vertexCost else 0)) / Real.log 2 =
      c.size - outputConjunctionCount c -
        (if graph then Joint.gateSaving else Entropy.bitSaving) *
          (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card -
        Shared.wideSaving * (Joint.retainedWide c.program Finset.univ).card +
        (if graph then Joint.overlapPenalty * n else 0) := by
    cases graph <;>
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;>
      simp only [Joint.gateSaving, Joint.overlapPenalty, Joint.quarterEntropy, Entropy.bitSaving,
        Entropy.biasSaving, Shared.wideSaving, Shared.wideEntropy, Graph.vertexCost,
        outputConjunctionCount] <;>
      dsimp only [O] <;>
      field_simp
  rw [cost] at divided
  cases graph <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at * <;> linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber

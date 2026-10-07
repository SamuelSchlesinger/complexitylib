/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.InitialPredicates
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.TowerProfiles
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.QuantitativeProfiles
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Or
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Reindex

/-!
# Sensitivity separation: construction

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Construction.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- The initial family, recursively constructed predicates, and final OR. -/

noncomputable section
open scoped Classical

namespace Internal

/-- Extend the initial Hamming-ball predicates to all index counts. -/
def constructionBase (d M : ℕ) := baseExtension (d + 1) (initialFamily d M)

/-- Coordinates for the regular-tournament construction at a given level. -/
abbrev ConstructionCoordinates (d M r n : ℕ) :=
  TowerCoordinates (2 * M ^ 2 + 1) r (Fin M × Fin (d + 2)) n

/-- The single remaining predicate after all recursive levels. -/
def terminalPredicate {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (ConstructionCoordinates d M r d → Bool) → Bool :=
  towerFamily T.toTournament A.label (constructionBase d M) d 1 0

theorem construction_base_nested (d M : ℕ) :
    NestedFamily (constructionBase d M (d + 1)) := by
  simpa only [constructionBase, baseExtension_same] using
      initialFamily_nested d M

theorem construction_base_zero (d M : ℕ) :
    ∀ q, constructionBase d M (1 + d) q (fun _ => false) = false := by
  rw [Nat.add_comm 1 d]
  simpa only [constructionBase, baseExtension_same] using
      initialFamily_zero d M

theorem construction_base_blocks (d M : ℕ) :
    ∀ b q, constructionBase d M (1 + d) q
      (flip (fun _ => false) (baseBlock b)) = true := by
  rw [Nat.add_comm 1 d]
  intro b q
  simpa only [constructionBase, baseExtension_same] using
      initialFamily_baseBlock d M q b

theorem terminalPredicate_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    terminalPredicate d T A (fun _ => false) = false :=
  towerFamily_zero T.toTournament A.label (constructionBase d M) hr d 1
    (construction_base_zero d M) 0

theorem terminalPredicate_blocks {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r)
    (b : TowerBlockIndex (2 * M ^ 2 + 1) (Fin M) d) :
    terminalPredicate d T A (flip (fun _ => false)
      (towerBlocks (r := r) (baseBlock (L := d + 2)) d b)) = true :=
  towerFamily_blocks T.toTournament A.label (constructionBase d M)
    (baseBlock (L := d + 2)) hr d 1 (construction_base_zero d M)
    (construction_base_blocks d M) b 0

theorem terminalPredicate_blockSensitivity {M r : ℕ} (d : ℕ)
    (T : RegularTournament M) (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (terminalPredicate d T A) (fun _ => false) := by
  have h := le_blockSensitivityAt_of_family (terminalPredicate d T A) (fun _ => false)
    (towerBlocks (r := r) (baseBlock (L := d + 2)) d)
    (towerBlocks_nonempty (baseBlock (L := d + 2)) hr
      (baseBlock_nonempty (by omega)) d)
    (towerBlocks_pairwise (baseBlock (L := d + 2)) baseBlock_disjoint d)
    (fun b => by rw [terminalPredicate_blocks d T A hr, terminalPredicate_zero d T A hr]; decide)
  simpa only [tower_block_index_card, Fintype.card_fin, Nat.mul_comm] using h

theorem construction_profiles {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    ∀ n ≤ d,
      towerSide T.toTournament A.label (constructionBase d M) (d + 1) n false ≤
        2 * (d + 2) * M ^ n ∧
      towerSide T.toTournament A.label (constructionBase d M) (d + 1) n true ≤
        2 * (d + 2) * M ^ (n + 1) := by
  have hstep (n : ℕ) (hn : n < d) := tower_four_recurrences T A (constructionBase d M)
    (d + 1) n (by omega) hr (construction_base_nested d M)
  apply quantitative_profile_bounds d (d + 2) M r hM hbudget
    (towerSide T.toTournament A.label (constructionBase d M) (d + 1))
    (towerJoint T.toTournament A.label (constructionBase d M) (d + 1))
  · simpa only [towerSide_zero, constructionBase, baseExtension_same] using
      initialFamily_side_zero d M
  · simpa only [towerSide_zero, constructionBase, baseExtension_same] using
      initialFamily_side_one d M
  · simpa only [towerJoint_zero, constructionBase, baseExtension_same] using
      initialFamily_joint d M false
  · simpa only [towerJoint_zero, constructionBase, baseExtension_same] using
      initialFamily_joint d M true
  · exact fun n hn => (hstep n hn).2.2.1
  · exact fun n hn => (hstep n hn).1
  · exact fun n hn => (hstep n hn).2.2.2
  · exact fun n hn => (hstep n hn).2.1

theorem terminalPredicate_sensitivityAt {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    (∀ x, terminalPredicate d T A x = false →
      sensitivityAt (terminalPredicate d T A) x ≤ 2 * (d + 2) * M ^ d) ∧
    (∀ x, terminalPredicate d T A x = true →
      sensitivityAt (terminalPredicate d T A) x ≤ 2 * (d + 2) * M ^ (d + 1)) := by
  have hs := construction_profiles d T A hM hr hbudget d (le_refl d)
  have he : d + 1 - d = 1 := by omega
  simp only [towerSide] at hs
  rw [he] at hs
  exact ⟨fun x hx => (sensitivityAt_le_sideSensitivity _ false 0 x hx).trans hs.1,
    fun x hx => (sensitivityAt_le_sideSensitivity _ true 0 x hx).trans hs.2⟩

/-- Disjoin `M` independent copies of the terminal predicate. -/
def finalBoolean {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (Fin M × ConstructionCoordinates d M r d → Bool) → Bool :=
  orCopies (K := Fin M) (terminalPredicate d T A)

theorem finalBoolean_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    finalBoolean d T A (fun _ => false) = false :=
  orCopies_zero _ (terminalPredicate_zero d T A hr)

theorem finalBoolean_sensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    sensitivity (finalBoolean d T A) ≤ 2 * (d + 2) * M ^ (d + 1) := by
  obtain ⟨h₀, h₁⟩ := terminalPredicate_sensitivityAt d T A hM hr hbudget
  have h := sensitivity_orCopies_le (K := Fin M) (terminalPredicate d T A) _ _ h₀ h₁
  have he : M * (2 * (d + 2) * M ^ d) = 2 * (d + 2) * M ^ (d + 1) := by ring
  simpa only [finalBoolean, Fintype.card_fin, he, max_self] using h

theorem finalBoolean_blockSensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (finalBoolean d T A) (fun _ => false) := by
  have h := (Nat.mul_le_mul_left M (terminalPredicate_blockSensitivity d T A hr)).trans
    (by simpa only [Fintype.card_fin] using
      blockSensitivityAt_orCopies_zero (K := Fin M) _ (terminalPredicate_zero d T A hr))
  change M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt
    (orCopies (K := Fin M) (terminalPredicate d T A)) (fun _ => false)
  calc
    _ = M * (M * (2 * M ^ 2 + 1) ^ d) := by ring
    _ ≤ _ := h

/-- Number of coordinates of the final Boolean function. -/
def constructionDimension (d M r : ℕ) : ℕ :=
  (d + 2) * M ^ 2 * ((2 * M ^ 2 + 1) * r) ^ d

theorem final_coordinates_card (d M r : ℕ) :
    Fintype.card (Fin M × ConstructionCoordinates d M r d) = constructionDimension d M r := by
  rw [Fintype.card_prod, tower_coordinates_card]
  simp only [Fintype.card_prod, Fintype.card_fin, constructionDimension]
  ring

/-- Reindex the final Boolean function onto an ordinary finite Boolean cube. -/
def finalWitness {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) : (Fin (constructionDimension d M r) → Bool) → Bool :=
  reindex (Fintype.equivFinOfCardEq (final_coordinates_card d M r)) (finalBoolean d T A)

theorem finalWitness_zero {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    finalWitness d T A (fun _ => false) = false := finalBoolean_zero d T A hr

theorem finalWitness_sensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hM : 0 < M) (hr : 0 < r)
    (hbudget : ((max r 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2) :
    sensitivity (finalWitness d T A) ≤ 2 * (d + 2) * M ^ (d + 1) := by
  rw [finalWitness, sensitivity_reindex]
  exact finalBoolean_sensitivity d T A hM hr hbudget

theorem finalWitness_blockSensitivity {M r : ℕ} (d : ℕ) (T : RegularTournament M)
    (A : GoodLabeling T.toTournament r) (hr : 0 < r) :
    M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt (finalWitness d T A) (fun _ => false) := by
  rw [finalWitness, blockSensitivityAt_reindex]
  exact finalBoolean_blockSensitivity d T A hr

theorem constructionDimension_pos {d M r : ℕ} (hM : 0 < M) (hr : 0 < r) :
    0 < constructionDimension d M r := by
  unfold constructionDimension
  positivity

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity

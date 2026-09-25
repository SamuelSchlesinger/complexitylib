/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Approximation
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Plucking
public import Mathlib.Data.Finset.Prod

/-!
# Bounded-width clique approximators

An approximator is a finite disjunction of clique indicators.  OR takes the
union of term families.  AND replaces a pair of clique indicators by the
clique on their combined nontrivial vertex sets; terms wider than `width` are
discarded, and the result is sunflower-normalized.

The special cases in `joinTerms` identify zero- and one-vertex indicators
with the Boolean constant `true`.  This is essential: blindly adjoining a
singleton to another term would introduce edges that were not present in the
conjunction.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique
namespace Approx

noncomputable section

/-- A finite family of clique-indicator vertex sets. -/
abbrev Family (n : Nat) := Plucking.Family n

/-- A clique DNF accepts a graph when one of its terms is contained. -/
def Accepts
    (family : Family n)
    (assignment : Fin (edgeCount n) → Bool) : Prop :=
  ∃ vertices ∈ family, Contains assignment vertices

instance (family : Family n) (assignment : Fin (edgeCount n) → Bool) :
    Decidable (Accepts family assignment) := by
  classical
  exact Classical.propDecidable _

/-- Boolean semantics of a clique DNF. -/
def decode
    (family : Family n)
    (assignment : Fin (edgeCount n) → Bool) : Bool :=
  decide (Accepts family assignment)

@[simp] theorem decode_eq_true
    (family : Family n)
    (assignment : Fin (edgeCount n) → Bool) :
    decode family assignment = true ↔ Accepts family assignment := by
  simp [decode]

@[simp] theorem decode_eq_false
    (family : Family n)
    (assignment : Fin (edgeCount n) → Bool) :
    decode family assignment = false ↔ ¬ Accepts family assignment := by
  simp [decode]

/-- The two endpoints of an input edge. -/
def inputTerm (input : Fin (edgeCount n)) : Finset (Fin n) :=
  let edge := (edgeEquiv n).symm input
  {edge.1.1, edge.1.2}

/-- The one-term approximator for an input variable. -/
def inputFamily (input : Fin (edgeCount n)) : Family n :=
  {inputTerm input}

private theorem inputTerm_card (input : Fin (edgeCount n)) :
    (inputTerm input).card = 2 := by
  classical
  let edge := (edgeEquiv n).symm input
  have different : edge.1.1 ≠ edge.1.2 := ne_of_lt edge.2
  simp [inputTerm, edge, different]

/-- The input term denotes exactly its edge variable. -/
theorem contains_inputTerm_iff
    (assignment : Fin (edgeCount n) → Bool)
    (input : Fin (edgeCount n)) :
    Contains assignment (inputTerm input) ↔ assignment input = true := by
  classical
  let target := (edgeEquiv n).symm input
  constructor
  · intro contains
    have inside : target.Inside (inputTerm input) := by
      simp [Edge.Inside, inputTerm, target]
    simpa [target] using contains target inside
  · intro targetTrue edge inside
    have firstCases : edge.1.1 = target.1.1 ∨ edge.1.1 = target.1.2 := by
      simpa [Edge.Inside, inputTerm, target] using inside.1
    have secondCases : edge.1.2 = target.1.1 ∨ edge.1.2 = target.1.2 := by
      simpa [Edge.Inside, inputTerm, target] using inside.2
    have equal : edge = target := by
      apply Subtype.ext
      apply Prod.ext
      · rcases firstCases with first | first
        · exact first
        · rcases secondCases with second | second
          · omega
          · omega
      · rcases secondCases with second | second
        · rcases firstCases with first | first
          · omega
          · omega
        · exact second
    rw [equal]
    simpa [target] using targetTrue

@[simp] theorem decode_inputFamily
    (assignment : Fin (edgeCount n) → Bool)
    (input : Fin (edgeCount n)) :
    decode (inputFamily input) assignment = assignment input := by
  cases value : assignment input <;>
    simp [decode, Accepts, inputFamily, contains_inputTerm_iff, value]

/-- Zero- and one-vertex clique indicators are the Boolean constant `true`.
When conjoining terms, discard such a vacuous side; otherwise take the union. -/
def joinTerms
    (left right : Finset (Fin n)) : Finset (Fin n) :=
  if left.card ≤ 1 then right
  else if right.card ≤ 1 then left
  else left ∪ right

/-- Raw OR before truncation and plucking. -/
def rawOr (left right : Family n) : Family n := left ∪ right

/-- Raw approximate AND before truncation and plucking. -/
def rawAnd (left right : Family n) : Family n :=
  (left ×ˢ right).image fun pair => joinTerms pair.1 pair.2

/-- Discard terms wider than `width`. -/
def truncate (width : Nat) (family : Family n) : Family n :=
  family.filter fun set => set.card ≤ width

private theorem truncate_bounded (width : Nat) (family : Family n) :
    Plucking.Bounded width (truncate width family) := by
  intro set present
  exact (Finset.mem_filter.mp present).2

/-- The bounded raw family produced at a gate, before normalization. -/
def gateFamily
    (width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → Family n) : Family n :=
  match op with
  | .or => truncate width <| rawOr
      (arguments 0) (arguments 1)
  | .and => truncate width <| rawAnd
      (arguments 0) (arguments 1)

/-- Gate preprocessing enforces the width bound before normalization. -/
theorem gateFamily_bounded
    (width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → Family n) :
    Plucking.Bounded width (gateFamily width op arguments) := by
  cases op <;> exact truncate_bounded width _

/-- The bounded-width approximate interpretation of binary AND/OR. -/
def interpretation
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (width : Nat) : Interpretation AndOr.signature (Family n)
  | op, arguments =>
      Plucking.normalize petalCount two_le (gateFamily width op arguments)

/-- Every approximate gate result has bounded width. -/
theorem interpretation_bounded
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → Family n) :
    Plucking.Bounded width
      (interpretation petalCount two_le width op arguments) := by
  exact Plucking.normalize_bounded petalCount two_le _
    (gateFamily_bounded width op arguments)

/-- Every approximate gate result has at most the sunflower bound many terms. -/
theorem interpretation_card_le
    (petalCount : Nat)
    (two_le : 2 ≤ petalCount)
    (width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → Family n) :
    (interpretation petalCount two_le width op arguments).card ≤
      Sunflower.bound petalCount width := by
  exact Plucking.normalize_card_le petalCount two_le _
    (gateFamily_bounded width op arguments)

/-- Input approximators have bounded width once the width is at least two. -/
theorem inputFamily_bounded
    (two_le_width : 2 ≤ width)
    (input : Fin (edgeCount n)) :
    Plucking.Bounded width (inputFamily input) := by
  intro set present
  simp only [inputFamily, Finset.mem_singleton] at present
  subst set
  rw [inputTerm_card]
  exact two_le_width

/-- Input approximators have one term. -/
@[simp] theorem inputFamily_card (input : Fin (edgeCount n)) :
    (inputFamily input).card = 1 := by
  simp [inputFamily]

/-- A normalized approximator packages the two invariants needed for uniform
local error bounds: bounded term width and bounded family cardinality. -/
structure NormalFamily
    (n petalCount width : Nat) where
  /-- The underlying clique DNF. -/
  family : Family n
  /-- Every term respects the approximation width. -/
  bounded : Plucking.Bounded width family
  /-- The family respects the elementary sunflower cardinality bound. -/
  card_le : family.card ≤ Sunflower.bound petalCount width

/-- The elementary sunflower bound is nonzero. -/
theorem one_le_sunflower_bound
    (petalCount width : Nat)
    (two_le_petals : 2 ≤ petalCount) :
    1 ≤ Sunflower.bound petalCount width := by
  simp only [Sunflower.bound]
  have basePositive : 0 < petalCount - 1 := by omega
  have positive :
      0 < (width + 1) * ((petalCount - 1) ^ width * width.factorial) := by
    exact Nat.mul_pos (by omega)
      (Nat.mul_pos (pow_pos basePositive width) (Nat.factorial_pos width))
  omega

/-- Input variables, viewed as normalized one-term approximators. -/
def normalInput
    (petalCount width : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width)
    (input : Fin (edgeCount n)) : NormalFamily n petalCount width where
  family := inputFamily input
  bounded := inputFamily_bounded two_le_width input
  card_le := by
    rw [inputFamily_card]
    exact one_le_sunflower_bound petalCount width two_le_petals

/-- Gate evaluation on normalized approximators. -/
def normalInterpretation
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (width : Nat) : Interpretation AndOr.signature
      (NormalFamily n petalCount width) :=
  fun op arguments =>
    { family := interpretation petalCount two_le_petals width op
        (fun input => (arguments input).family)
      bounded := interpretation_bounded petalCount two_le_petals width op _
      card_le := interpretation_card_le petalCount two_le_petals width op _ }

/-- Boolean semantics of a normalized approximator. -/
def normalDecode
    (family : NormalFamily n petalCount width)
    (assignment : Fin (edgeCount n) → Bool) : Bool :=
  decode family.family assignment

@[simp] theorem normalDecode_eq_true
    (family : NormalFamily n petalCount width)
    (assignment : Fin (edgeCount n) → Bool) :
    normalDecode family assignment = true ↔
      Accepts family.family assignment := by
  simp [normalDecode]

@[simp] theorem normalDecode_input
    (petalCount width : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width)
    (assignment : Fin (edgeCount n) → Bool)
    (input : Fin (edgeCount n)) :
    normalDecode
        (normalInput petalCount width two_le_petals two_le_width input)
        assignment =
      assignment input := by
  simp [normalDecode, normalInput]

private theorem contains_of_card_le_one
    (assignment : Fin (edgeCount n) → Bool)
    (vertices : Finset (Fin n))
    (small : vertices.card ≤ 1) :
    Contains assignment vertices := by
  intro edge inside
  have endpoints : {edge.1.1, edge.1.2} ⊆ vertices := by
    intro vertex present
    simp only [Finset.mem_insert, Finset.mem_singleton] at present
    exact present.elim (fun equal => equal ▸ inside.1)
      (fun equal => equal ▸ inside.2)
  have two_le : 2 ≤ vertices.card := by
    simpa [ne_of_lt edge.2] using Finset.card_le_card endpoints
  omega

/-- A joined term implies both input terms on every graph. -/
theorem contains_of_contains_joinTerms
    (assignment : Fin (edgeCount n) → Bool)
    (left right : Finset (Fin n))
    (contains : Contains assignment (joinTerms left right)) :
    Contains assignment left ∧ Contains assignment right := by
  unfold joinTerms at contains
  split at contains
  next leftSmall =>
    exact ⟨contains_of_card_le_one assignment left leftSmall, contains⟩
  next leftLarge =>
    split at contains
    next rightSmall =>
      exact ⟨contains, contains_of_card_le_one assignment right rightSmall⟩
    next rightLarge =>
      exact ⟨Contains.mono_vertices Finset.subset_union_left contains,
        Contains.mono_vertices Finset.subset_union_right contains⟩

/-- On a minimal positive clique graph, conjoining two accepted terms is
represented exactly by `joinTerms`. -/
theorem contains_joinTerms_cliqueAssignment
    (clique : Finset (Fin n))
    (left right : Finset (Fin n))
    (leftContains : Contains (cliqueAssignment clique) left)
    (rightContains : Contains (cliqueAssignment clique) right) :
    Contains (cliqueAssignment clique) (joinTerms left right) := by
  unfold joinTerms
  split
  · exact rightContains
  next leftLarge =>
    split
    · exact leftContains
    next rightLarge =>
      apply Contains.mono_vertices _ <|
        show Contains (cliqueAssignment clique) clique from by
          intro edge inside
          simp [cliqueAssignment_edge, inside]
      exact Finset.union_subset
        (subset_of_contains_cliqueAssignment (by omega) leftContains)
        (subset_of_contains_cliqueAssignment (by omega) rightContains)

/-- Raw OR has exactly Boolean-OR semantics. -/
theorem accepts_rawOr_iff
    (assignment : Fin (edgeCount n) → Bool)
    (left right : Family n) :
    Accepts (rawOr left right) assignment ↔
      Accepts left assignment ∨ Accepts right assignment := by
  constructor
  · rintro ⟨vertices, present, contains⟩
    rw [rawOr, Finset.mem_union] at present
    exact present.elim
      (fun inLeft => Or.inl ⟨vertices, inLeft, contains⟩)
      (fun inRight => Or.inr ⟨vertices, inRight, contains⟩)
  · rintro (⟨vertices, present, contains⟩ | ⟨vertices, present, contains⟩)
    · exact ⟨vertices, Finset.mem_union_left _ present, contains⟩
    · exact ⟨vertices, Finset.mem_union_right _ present, contains⟩

/-- Raw approximate AND implies exact Boolean AND on every graph. -/
theorem accepts_left_right_of_accepts_rawAnd
    (assignment : Fin (edgeCount n) → Bool)
    (left right : Family n)
    (accepted : Accepts (rawAnd left right) assignment) :
    Accepts left assignment ∧ Accepts right assignment := by
  classical
  obtain ⟨joined, joinedPresent, joinedContains⟩ := accepted
  rw [rawAnd, Finset.mem_image] at joinedPresent
  obtain ⟨pair, pairPresent, rfl⟩ := joinedPresent
  rw [Finset.mem_product] at pairPresent
  have both := contains_of_contains_joinTerms assignment pair.1 pair.2 joinedContains
  exact ⟨⟨pair.1, pairPresent.1, both.1⟩,
    ⟨pair.2, pairPresent.2, both.2⟩⟩

end

end Approx
end Clique
end Monotone
end Algebraic

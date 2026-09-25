/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Positive
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Negative errors in the monotone CLIQUE approximation

The negative test graphs are complete multipartite graphs represented by
vertex colorings.  A term accepts exactly when its vertices receive distinct
colors.  If a sunflower pluck accepts its core but none of its petals, every
petal supplies a collision involving a private petal vertex.  Choosing one
such collision per petal leaves one independently determined coordinate per
petal, yielding the integral bound

`width ^ (2 * petals) * colors ^ (n - petals)`.

The proof is a direct finite-cardinality count.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique
namespace Negative

noncomputable section

open Approx

/-- A coloring graph contains a clique term exactly when the coloring is
injective on the term's vertices. -/
theorem contains_coloringAssignment_iff
    (coloring : Coloring n r)
    (vertices : Finset (Fin n)) :
    Contains (coloringAssignment coloring) vertices ↔
      Set.InjOn coloring ↑vertices := by
  constructor
  · exact coloring_injectiveOn_of_contains coloring vertices
  · intro injective edge inside
    rw [coloringAssignment_edge, decide_eq_true_eq]
    intro equal
    have endpointsEqual := injective inside.1 inside.2 equal
    exact (ne_of_lt edge.2) endpointsEqual

/-- Ordered collision witnesses whose first endpoint is outside the core. -/
def collisionPairs
    (core petal : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  ((petal \ core) ×ˢ petal).filter fun pair => pair.1 ≠ pair.2

@[simp] theorem mem_collisionPairs
    (pair : Fin n × Fin n)
    (core petal : Finset (Fin n)) :
    pair ∈ collisionPairs core petal ↔
      pair.1 ∈ petal ∧ pair.1 ∉ core ∧
      pair.2 ∈ petal ∧ pair.1 ≠ pair.2 := by
  simp [collisionPairs, and_assoc]

/-- One collision choice for every petal. -/
abbrev Profile
    (petals : Finset (Finset (Fin n)))
    (core : Finset (Fin n)) :=
  ∀ petal : ↥petals, ↥(collisionPairs core petal.1)

private theorem card_collisionPairs_le
    (core petal : Finset (Fin n))
    (petal_le : petal.card ≤ width) :
    (collisionPairs core petal).card ≤ width ^ 2 := by
  calc
    (collisionPairs core petal).card ≤
        ((petal \ core) ×ˢ petal).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (petal \ core).card * petal.card := by simp
    _ ≤ width * width := Nat.mul_le_mul
      (Finset.card_le_card Finset.sdiff_subset |>.trans petal_le) petal_le
    _ = width ^ 2 := by simp [pow_two]

/-- There are at most `width^(2*petals.card)` collision profiles. -/
theorem card_profile_le
    (petals : Finset (Finset (Fin n)))
    (core : Finset (Fin n))
    (bounded : ∀ petal ∈ petals, petal.card ≤ width) :
    Fintype.card (Profile petals core) ≤
      (width ^ 2) ^ petals.card := by
  classical
  rw [Fintype.card_pi]
  calc
    ∏ petal : ↥petals, Fintype.card ↥(collisionPairs core petal.1) ≤
        ∏ _petal : ↥petals, width ^ 2 := by
      refine Finset.prod_le_prod fun petal _ => ?_
      exact (Fintype.card_coe _).trans_le
        (card_collisionPairs_le core petal.1 (bounded petal.1 petal.2))
    _ = (width ^ 2) ^ petals.card := by simp

/-- The private (first) vertices selected by a collision profile. -/
def selected
    {petals : Finset (Finset (Fin n))}
    {core : Finset (Fin n)}
    (profile : Profile petals core) : Finset (Fin n) :=
  Finset.univ.image fun petal : ↥petals => (profile petal).1.1

/-- Distinct sunflower petals select distinct private vertices. -/
theorem selectedVertex_injective
    {petals : Finset (Finset (Fin n))}
    {core : Finset (Fin n)}
    (sunflower : Sunflower.IsSunflowerWithCore petals core)
    (profile : Profile petals core) :
    Function.Injective fun petal : ↥petals => (profile petal).1.1 := by
  intro left right equal
  apply Subtype.ext
  by_contra different
  have leftData := (mem_collisionPairs (profile left).1 core left.1).mp
    (profile left).2
  have rightData := (mem_collisionPairs (profile right).1 core right.1).mp
    (profile right).2
  have equalVertices : (profile left).1.1 = (profile right).1.1 := equal
  have inIntersection : (profile left).1.1 ∈ left.1 ∩ right.1 := by
    rw [Finset.mem_inter]
    refine ⟨leftData.1, ?_⟩
    rw [equalVertices]
    exact rightData.1
  have intersection := sunflower left.2 right.2 different
  rw [intersection] at inIntersection
  exact leftData.2.1 inIntersection

private theorem selected_card
    {petals : Finset (Finset (Fin n))}
    {core : Finset (Fin n)}
    (sunflower : Sunflower.IsSunflowerWithCore petals core)
    (profile : Profile petals core) :
    (selected profile).card = petals.card := by
  classical
  rw [selected, Finset.card_image_of_injective _
    (selectedVertex_injective sunflower profile), Finset.card_univ,
    Fintype.card_coe]

/-- A selected collision's dependency (its second endpoint) is never itself
selected by the profile. -/
theorem second_not_selected
    {petals : Finset (Finset (Fin n))}
    {core : Finset (Fin n)}
    (sunflower : Sunflower.IsSunflowerWithCore petals core)
    (profile : Profile petals core)
    (petal : ↥petals) :
    (profile petal).1.2 ∉ selected profile := by
  classical
  intro present
  rw [selected, Finset.mem_image] at present
  obtain ⟨other, _, selectedEqual⟩ := present
  have petalData := (mem_collisionPairs (profile petal).1 core petal.1).mp
    (profile petal).2
  have otherData := (mem_collisionPairs (profile other).1 core other.1).mp
    (profile other).2
  by_cases same : petal = other
  · subst other
    exact petalData.2.2.2 selectedEqual
  · have inIntersection : (profile other).1.1 ∈ petal.1 ∩ other.1 := by
      rw [Finset.mem_inter]
      refine ⟨?_, otherData.1⟩
      rw [selectedEqual]
      exact petalData.2.2.1
    have intersection := sunflower petal.2 other.2
      (fun equal => same (Subtype.ext equal))
    rw [intersection] at inIntersection
    exact otherData.2.1 inIntersection

/-- Colorings satisfying every equality selected by one profile. -/
def profileColorings
    (r : Nat)
    {petals : Finset (Finset (Fin n))}
    {core : Finset (Fin n)}
    (profile : Profile petals core) : Finset (Coloring n r) :=
  Finset.univ.filter fun coloring =>
    ∀ petal, coloring (profile petal).1.1 = coloring (profile petal).1.2

@[simp] theorem mem_profileColorings
    (coloring : Coloring n r)
    {petals : Finset (Finset (Fin n))}
    {core : Finset (Fin n)}
    (profile : Profile petals core) :
    coloring ∈ profileColorings r profile ↔
      ∀ petal, coloring (profile petal).1.1 =
        coloring (profile petal).1.2 := by
  simp [profileColorings]

/-- Fixing one private collision coordinate per petal leaves at most
`colors^(n-petals)` colorings. -/
theorem card_profileColorings_le
    (r : Nat)
    {petals : Finset (Finset (Fin n))}
    {core : Finset (Fin n)}
    (sunflower : Sunflower.IsSunflowerWithCore petals core)
    (profile : Profile petals core) :
    (profileColorings r profile).card ≤ r ^ (n - petals.card) := by
  classical
  let outside := (Finset.univ : Finset (Fin n)) \ selected profile
  let restriction : ↥(profileColorings r profile) → (↥outside → Fin r) :=
    fun coloring vertex => coloring.1 vertex.1
  have injective : Function.Injective restriction := by
    intro left right restrictionsEqual
    apply Subtype.ext
    funext vertex
    by_cases isSelected : vertex ∈ selected profile
    · rw [selected, Finset.mem_image] at isSelected
      obtain ⟨petal, _, selectedEqual⟩ := isSelected
      have leftConstraint := (mem_profileColorings left.1 profile).mp left.2 petal
      have rightConstraint := (mem_profileColorings right.1 profile).mp right.2 petal
      have dependencyOutside : (profile petal).1.2 ∈ outside := by
        simp only [outside, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact second_not_selected sunflower profile petal
      have outsideEqual := congrFun restrictionsEqual
        ⟨(profile petal).1.2, dependencyOutside⟩
      change left.1 vertex = right.1 vertex
      rw [← selectedEqual, leftConstraint, rightConstraint]
      exact outsideEqual
    · have vertexOutside : vertex ∈ outside := by
        simp only [outside, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact isSelected
      exact congrFun restrictionsEqual ⟨vertex, vertexOutside⟩
  have cardinality := Fintype.card_le_of_injective restriction injective
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe] at cardinality
  have selectedSubset : selected profile ⊆ (Finset.univ : Finset (Fin n)) :=
    fun _ _ => Finset.mem_univ _
  dsimp only [outside] at cardinality
  rw [Finset.card_sdiff_of_subset selectedSubset,
    Finset.card_univ, Fintype.card_fin,
    selected_card sunflower profile] at cardinality
  exact cardinality

/-- Failure of injectivity on a petal, together with injectivity on the core,
supplies a collision whose first endpoint is private to the petal. -/
theorem exists_collisionPair_of_not_injective
    (coloring : Coloring n r)
    (core petal : Finset (Fin n))
    (coreInjective : Set.InjOn coloring ↑core)
    (petalNotInjective : ¬ Set.InjOn coloring ↑petal) :
    ∃ pair : ↥(collisionPairs core petal),
      coloring pair.1.1 = coloring pair.1.2 := by
  classical
  unfold Set.InjOn at petalNotInjective
  push Not at petalNotInjective
  obtain ⟨left, leftPresent, right, rightPresent, colorsEqual, different⟩ :=
    petalNotInjective
  have outside : left ∉ core ∨ right ∉ core := by
    by_contra neither
    push Not at neither
    exact different (coreInjective neither.1 neither.2 colorsEqual)
  rcases outside with leftOutside | rightOutside
  · refine ⟨⟨(left, right), ?_⟩, colorsEqual⟩
    rw [mem_collisionPairs]
    exact ⟨leftPresent, leftOutside, rightPresent, different⟩
  · refine ⟨⟨(right, left), ?_⟩, colorsEqual.symm⟩
    rw [mem_collisionPairs]
    exact ⟨rightPresent, rightOutside, leftPresent, different.symm⟩

/-- Colorings that accept a sunflower core but reject every petal. -/
def sunflowerBad
    (r : Nat)
    (petals : Finset (Finset (Fin n)))
    (core : Finset (Fin n)) : Finset (Coloring n r) :=
  Finset.univ.filter fun coloring =>
    Set.InjOn coloring ↑core ∧
      ∀ petal ∈ petals, ¬ Set.InjOn coloring ↑petal

@[simp] theorem mem_sunflowerBad
    (coloring : Coloring n r)
    (petals : Finset (Finset (Fin n)))
    (core : Finset (Fin n)) :
    coloring ∈ sunflowerBad r petals core ↔
      Set.InjOn coloring ↑core ∧
        ∀ petal ∈ petals, ¬ Set.InjOn coloring ↑petal := by
  simp [sunflowerBad]

/-- Union of the equality classes associated with all collision profiles. -/
def profileCover
    (r : Nat)
    (petals : Finset (Finset (Fin n)))
    (core : Finset (Fin n)) : Finset (Coloring n r) :=
  (Finset.univ : Finset (Profile petals core)).biUnion
    (profileColorings r)

private theorem sunflowerBad_subset_profileCover
    (r : Nat)
    (petals : Finset (Finset (Fin n)))
    (core : Finset (Fin n)) :
    sunflowerBad r petals core ⊆ profileCover r petals core := by
  classical
  intro coloring bad
  rw [mem_sunflowerBad] at bad
  have collision (petal : ↥petals) :
      ∃ pair : ↥(collisionPairs core petal.1),
        coloring pair.1.1 = coloring pair.1.2 :=
    exists_collisionPair_of_not_injective coloring core petal.1 bad.1
      (bad.2 petal.1 petal.2)
  let profile : Profile petals core :=
    fun petal => Classical.choose (collision petal)
  have satisfies : ∀ petal,
      coloring (profile petal).1.1 = coloring (profile petal).1.2 := by
    intro petal
    exact Classical.choose_spec (collision petal)
  rw [profileCover, Finset.mem_biUnion]
  exact ⟨profile, Finset.mem_univ _,
    (mem_profileColorings coloring profile).mpr satisfies⟩

/-- Integral error cap for one `petalCount`-sunflower pluck. -/
def pluckErrorCap
    (n r petalCount width : Nat) : Nat :=
  (width ^ 2) ^ petalCount * r ^ (n - petalCount)

/-- Direct finite count for the bad colorings of one bounded sunflower. -/
theorem card_sunflowerBad_le
    (r petalCount width : Nat)
    (petals : Finset (Finset (Fin n)))
    (core : Finset (Fin n))
    (petalsCard : petals.card = petalCount)
    (sunflower : Sunflower.IsSunflowerWithCore petals core)
    (bounded : ∀ petal ∈ petals, petal.card ≤ width) :
    (sunflowerBad r petals core).card ≤
      pluckErrorCap n r petalCount width := by
  classical
  calc
    (sunflowerBad r petals core).card ≤
        (profileCover r petals core).card :=
      Finset.card_le_card (sunflowerBad_subset_profileCover r petals core)
    _ ≤ ∑ profile : Profile petals core,
        (profileColorings r profile).card := Finset.card_biUnion_le
    _ ≤ ∑ _profile : Profile petals core,
        r ^ (n - petals.card) := by
      apply Finset.sum_le_sum
      intro profile _
      exact card_profileColorings_le r sunflower profile
    _ = Fintype.card (Profile petals core) *
        r ^ (n - petals.card) := by simp
    _ ≤ (width ^ 2) ^ petals.card *
        r ^ (n - petals.card) := by
      gcongr
      exact card_profile_le petals core bounded
    _ = pluckErrorCap n r petalCount width := by
      simp [pluckErrorCap, petalsCard]

/-- Colorings newly accepted by one concrete family transition. -/
def stepExceptions
    (r : Nat)
    (before after : Family n) : Finset (Coloring n r) :=
  Finset.univ.filter fun coloring =>
    Accepts after (coloringAssignment coloring) ∧
      ¬ Accepts before (coloringAssignment coloring)

@[simp] theorem mem_stepExceptions
    (coloring : Coloring n r)
    (before after : Family n) :
    coloring ∈ stepExceptions r before after ↔
      Accepts after (coloringAssignment coloring) ∧
        ¬ Accepts before (coloringAssignment coloring) := by
  simp [stepExceptions]

/-- Every fresh false positive of a pluck lies in the corresponding
sunflower bad-coloring set. -/
theorem stepExceptions_subset_sunflowerBad
    {petalCount : Nat}
    {before after : Family n}
    (step : Plucking.Step petalCount before after) :
    stepExceptions r before after ⊆
      sunflowerBad r step.petals step.core := by
  classical
  intro coloring exceptional
  rw [mem_stepExceptions] at exceptional
  rw [mem_sunflowerBad]
  constructor
  · rw [← contains_coloringAssignment_iff]
    obtain ⟨term, termPresent, termContains⟩ := exceptional.1
    rw [step.result, Finset.mem_insert] at termPresent
    rcases termPresent with equal | remaining
    · simpa [equal] using termContains
    · exfalso
      apply exceptional.2
      exact ⟨term, (Finset.mem_sdiff.mp remaining).1, termContains⟩
  · intro petal petalPresent injective
    apply exceptional.2
    refine ⟨petal, step.petals_subset petalPresent, ?_⟩
    rw [contains_coloringAssignment_iff]
    exact injective

/-- One bounded pluck introduces at most `pluckErrorCap` negative errors. -/
theorem card_stepExceptions_le
    {petalCount : Nat}
    {before after : Family n}
    (step : Plucking.Step petalCount before after)
    (bounded : Plucking.Bounded width before) :
    (stepExceptions r before after).card ≤
      pluckErrorCap n r petalCount width := by
  apply (Finset.card_le_card
    (stepExceptions_subset_sunflowerBad step)).trans
  exact card_sunflowerBad_le r petalCount width step.petals step.core
    step.petals_card step.sunflower
    (fun petal present => bounded petal (step.petals_subset present))

/-- Fresh errors across a composite transition lie in the union of the fresh
errors of its two pieces. -/
theorem stepExceptions_trans_subset
    (r : Nat)
    (before middle after : Family n) :
    stepExceptions r before after ⊆
      stepExceptions r before middle ∪
        stepExceptions r middle after := by
  intro coloring exceptional
  rw [mem_stepExceptions] at exceptional
  rw [Finset.mem_union]
  by_cases middleAccepted : Accepts middle (coloringAssignment coloring)
  · left
    rw [mem_stepExceptions]
    exact ⟨middleAccepted, exceptional.2⟩
  · right
    rw [mem_stepExceptions]
    exact ⟨exceptional.1, middleAccepted⟩

/-- A bounded reduction has at most one pluck cap per step.  The exception set
is defined extensionally, avoiding any elimination of proof-relevant
reductions into data. -/
theorem card_reductionExceptions_le
    (r width : Nat)
    {steps : Nat}
    {before after : Family n}
    (reduction : Plucking.Reduction petalCount steps before after)
    (two_le_petals : 2 ≤ petalCount)
    (bounded : Plucking.Bounded width before) :
    (stepExceptions r before after).card ≤
      steps * pluckErrorCap n r petalCount width := by
  induction reduction with
  | refl => simp [stepExceptions]
  | @step before middle after steps first rest inductionHypothesis =>
      calc
        (stepExceptions r before after).card ≤
            (stepExceptions r before middle ∪
              stepExceptions r middle after).card :=
          Finset.card_le_card
            (stepExceptions_trans_subset r before middle after)
        _ ≤
            (stepExceptions r before middle).card +
              (stepExceptions r middle after).card := Finset.card_union_le _ _
        _ ≤ pluckErrorCap n r petalCount width +
              steps * pluckErrorCap n r petalCount width :=
          Nat.add_le_add
            (card_stepExceptions_le first bounded)
            (inductionHypothesis (first.bounded two_le_petals bounded))
        _ = (steps + 1) * pluckErrorCap n r petalCount width := by
          simp [Nat.add_mul, Nat.add_comm]

/-- Negative exceptions accumulated by the chosen normalizer. -/
def normalizeExceptions
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (r : Nat)
    (family : Family n) : Finset (Coloring n r) :=
  stepExceptions r family
    (Plucking.normalize petalCount two_le_petals family)

/-- Normalization is negatively sound away from its recorded exceptions. -/
theorem acceptance_of_normalize_away
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (r : Nat)
    (family : Family n)
    (coloring : Coloring n r)
    (fresh : coloring ∉
      normalizeExceptions petalCount two_le_petals r family)
    (accepted : Accepts
      (Plucking.normalize petalCount two_le_petals family)
      (coloringAssignment coloring)) :
    Accepts family (coloringAssignment coloring) := by
  by_contra rejected
  apply fresh
  rw [normalizeExceptions, mem_stepExceptions]
  exact ⟨accepted, rejected⟩

/-- A bounded family pays at most one pluck cap per initial term. -/
theorem card_normalizeExceptions_le
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (r width : Nat)
    (family : Family n)
    (bounded : Plucking.Bounded width family) :
    (normalizeExceptions petalCount two_le_petals r family).card ≤
      family.card * pluckErrorCap n r petalCount width := by
  apply (card_reductionExceptions_le r width
    (Plucking.reduction_normalize petalCount two_le_petals family)
    two_le_petals bounded).trans
  exact Nat.mul_le_mul_right _
    (Plucking.normalizeSteps_le_card petalCount two_le_petals family)

/-- The bounded raw family normalized by one gate. -/
def gateFamily
    (width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → NormalFamily n petalCount width) : Family n :=
  Approx.gateFamily width op fun input => (arguments input).family

private theorem card_rawOr_le
    (left right : Family n) :
    (rawOr left right).card ≤ left.card + right.card :=
  Finset.card_union_le _ _

private theorem card_rawAnd_le
    (left right : Family n) :
    (rawAnd left right).card ≤ left.card * right.card := by
  unfold rawAnd
  calc
    ((left ×ˢ right).image fun pair => joinTerms pair.1 pair.2).card ≤
        (left ×ˢ right).card := Finset.card_image_le
    _ = left.card * right.card := by simp

private theorem card_gateFamily_or_le
    (arguments : Fin 2 → NormalFamily n petalCount width) :
    (gateFamily width .or arguments).card ≤
      2 * Sunflower.bound petalCount width := by
  apply (Finset.card_filter_le _ _).trans
  apply (card_rawOr_le _ _).trans
  calc
    (arguments 0).family.card +
        (arguments 1).family.card ≤
        Sunflower.bound petalCount width +
          Sunflower.bound petalCount width :=
      Nat.add_le_add
        (arguments 0).card_le
        (arguments 1).card_le
    _ = 2 * Sunflower.bound petalCount width := by omega

private theorem card_gateFamily_and_le
    (arguments : Fin 2 → NormalFamily n petalCount width) :
    (gateFamily width .and arguments).card ≤
      (Sunflower.bound petalCount width) ^ 2 := by
  apply (Finset.card_filter_le _ _).trans
  apply (card_rawAnd_le _ _).trans
  simpa [pow_two] using Nat.mul_le_mul
    (arguments 0).card_le
    (arguments 1).card_le

/-- Per-operation negative error cost. -/
def operationCost
    (n r petalCount width : Nat) : OperationCost AndOr.signature
  | .or => 2 * Sunflower.bound petalCount width *
      pluckErrorCap n r petalCount width
  | .and => (Sunflower.bound petalCount width) ^ 2 *
      pluckErrorCap n r petalCount width

/-- Concrete negative exceptions are precisely the false positives introduced
while normalizing the gate's truncated raw family. -/
def exceptions
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (r width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → NormalFamily n petalCount width) :
    Finset (Coloring n r) :=
  normalizeExceptions petalCount two_le_petals r
    (gateFamily width op arguments)

theorem card_exceptions_le
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (r width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → NormalFamily n petalCount width) :
    (exceptions petalCount two_le_petals r width op arguments).card ≤
      operationCost n r petalCount width op := by
  apply (card_normalizeExceptions_le petalCount two_le_petals r width
    (gateFamily width op arguments)
    (Approx.gateFamily_bounded width op
      (fun input => (arguments input).family))).trans
  cases op with
  | or =>
      exact Nat.mul_le_mul_right _ (card_gateFamily_or_le arguments)
  | and =>
      exact Nat.mul_le_mul_right _ (card_gateFamily_and_le arguments)

/-- A normalized gate is negatively correct away from the colorings charged
to its plucking normalization. -/
theorem gate_correct
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (r width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → NormalFamily n petalCount width)
    (coloring : Coloring n r)
    (fresh : coloring ∉
      exceptions petalCount two_le_petals r width op arguments) :
    normalDecode
        (normalInterpretation petalCount two_le_petals width op arguments)
        (coloringAssignment coloring) ≤
      AndOr.boolInterpretation op (fun input =>
        normalDecode (arguments input) (coloringAssignment coloring)) := by
  rw [Bool.le_iff_imp]
  intro normalizedTrue
  rw [normalDecode_eq_true] at normalizedTrue
  have gateAccepted : Accepts (gateFamily width op arguments)
      (coloringAssignment coloring) := by
    apply acceptance_of_normalize_away petalCount two_le_petals r
      (gateFamily width op arguments) coloring fresh
    simpa [normalInterpretation, interpretation, gateFamily] using
      normalizedTrue
  cases op with
  | or =>
      obtain ⟨term, termPresent, termContains⟩ := gateAccepted
      have rawPresent : term ∈
          rawOr (arguments 0).family
            (arguments 1).family :=
        (Finset.mem_filter.mp termPresent).1
      have rawAccepted : Accepts
          (rawOr (arguments 0).family
            (arguments 1).family)
          (coloringAssignment coloring) :=
        ⟨term, rawPresent, termContains⟩
      rw [accepts_rawOr_iff] at rawAccepted
      rcases rawAccepted with leftAccepted | rightAccepted
      · have leftTrue : normalDecode (arguments 0)
            (coloringAssignment coloring) = true := by
          exact (normalDecode_eq_true (arguments 0)
            (coloringAssignment coloring)).2 leftAccepted
        change (normalDecode (arguments 0) (coloringAssignment coloring) ||
          normalDecode (arguments 1) (coloringAssignment coloring)) = true
        simp [leftTrue]
      · have rightTrue : normalDecode (arguments 1)
            (coloringAssignment coloring) = true := by
          exact (normalDecode_eq_true (arguments 1)
            (coloringAssignment coloring)).2 rightAccepted
        change (normalDecode (arguments 0) (coloringAssignment coloring) ||
          normalDecode (arguments 1) (coloringAssignment coloring)) = true
        simp [rightTrue]
  | and =>
      obtain ⟨term, termPresent, termContains⟩ := gateAccepted
      have rawPresent : term ∈
          rawAnd (arguments 0).family
            (arguments 1).family :=
        (Finset.mem_filter.mp termPresent).1
      have rawAccepted : Accepts
          (rawAnd (arguments 0).family
            (arguments 1).family)
          (coloringAssignment coloring) :=
        ⟨term, rawPresent, termContains⟩
      have both := accepts_left_right_of_accepts_rawAnd
        (coloringAssignment coloring) _ _ rawAccepted
      have leftTrue : normalDecode (arguments 0)
          (coloringAssignment coloring) = true := by
        exact (normalDecode_eq_true (arguments 0)
          (coloringAssignment coloring)).2 both.1
      have rightTrue : normalDecode (arguments 1)
          (coloringAssignment coloring) = true := by
        exact (normalDecode_eq_true (arguments 1)
          (coloringAssignment coloring)).2 both.2
      change (normalDecode (arguments 0) (coloringAssignment coloring) &&
        normalDecode (arguments 1) (coloringAssignment coloring)) = true
      simp [leftTrue, rightTrue]

/-- The complete negative-side local approximation scheme. -/
def scheme
    (n r petalCount width : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width) :
    Approximation.Scheme
      AndOr.boolInterpretation
      (normalInterpretation petalCount two_le_petals width)
      (fun (family : NormalFamily n petalCount width)
          (coloring : Coloring n r) =>
        normalDecode family (coloringAssignment coloring))
      (fun (coloring : Coloring n r) => coloringAssignment coloring)
      (normalInput petalCount width two_le_petals two_le_width) where
  relation := fun exact approximate => approximate ≤ exact
  relation_trans := fun first second => second.trans first
  interpretation_preserves := by
    intro op exactArguments approxArguments ordered
    exact Positive.boolInterpretation_mono op approxArguments exactArguments
      ordered
  errorCost := operationCost n r petalCount width
  exceptions := exceptions petalCount two_le_petals r width
  input_correct := by
    intro coloring input
    rw [normalDecode_input]
  gate_correct := by
    intro op arguments coloring fresh
    exact gate_correct petalCount two_le_petals r width op arguments
      coloring fresh
  exceptions_card_le := card_exceptions_le petalCount two_le_petals r width

/-- Colorings injective on a fixed vertex term. -/
def injectiveColorings
    (r : Nat)
    (vertices : Finset (Fin n)) : Finset (Coloring n r) :=
  Finset.univ.filter fun coloring => Set.InjOn coloring ↑vertices

/-- Colorings with a collision on a fixed vertex term. -/
def nonInjectiveColorings
    (r : Nat)
    (vertices : Finset (Fin n)) : Finset (Coloring n r) :=
  Finset.univ.filter fun coloring => ¬ Set.InjOn coloring ↑vertices

/-- A width-bounded term has at most `width² * colors^(n-1)` noninjective
colorings.  This is the one-petal specialization of the profile count. -/
theorem card_nonInjectiveColorings_le
    (r width : Nat)
    (vertices : Finset (Fin n))
    (bounded : vertices.card ≤ width) :
    (nonInjectiveColorings r vertices).card ≤
      width ^ 2 * r ^ (n - 1) := by
  classical
  let petals : Finset (Finset (Fin n)) := {vertices}
  have sunflower : Sunflower.IsSunflowerWithCore petals ∅ := by
    intro left leftPresent right rightPresent different
    simp only [petals, Finset.mem_singleton] at leftPresent rightPresent
    subst left
    subst right
    exact (different rfl).elim
  have badEq : nonInjectiveColorings r vertices =
      sunflowerBad r petals ∅ := by
    ext coloring
    simp [nonInjectiveColorings, sunflowerBad, petals]
  rw [badEq]
  simpa [pluckErrorCap, petals] using
    card_sunflowerBad_le r 1 width petals ∅ (by simp [petals])
      sunflower (by
        intro petal present
        simp only [petals, Finset.mem_singleton] at present
        subst petal
        exact bounded)

/-- Injective and noninjective colorings partition the full coloring space. -/
theorem card_injective_add_nonInjective
    (r : Nat)
    (vertices : Finset (Fin n)) :
    (injectiveColorings r vertices).card +
      (nonInjectiveColorings r vertices).card = r ^ n := by
  classical
  have partition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Coloring n r)))
    (fun coloring => Set.InjOn coloring ↑vertices)
  simpa [injectiveColorings, nonInjectiveColorings, Fintype.card_fun] using
    partition

/-- When the color set is at least twice the ordered-pair budget, at least
half of all colorings are injective on every bounded term. -/
theorem half_colorings_injective
    (nPositive : 0 < n)
    (r width : Nat)
    (colorsLarge : 2 * width ^ 2 ≤ r)
    (vertices : Finset (Fin n))
    (bounded : vertices.card ≤ width) :
    r ^ n ≤ 2 * (injectiveColorings r vertices).card := by
  have badBound := card_nonInjectiveColorings_le r width vertices bounded
  have twoBad : 2 * (nonInjectiveColorings r vertices).card ≤ r ^ n := by
    calc
      2 * (nonInjectiveColorings r vertices).card ≤
          2 * (width ^ 2 * r ^ (n - 1)) :=
        Nat.mul_le_mul_left 2 badBound
      _ = (2 * width ^ 2) * r ^ (n - 1) := by
        simp [Nat.mul_assoc]
      _ ≤ r * r ^ (n - 1) := Nat.mul_le_mul_right _ colorsLarge
      _ = r ^ ((n - 1) + 1) := (pow_succ' r (n - 1)).symm
      _ = r ^ n := by congr 1; omega
  have partition := card_injective_add_nonInjective r vertices
  omega

/-- Colorings accepted by a clique DNF family. -/
def acceptedColorings
    (r : Nat)
    (family : Family n) : Finset (Coloring n r) :=
  Finset.univ.filter fun coloring =>
    Accepts family (coloringAssignment coloring)

@[simp] theorem mem_acceptedColorings
    (coloring : Coloring n r)
    (family : Family n) :
    coloring ∈ acceptedColorings r family ↔
      Accepts family (coloringAssignment coloring) := by
  simp [acceptedColorings]

private theorem injectiveColorings_subset_acceptedColorings
    (r : Nat)
    (family : Family n)
    (vertices : Finset (Fin n))
    (present : vertices ∈ family) :
    injectiveColorings r vertices ⊆ acceptedColorings r family := by
  intro coloring injective
  rw [injectiveColorings, Finset.mem_filter] at injective
  rw [mem_acceptedColorings]
  refine ⟨vertices, present, ?_⟩
  rw [contains_coloringAssignment_iff]
  exact injective.2

/-- Every nonempty bounded clique DNF accepts at least half of all negative
colorings under the large-color hypothesis. -/
theorem half_colorings_accepted
    (nPositive : 0 < n)
    (r width : Nat)
    (colorsLarge : 2 * width ^ 2 ≤ r)
    (family : Family n)
    (bounded : Plucking.Bounded width family)
    (nonempty : family.Nonempty) :
    r ^ n ≤ 2 * (acceptedColorings r family).card := by
  obtain ⟨vertices, present⟩ := nonempty
  apply (half_colorings_injective nPositive r width colorsLarge vertices
    (bounded vertices present)).trans
  exact Nat.mul_le_mul_left 2 <|
    Finset.card_le_card
      (injectiveColorings_subset_acceptedColorings r family vertices present)

end

end Negative
end Clique
end Monotone
end Algebraic

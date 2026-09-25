/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Approximation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Positive errors in the monotone CLIQUE approximation

On a minimal positive `k`-clique graph, sunflower plucking is harmless.  The
only possible local error is an AND whose two accepted terms join to more than
`width` vertices and are therefore truncated.  Such an error forces the
positive clique to contain one fixed `(width + 1)`-set.  This file packages
that observation as a local approximation scheme and proves its exact finite
counting bound.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique
namespace Positive

noncomputable section

open Approx

/-- Positive `k`-cliques containing a prescribed vertex set. -/
def containingCliques
    (n k : Nat)
    (vertices : Finset (Fin n)) : Finset (CliqueSet n k) :=
  Finset.univ.filter fun clique => vertices ⊆ clique.1

@[simp] theorem mem_containingCliques
    (clique : CliqueSet n k)
    (vertices : Finset (Fin n)) :
    clique ∈ containingCliques n k vertices ↔ vertices ⊆ clique.1 := by
  simp [containingCliques]

/-- The subtype presentation of `CliqueSet` does not change the usual
binomial count of supersets. -/
theorem card_containingCliques
    (vertices : Finset (Fin n))
    (vertices_le_k : vertices.card ≤ k) :
    (containingCliques n k vertices).card =
      Nat.choose (n - vertices.card) (k - vertices.card) := by
  classical
  let base := (Finset.univ : Finset (Fin n)).powersetCard k
  let selected := base.filter fun clique => vertices ⊆ clique
  let embedding : ↥selected → CliqueSet n k :=
    fun clique => ⟨clique.1, (Finset.mem_filter.mp clique.2).1⟩
  have injective : Function.Injective embedding := by
    intro left right equal
    apply Subtype.ext
    exact congrArg (fun clique : CliqueSet n k => clique.1) equal
  have range : Finset.univ.filter (fun clique : CliqueSet n k =>
      vertices ⊆ clique.1) = Finset.univ.image embedding := by
    ext clique
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro contains
      let source : ↥selected := ⟨clique.1,
        Finset.mem_filter.mpr ⟨clique.2, contains⟩⟩
      exact ⟨source, Subtype.ext rfl⟩
    · rintro ⟨source, rfl⟩
      exact (Finset.mem_filter.mp source.2).2
  rw [containingCliques, range, Finset.card_image_of_injective _ injective,
    Finset.card_univ, Fintype.card_coe]
  change selected.card = _
  simpa [selected, base] using
    Finset.card_filter_powersetCard_subset vertices
      (Finset.univ : Finset (Fin n)) k (by simp) vertices_le_k

/-- If `vertices` is wider than the approximation width, the number of
positive cliques containing it is bounded by the standard binomial cap. -/
theorem card_containingCliques_of_wide
    (width_succ_le_k : width + 1 ≤ k)
    (vertices : Finset (Fin n))
    (wide : width < vertices.card) :
    (containingCliques n k vertices).card ≤
      Nat.choose (n - (width + 1)) (k - (width + 1)) := by
  classical
  obtain ⟨witness, witnessSubset, witnessCard⟩ :=
    Finset.exists_subset_card_eq (s := vertices) (n := width + 1) (by omega)
  have subset : containingCliques n k vertices ⊆
      containingCliques n k witness := by
    intro clique present
    rw [mem_containingCliques] at present ⊢
    exact witnessSubset.trans present
  calc
    (containingCliques n k vertices).card ≤
        (containingCliques n k witness).card := Finset.card_le_card subset
    _ = Nat.choose (n - (width + 1)) (k - (width + 1)) := by
      rw [card_containingCliques witness
        (by simpa [witnessCard] using width_succ_le_k), witnessCard]

/-- A wide pair contributes all positive cliques containing its joined term;
a narrow pair contributes no exceptions. -/
def pairExceptions
    (n k width : Nat)
    (pair : Finset (Fin n) × Finset (Fin n)) : Finset (CliqueSet n k) :=
  if width < (joinTerms pair.1 pair.2).card then
    containingCliques n k (joinTerms pair.1 pair.2)
  else ∅

/-- Fresh positive errors at an approximate AND gate. -/
def andExceptions
    (n k width : Nat)
    (left right : Family n) : Finset (CliqueSet n k) :=
  (left ×ˢ right).biUnion (pairExceptions n k width)

@[simp] theorem mem_pairExceptions
    (clique : CliqueSet n k)
    (pair : Finset (Fin n) × Finset (Fin n)) :
    clique ∈ pairExceptions n k width pair ↔
      width < (joinTerms pair.1 pair.2).card ∧
      joinTerms pair.1 pair.2 ⊆ clique.1 := by
  classical
  unfold pairExceptions
  split <;> simp_all

private theorem mem_andExceptions_of_pair
    (clique : CliqueSet n k)
    (left right : Family n)
    (leftTerm : Finset (Fin n))
    (leftPresent : leftTerm ∈ left)
    (rightTerm : Finset (Fin n))
    (rightPresent : rightTerm ∈ right)
    (wide : width < (joinTerms leftTerm rightTerm).card)
    (contained : joinTerms leftTerm rightTerm ⊆ clique.1) :
    clique ∈ andExceptions n k width left right := by
  classical
  rw [andExceptions, Finset.mem_biUnion]
  refine ⟨(leftTerm, rightTerm), Finset.mem_product.mpr
    ⟨leftPresent, rightPresent⟩, ?_⟩
  rw [mem_pairExceptions]
  exact ⟨wide, contained⟩

/-- One AND gate has at most one binomial cap per term pair. -/
theorem card_andExceptions_le
    (width_succ_le_k : width + 1 ≤ k)
    (left right : Family n) :
    (andExceptions n k width left right).card ≤
      left.card * right.card *
        Nat.choose (n - (width + 1)) (k - (width + 1)) := by
  classical
  let cap := Nat.choose (n - (width + 1)) (k - (width + 1))
  calc
    (andExceptions n k width left right).card ≤
        ∑ pair ∈ left ×ˢ right, (pairExceptions n k width pair).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _pair ∈ left ×ˢ right, cap := by
      apply Finset.sum_le_sum
      intro pair pairPresent
      unfold pairExceptions
      split
      · exact card_containingCliques_of_wide width_succ_le_k _ (by assumption)
      · simp
    _ = left.card * right.card * cap := by
      simp [cap]

/-- Uniform positive error budget for normalized families. -/
def errorCap (n k petalCount width : Nat) : Nat :=
  (Sunflower.bound petalCount width) ^ 2 *
    Nat.choose (n - (width + 1)) (k - (width + 1))

private theorem card_andExceptions_normal_le
    (width_succ_le_k : width + 1 ≤ k)
    (left right : NormalFamily n petalCount width) :
    (andExceptions n k width left.family right.family).card ≤
      errorCap n k petalCount width := by
  apply (card_andExceptions_le width_succ_le_k left.family right.family).trans
  unfold errorCap
  gcongr
  simpa [pow_two] using Nat.mul_le_mul left.card_le right.card_le

/-- Per-operation positive error cost.  OR gates introduce no truncation
error; an AND gate is charged the uniform pair bound. -/
def operationCost
    (n k petalCount width : Nat) : OperationCost AndOr.signature
  | .and => errorCap n k petalCount width
  | .or => 0

/-- Concrete positive exceptions for one normalized gate application. -/
def exceptions
    (n k width : Nat)
    (op : AndOr.Op)
    (arguments : Fin 2 → NormalFamily n petalCount width) :
    Finset (CliqueSet n k) :=
  match op with
  | .and => andExceptions n k width
      (arguments 0).family
      (arguments 1).family
  | .or => ∅

/-- Binary Boolean AND and OR preserve pointwise Boolean order. -/
theorem boolInterpretation_mono
    (op : AndOr.Op)
    (exactArguments approxArguments : Fin 2 → Bool)
    (ordered : ∀ input, exactArguments input ≤ approxArguments input) :
    AndOr.boolInterpretation op exactArguments ≤
      AndOr.boolInterpretation op approxArguments := by
  cases op with
  | and =>
      apply Bool.le_and
      · exact (Bool.and_le_left _ _).trans (ordered 0)
      · exact (Bool.and_le_right _ _).trans (ordered 1)
  | or =>
      apply Bool.or_le
      · exact (ordered 0).trans
          (Bool.left_le_or _ _)
      · exact (ordered 1).trans
          (Bool.right_le_or _ _)

/-- Normalized OR is positively correct on every minimal clique graph. -/
theorem or_gate_correct
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (width : Nat)
    (arguments : Fin 2 → NormalFamily n petalCount width)
    (clique : CliqueSet n k) :
    AndOr.boolInterpretation .or (fun input =>
        normalDecode (arguments input) (cliqueAssignment clique.1)) ≤
      normalDecode
        (normalInterpretation petalCount two_le_petals width .or arguments)
        (cliqueAssignment clique.1) := by
  rw [Bool.le_iff_imp]
  intro accepted
  have disjunction :
      normalDecode (arguments 0)
          (cliqueAssignment clique.1) = true ∨
      normalDecode (arguments 1)
          (cliqueAssignment clique.1) = true := by
    simpa [AndOr.boolInterpretation] using accepted
  rw [normalDecode_eq_true]
  change Accepts
    (Plucking.normalize petalCount two_le_petals
      (truncate width (rawOr
        (arguments 0).family
        (arguments 1).family)))
      (cliqueAssignment clique.1)
  apply Plucking.normalize_acceptance_mono
  rcases disjunction with leftAccepted | rightAccepted
  · rw [normalDecode_eq_true] at leftAccepted
    obtain ⟨term, present, contains⟩ := leftAccepted
    refine ⟨term, Finset.mem_filter.mpr ⟨?_,
      (arguments 0).bounded term present⟩, contains⟩
    exact Finset.mem_union_left _ present
  · rw [normalDecode_eq_true] at rightAccepted
    obtain ⟨term, present, contains⟩ := rightAccepted
    refine ⟨term, Finset.mem_filter.mpr ⟨?_,
      (arguments 1).bounded term present⟩, contains⟩
    exact Finset.mem_union_right _ present

/-- Away from `andExceptions`, normalized AND is positively correct. -/
theorem and_gate_correct
    (petalCount : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (width : Nat)
    (two_le_width : 2 ≤ width)
    (arguments : Fin 2 → NormalFamily n petalCount width)
    (clique : CliqueSet n k)
    (fresh : clique ∉ andExceptions n k width
      (arguments 0).family
      (arguments 1).family) :
    AndOr.boolInterpretation .and (fun input =>
        normalDecode (arguments input) (cliqueAssignment clique.1)) ≤
      normalDecode
        (normalInterpretation petalCount two_le_petals width .and arguments)
        (cliqueAssignment clique.1) := by
  rw [Bool.le_iff_imp]
  intro accepted
  have leftTrue : normalDecode (arguments 0)
      (cliqueAssignment clique.1) = true := by
    simpa [AndOr.boolInterpretation] using Bool.and_elim_left accepted
  have rightTrue : normalDecode (arguments 1)
      (cliqueAssignment clique.1) = true := by
    simpa [AndOr.boolInterpretation] using Bool.and_elim_right accepted
  rw [normalDecode_eq_true] at leftTrue rightTrue
  obtain ⟨leftTerm, leftPresent, leftContains⟩ := leftTrue
  obtain ⟨rightTerm, rightPresent, rightContains⟩ := rightTrue
  let joined := joinTerms leftTerm rightTerm
  have joinedContains : Contains (cliqueAssignment clique.1) joined :=
    contains_joinTerms_cliqueAssignment clique.1 leftTerm rightTerm
      leftContains rightContains
  have narrow : joined.card ≤ width := by
    by_contra notNarrow
    have wide : width < joined.card := Nat.lt_of_not_ge notNarrow
    have joinedSubset : joined ⊆ clique.1 :=
      subset_of_contains_cliqueAssignment (by omega) joinedContains
    apply fresh
    exact mem_andExceptions_of_pair clique
      (arguments 0).family
      (arguments 1).family
      leftTerm leftPresent rightTerm rightPresent wide joinedSubset
  rw [normalDecode_eq_true]
  change Accepts
    (Plucking.normalize petalCount two_le_petals
      (truncate width (rawAnd
        (arguments 0).family
        (arguments 1).family)))
      (cliqueAssignment clique.1)
  apply Plucking.normalize_acceptance_mono
  refine ⟨joined, Finset.mem_filter.mpr ⟨?_, narrow⟩, joinedContains⟩
  rw [rawAnd, Finset.mem_image]
  exact ⟨(leftTerm, rightTerm), Finset.mem_product.mpr
    ⟨leftPresent, rightPresent⟩, rfl⟩

/-- The complete positive-side local approximation scheme. -/
def scheme
    (n k petalCount width : Nat)
    (two_le_petals : 2 ≤ petalCount)
    (two_le_width : 2 ≤ width)
    (width_succ_le_k : width + 1 ≤ k) :
    Approximation.Scheme
      AndOr.boolInterpretation
      (normalInterpretation petalCount two_le_petals width)
      (fun (family : NormalFamily n petalCount width)
          (clique : CliqueSet n k) =>
        normalDecode family (cliqueAssignment clique.1))
      (fun (clique : CliqueSet n k) => cliqueAssignment clique.1)
      (normalInput petalCount width two_le_petals two_le_width) where
  relation := (· ≤ ·)
  relation_trans := le_trans
  interpretation_preserves := boolInterpretation_mono
  errorCost := operationCost n k petalCount width
  exceptions := exceptions n k width
  input_correct := by
    intro clique input
    rw [normalDecode_input]
  gate_correct := by
    intro op arguments clique fresh
    cases op with
    | and =>
        exact and_gate_correct petalCount two_le_petals width two_le_width
          arguments clique fresh
    | or =>
        exact or_gate_correct petalCount two_le_petals width arguments clique
  exceptions_card_le := by
    intro op arguments
    cases op with
    | and =>
        exact card_andExceptions_normal_le width_succ_le_k
          (arguments 0) (arguments 1)
    | or => simp [exceptions, operationCost]

end

end Positive
end Clique
end Monotone
end Algebraic

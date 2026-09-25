/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Semifilter
public import Complexitylib.Algebraic.Combinatorics.FiniteCover
public import Mathlib.Tactic.NormNum

/-!
# A logarithmic ceiling for canonical graph semi-filters

For a bipartite graph `G`, the canonical semi-filter at an edge `(u, v)` is
the upward closure of its complementary row and complementary column. Both
must be nonempty. A random pair consisting of a union of rows and a union of
columns violates this semi-filter with probability at least `1 / 16`.

Consequently, on `2 ^ n` vertices per side, `32 * n` pairs cover every
canonical semi-filter. This is an upper bound for this restricted witness
class, not for full Fusion cover complexity or circuit size. In particular,
canonical graph semi-filters cannot establish the super-logarithmic graph
cover bound needed for a superlinear Boolean circuit lower bound.

The definition of canonical semi-filters is from Section 4.2 of:

* B. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and
  Two-Dimensional Cover Problems* (2025), https://arxiv.org/abs/2503.14117.

The probabilistic upper bound below is proved here; no priority claim is made.
-/

@[expose] public section

namespace Algebraic.Fusion.Graph

open Finset

noncomputable section

variable {N : Nat}

/-- A graph construction problem with all rows and columns as generators. -/
abbrev problem (graph : Set (Fin N × Fin N)) : SetProblem (Fin N × Fin N) where
  inputCount := N + N
  inputs := Fin.addCases
    (fun row => {edge | edge.1 = row})
    (fun column => {edge | edge.2 = column})
  target := graph

/-- The part of a row outside the graph. -/
def outsideRow (graph : Set (Fin N × Fin N)) (row : Fin N) :
    Set (Problem.Outside (problem graph)) :=
  {edge | edge.val.1 = row}

/-- The part of a column outside the graph. -/
def outsideColumn (graph : Set (Fin N × Fin N)) (column : Fin N) :
    Set (Problem.Outside (problem graph)) :=
  {edge | edge.val.2 = column}

/-- Edges whose complementary row and column are both nonempty. -/
def CanonicalEdge (graph : Set (Fin N × Fin N)) :=
  {edge : Fin N × Fin N // edge ∈ graph ∧
    (∃ column, (edge.1, column) ∉ graph) ∧
    (∃ row, (row, edge.2) ∉ graph)}

instance (graph : Set (Fin N × Fin N)) : Fintype (CanonicalEdge graph) := by
  classical
  unfold CanonicalEdge
  infer_instance

/-- A canonical edge supplies a nonedge in its row. -/
def CanonicalEdge.rowWitness
    {graph : Set (Fin N × Fin N)} (edge : CanonicalEdge graph) : Fin N :=
  edge.property.2.1.choose

/-- A canonical edge supplies a nonedge in its column. -/
def CanonicalEdge.columnWitness
    {graph : Set (Fin N × Fin N)} (edge : CanonicalEdge graph) : Fin N :=
  edge.property.2.2.choose

/-- Upward closure of the complementary row and column of a graph edge. -/
def canonicalFilter
    (graph : Set (Fin N × Fin N)) (edge : CanonicalEdge graph) :
    Semifilter (Problem.Outside (problem graph)) where
  carrier := {set | outsideRow graph edge.val.1 ⊆ set ∨
    outsideColumn graph edge.val.2 ⊆ set}
  nonempty := ⟨Set.univ, Or.inl (Set.subset_univ _)⟩
  upward := by
    intro lower upper present inclusion
    exact present.elim (fun h => Or.inl (h.trans inclusion))
      (fun h => Or.inr (h.trans inclusion))
  empty_not_mem := by
    rintro (rowEmpty | columnEmpty)
    · exact rowEmpty (show
        (⟨(edge.val.1, edge.rowWitness), edge.property.2.1.choose_spec⟩ :
          Problem.Outside (problem graph)) ∈ outsideRow graph edge.val.1
        from rfl)
    · exact columnEmpty (show
        (⟨(edge.columnWitness, edge.val.2), edge.property.2.2.choose_spec⟩ :
          Problem.Outside (problem graph)) ∈ outsideColumn graph edge.val.2
        from rfl)

/-- The canonical semi-filter is above the edge that defines it. -/
theorem canonicalFilter_above
    (graph : Set (Fin N × Fin N)) (edge : CanonicalEdge graph) :
    (canonicalFilter graph edge).Above (problem := problem graph) edge.val := by
  intro input
  refine Fin.addCases (fun row => ?_) (fun column => ?_) input
  · intro present
    simp only [Fin.addCases_left, Set.mem_ofPred_eq] at present
    left
    intro outside inRow
    change outside.val ∈ (problem graph).inputs (Fin.castAdd N row)
    simp only [problem, Fin.addCases_left, Set.mem_ofPred_eq]
    exact inRow.trans present
  · intro present
    simp only [Fin.addCases_right, Set.mem_ofPred_eq] at present
    right
    intro outside inColumn
    change outside.val ∈ (problem graph).inputs (Fin.natAdd N column)
    simp only [problem, Fin.addCases_right, Set.mem_ofPred_eq]
    exact inColumn.trans present

/-- Restrict admissible witnesses to canonical graph semi-filters. -/
def canonicalClass (graph : Set (Fin N × Fin N)) :
    SemifilterClass (problem graph) :=
  fun filter => ∃ edge : CanonicalEdge graph, filter = canonicalFilter graph edge

/-- Independently choose a set of row labels and a set of column labels. -/
abbrev Coloring (N : Nat) := (Fin N → Bool) × (Fin N → Bool)

/-- The fusion pair associated with a row/column coloring. -/
def colorPair (graph : Set (Fin N × Fin N)) (color : Coloring N) :
    Pair (problem graph) :=
  ({edge | color.1 edge.val.1 = true},
    {edge | color.2 edge.val.2 = true})

/-- Four prescribed color bits suffice to violate a canonical semi-filter. -/
def hits (graph : Set (Fin N × Fin N))
    (color : Coloring N) (edge : CanonicalEdge graph) : Prop :=
  color.1 edge.val.1 = true ∧ color.1 edge.columnWitness = false ∧
    color.2 edge.val.2 = true ∧ color.2 edge.rowWitness = false

instance (graph : Set (Fin N × Fin N)) : DecidableRel (hits graph) := by
  intro color edge
  unfold hits
  infer_instance

/-- A hit makes both members accepted but their intersection rejected. -/
theorem not_preservesPair_of_hits
    (graph : Set (Fin N × Fin N))
    (color : Coloring N) (edge : CanonicalEdge graph)
    (hit : hits graph color edge) :
    ¬ (canonicalFilter graph edge).PreservesPair (colorPair graph color) := by
  rcases hit with ⟨rowTrue, rowFalse, columnTrue, columnFalse⟩
  intro preserves
  have rowAccepted : (colorPair graph color).1 ∈ canonicalFilter graph edge := by
    left
    intro outside inRow
    change color.1 outside.val.1 = true
    rw [show outside.val.1 = edge.val.1 from inRow]
    exact rowTrue
  have columnAccepted : (colorPair graph color).2 ∈ canonicalFilter graph edge := by
    right
    intro outside inColumn
    change color.2 outside.val.2 = true
    rw [show outside.val.2 = edge.val.2 from inColumn]
    exact columnTrue
  rcases preserves rowAccepted columnAccepted with rowSubset | columnSubset
  · have included := rowSubset (show
      (⟨(edge.val.1, edge.rowWitness), edge.property.2.1.choose_spec⟩ :
        Problem.Outside (problem graph)) ∈ outsideRow graph edge.val.1 from rfl)
    have : color.2 edge.rowWitness = true := included.2
    simp [columnFalse] at this
  · have included := columnSubset (show
      (⟨(edge.columnWitness, edge.val.2), edge.property.2.2.choose_spec⟩ :
        Problem.Outside (problem graph)) ∈ outsideColumn graph edge.val.2 from rfl)
    have : color.1 edge.columnWitness = true := included.1
    simp [rowFalse] at this

private theorem witnesses_distinct
    {graph : Set (Fin N × Fin N)} (edge : CanonicalEdge graph) :
    edge.val.1 ≠ edge.columnWitness ∧ edge.val.2 ≠ edge.rowWitness := by
  constructor
  · intro equal
    have outside := edge.property.2.2.choose_spec
    change (edge.columnWitness, edge.val.2) ∉ graph at outside
    rw [← equal] at outside
    exact outside edge.property.1
  · intro equal
    have outside := edge.property.2.1.choose_spec
    change (edge.val.1, edge.rowWitness) ∉ graph at outside
    rw [← equal] at outside
    exact outside edge.property.1

private def forceHit
    {graph : Set (Fin N × Fin N)}
    (edge : CanonicalEdge graph) (color : Coloring N) : Coloring N :=
  (Function.update (Function.update color.1 edge.val.1 true)
      edge.columnWitness false,
    Function.update (Function.update color.2 edge.val.2 true)
      edge.rowWitness false)

private theorem forceHit_hits
    {graph : Set (Fin N × Fin N)}
    (edge : CanonicalEdge graph) (color : Coloring N) :
    hits graph (forceHit edge color) edge := by
  obtain ⟨rowsDifferent, columnsDifferent⟩ := witnesses_distinct edge
  simp [hits, forceHit, rowsDifferent, columnsDifferent]

private def remember
    {graph : Set (Fin N × Fin N)}
    (edge : CanonicalEdge graph) (color : Coloring N) :
    (Bool × Bool) × (Bool × Bool) :=
  ((color.1 edge.val.1, color.1 edge.columnWitness),
    (color.2 edge.val.2, color.2 edge.rowWitness))

private theorem forceHit_remember_injective
    {graph : Set (Fin N × Fin N)} (edge : CanonicalEdge graph) :
    Function.Injective (fun color : Coloring N =>
      (forceHit edge color, remember edge color)) := by
  intro left right equal
  have forced := congrArg Prod.fst equal
  have saved := congrArg Prod.snd equal
  apply Prod.ext
  · funext row
    by_cases atEdge : row = edge.val.1
    · simpa [remember, atEdge] using congrArg (fun saved => saved.1.1) saved
    by_cases atWitness : row = edge.columnWitness
    · simpa [remember, atWitness] using congrArg (fun saved => saved.1.2) saved
    have := congrArg (fun colors => colors.1 row) forced
    simpa [forceHit, atEdge, atWitness] using this
  · funext column
    by_cases atEdge : column = edge.val.2
    · simpa [remember, atEdge] using congrArg (fun saved => saved.2.1) saved
    by_cases atWitness : column = edge.rowWitness
    · simpa [remember, atWitness] using congrArg (fun saved => saved.2.2) saved
    have := congrArg (fun colors => colors.2 column) forced
    simpa [forceHit, atEdge, atWitness] using this

/-- At most fifteen sixteenths of all row/column colorings miss a fixed edge. -/
theorem sixteen_mul_misses_le
    (graph : Set (Fin N × Fin N)) (edge : CanonicalEdge graph) :
    16 * Fintype.card {color : Coloring N // ¬ hits graph color edge} ≤
      15 * Fintype.card (Coloring N) := by
  classical
  let encode (color : Coloring N) :
      {color : Coloring N // hits graph color edge} ×
        ((Bool × Bool) × (Bool × Bool)) :=
    (⟨forceHit edge color, forceHit_hits edge color⟩, remember edge color)
  have injective : Function.Injective encode := by
    intro left right equal
    apply forceHit_remember_injective edge
    exact congrArg (fun result => (result.1.val, result.2)) equal
  have enough := Fintype.card_le_of_injective encode injective
  have enough' : Fintype.card (Coloring N) ≤
      16 * Fintype.card {color : Coloring N // hits graph color edge} := by
    simpa only [Fintype.card_prod, Fintype.card_bool,
      show 2 * 2 * (2 * 2) = 16 from rfl, Nat.mul_comm] using enough
  have partition := Fintype.card_subtype_compl (hits graph · edge)
  omega

/-- `32 * n` independent samples suffice for at most `(2 ^ n)^2` obligations. -/
theorem sampling_bound {n : Nat} (positive : 0 < n) :
    (2 ^ n) ^ 2 * 15 ^ (32 * n) < 16 ^ (32 * n) := by
  have base : 4 * 15 ^ 32 < (16 : Nat) ^ 32 := by norm_num
  have powered := Nat.pow_lt_pow_left base (Nat.ne_of_gt positive)
  have fourPower : (2 ^ n) ^ 2 = (4 : Nat) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    rfl
  simpa only [mul_pow, ← pow_mul, fourPower] using powered

/-- Every graph has a logarithmic cover of all its canonical semi-filters. -/
theorem exists_canonical_cover
    {n : Nat} (positive : 0 < n)
    (graph : Set (Fin (2 ^ n) × Fin (2 ^ n))) :
    ∃ cover : PairCover (problem graph) (canonicalClass graph),
      cover.cost = 32 * n := by
  classical
  have edgeCount : Fintype.card (CanonicalEdge graph) ≤ (2 ^ n) ^ 2 := by
    simpa [CanonicalEdge, pow_two] using Fintype.card_subtype_le
      (fun edge : Fin (2 ^ n) × Fin (2 ^ n) => edge ∈ graph ∧
        (∃ column, (edge.1, column) ∉ graph) ∧
        (∃ row, (row, edge.2) ∉ graph))
  obtain ⟨tests, covers⟩ :=
    Combinatorics.FiniteCover.exists_cover_of_scaled_card_lt
      (hits graph) 15 16 (32 * n) (sixteen_mul_misses_le graph)
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ edgeCount) (sampling_bound positive))
  let cover : PairCover (problem graph) (canonicalClass graph) :=
    { pairs := List.ofFn fun i => colorPair graph (tests i)
      isCover := by
        intro point present filter admissible above preserves
        obtain ⟨edge, rfl⟩ := admissible
        obtain ⟨i, hit⟩ := covers edge
        exact not_preservesPair_of_hits graph (tests i) edge hit
          (preserves _ (List.mem_ofFn.mpr ⟨i, rfl⟩)) }
  exact ⟨cover, by simp [cover, PairCover.cost]⟩

/-- Restricted canonical cover complexity is at most linear in the binary
label length, uniformly over the graph. This does not bound full cover complexity. -/
theorem canonical_coverComplexity_le
    {n : Nat} (positive : 0 < n)
    (graph : Set (Fin (2 ^ n) × Fin (2 ^ n))) :
    pairCoverComplexity (problem graph) (canonicalClass graph) ≤
      (32 * n : Nat) := by
  obtain ⟨cover, cost⟩ := exists_canonical_cover positive graph
  simpa [cost] using pairCoverComplexity_le
    (problem graph) (canonicalClass graph) cover

end

end Algebraic.Fusion.Graph

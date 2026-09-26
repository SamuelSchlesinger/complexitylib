/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation
public import Complexitylib.DescriptiveComplexity.Problems.Coloring

/-!
# Graph constructions by tagged interpretations

The two-copy construction of Senellart and Gnatenko (2026), Section 3.2,
<https://arxiv.org/abs/2609.18261>, creates a left and a right copy of every
vertex and copies edges only from left to right. We verify the relation semantics,
exact size, and a Boolean bipartition for every input graph. This is an
interpretation example, not a hardness reduction for bipartiteness.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.GraphQuery

open TaggedFOInterpretation in
/-- Two copies of the source graph, with edges only from the left copy to the right. -/
def doubleCover : TaggedFOInterpretation Vocabulary.graph Vocabulary.graph 2 1 where
  tags_pos := by decide
  dim_pos := by decide
  relFormula := fun _ tags =>
    if tags 0 = 0 ∧ tags 1 = 1 then
      .relApp 0 (fun j => .var (finProdFinEquiv (j, 0)))
    else .falsum
  constTag := Fin.elim0
  constCoord := Fin.elim0

/-- The double cover has exactly twice as many vertices as its source. -/
theorem doubleCover_card (A : FinStruct Vocabulary.graph) :
    (doubleCover.apply A).card = 2 * A.card := by
  simp

/-- Double-cover edges are precisely source edges with left-to-right tags. -/
theorem doubleCover_rel (A : FinStruct Vocabulary.graph)
    (args : Fin 2 → Fin (2 * A.card ^ 1)) :
    (doubleCover.apply A).rel 0 args ↔
      (TaggedFOInterpretation.elementEquiv A.card 2 1 (args 0)).1 = 0 ∧
      (TaggedFOInterpretation.elementEquiv A.card 2 1 (args 1)).1 = 1 ∧
      A.rel 0 (fun j => (TaggedFOInterpretation.elementEquiv A.card 2 1 (args j)).2 0) := by
  simp only [doubleCover]
  split <;> simp_all [Formula.Sat, Term.eval, TaggedFOInterpretation.relationEnv,
    Formula.falsum_sat]

/-- The tag supplies a bipartition of the double cover, regardless of the source graph. -/
theorem doubleCover_bipartite (A : FinStruct Vocabulary.graph) :
    Bipartite (doubleCover.apply A) := by
  refine ⟨fun x => decide ((TaggedFOInterpretation.elementEquiv A.card 2 1 x).1 = 0), ?_⟩
  intro x y hxy
  have h := (doubleCover_rel A _).mp hxy
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h
  simp [h.1, h.2.1]

end Complexity.DescriptiveComplexity.GraphQuery

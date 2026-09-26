/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Definable
public import Complexitylib.DescriptiveComplexity.SecondOrder.ModelChecking

/-!
# Bipartiteness as an existential second-order query

The graph vocabulary describes arbitrary directed graphs, including loops. A
bipartition assigns a Boolean color to each vertex, with different colors at the
ends of every directed edge. Symmetry is not required; a loop prevents a coloring.

The sentence `∃X ∀x ∀y (E(x,y) → (X(x) ↔ ¬X(y)))` defines this query.
This is the example in Senellart and Gnatenko (2026), Section 2.1,
<https://arxiv.org/abs/2609.18261>. We prove agreement with an ordinary Boolean
coloring, rather than defining the query as satisfaction of its witness.
No NP membership or hardness statement is claimed here.
`checkBipartition` executes the matrix on a supplied Boolean coloring and is
proved to accept exactly the colorings separating every directed edge.
The general binary certificate checker agrees with it when the certificate
lists the vertex colors, one bit per vertex.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

namespace GraphQuery

/-- There is an edge from `x` to `y` in a graph structure. -/
def Edge (A : FinStruct Vocabulary.graph) (x y : Fin A.card) : Prop :=
  A.rel 0 (fun i => if i = 0 then x else y)

/-- A Boolean coloring separates the endpoints of every directed edge. -/
def Bipartite : BooleanQuery Vocabulary.graph := fun A =>
  ∃ color : Fin A.card → Bool, ∀ x y, Edge A x y → color x ≠ color y

/-- A graph without edges has a constant Boolean coloring. -/
theorem bipartite_of_no_edges {A : FinStruct Vocabulary.graph}
    (h : ∀ x y, ¬ Edge A x y) : Bipartite A :=
  ⟨fun _ => false, fun x y hxy => (h x y hxy).elim⟩

/-- A self-loop rules out a Boolean bipartition. -/
theorem not_bipartite_of_loop {A : FinStruct Vocabulary.graph} {x : Fin A.card}
    (h : Edge A x x) : ¬ Bipartite A := by
  rintro ⟨color, hcolor⟩
  exact hcolor x x h rfl

/-- The open FO matrix: adjacent vertices disagree on the unary relation variable. -/
def bipartiteMatrix : SOFormula Vocabulary.graph [1] 2 :=
  .disj (.neg (.relApp 0 (fun i => .var i)))
    (.conj
      (.disj (.neg (.soRelApp 0 (fun _ => .var 0)))
        (.neg (.soRelApp 0 (fun _ => .var 1))))
      (.disj (.soRelApp 0 (fun _ => .var 0)) (.soRelApp 0 (fun _ => .var 1))))

/-- Guess one unary relation, then check every pair of vertices. -/
def bipartiteSentence : SOSentence Vocabulary.graph :=
  .soExist 1 (.all (.all bipartiteMatrix))

/-- This witness has one existential SO quantifier and an FO matrix. -/
theorem bipartiteSentence_isExistSO : bipartiteSentence.IsExistSO := by
  simp [bipartiteSentence, bipartiteMatrix, SOFormula.IsExistSO, SOFormula.IsFOMatrix]

/-- Semantics of the open matrix, independent of the choice of variable environment. -/
theorem bipartiteMatrix_sat (A : FinStruct Vocabulary.graph) (σ : Env A.card 2)
    (S : (Fin 1 → Fin A.card) → Prop) :
    bipartiteMatrix.Sat A σ (rCons S (emptyREnv A.card)) ↔
      (Edge A (σ 0) (σ 1) → (S (fun _ => σ 0) ↔ ¬ S (fun _ => σ 1))) := by
  classical
  simp only [bipartiteMatrix, SOFormula.Sat, Term.eval, rCons]
  have hσ : (fun i : Fin 2 => if i = 0 then σ 0 else σ 1) = σ := by
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp
  simp only [Edge, hσ]
  change (¬ A.rel 0 σ) ∨ ((¬ S (fun _ => σ 0) ∨ ¬ S (fun _ => σ 1)) ∧
    (S (fun _ => σ 0) ∨ S (fun _ => σ 1))) ↔ _
  by_cases h0 : S (fun _ => σ 0) <;> by_cases h1 : S (fun _ => σ 1) <;> simp [h0, h1]

/-- The logical witness defines exactly the Boolean-coloring query. -/
theorem bipartiteSentence_models (A : FinStruct Vocabulary.graph) :
    SOSentence.Models A bipartiteSentence ↔ Bipartite A := by
  classical
  simp only [SOSentence.Models, bipartiteSentence, SOFormula.Sat, bipartiteMatrix_sat,
    Bipartite]
  change (∃ S : (Fin 1 → Fin A.card) → Prop,
    ∀ y x, Edge A x y → (S (fun _ => x) ↔ ¬ S (fun _ => y))) ↔ _
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨fun x => decide (S (fun _ => x)), ?_⟩
    intro x y hxy
    have h := hS y x hxy
    by_cases hx : S (fun _ => x) <;> by_cases hy : S (fun _ => y) <;> simp_all
  · rintro ⟨color, hcolor⟩
    refine ⟨fun args => color (args 0) = true, ?_⟩
    intro y x hxy
    have h := hcolor x y hxy
    cases hx : color x <;> cases hy : color y <;> simp_all

/-- Bipartiteness is existential second-order definable. -/
theorem bipartite_existSODefinable : ExistSODefinable Bipartite :=
  ⟨bipartiteSentence, bipartiteSentence_isExistSO, fun A => (bipartiteSentence_models A).symm⟩

/-- Check a supplied Boolean bipartition by evaluating the sentence's FO matrix. -/
def checkBipartition (A : DecFinStruct Vocabulary.graph) (color : Fin A.card → Bool) : Bool :=
  (SOFormula.all (.all bipartiteMatrix)).evalMatrixB A bipartiteSentence_isExistSO
    (emptyEnv A.card) ((DecREnv.empty A.card).cons (fun args => color (args 0)))

/-- The executable witness checker accepts exactly the proper Boolean colorings. -/
theorem checkBipartition_eq_true (A : DecFinStruct Vocabulary.graph)
    (color : Fin A.card → Bool) :
    checkBipartition A color = true ↔
      ∀ x y, Edge A.toFinStruct x y → color x ≠ color y := by
  unfold checkBipartition
  refine (SOFormula.evalMatrixB_eq_sat A (.all (.all bipartiteMatrix)) _ _ _).trans ?_
  simp only [DecREnv.toREnv_cons, DecREnv.toREnv_empty, SOFormula.Sat]
  refine (forall_congr' fun y => forall_congr' fun x =>
    bipartiteMatrix_sat A.toFinStruct (envCons x (envCons y (emptyEnv A.card)))
      (fun args => color (args 0) = true)).trans ?_
  change (∀ y x, Edge A.toFinStruct x y → (color x = true ↔ ¬ color y = true)) ↔ _
  have hb (a b : Bool) : (a = true ↔ ¬ b = true) ↔ a ≠ b := by
    cases a <;> cases b <;> decide
  simp only [hb]
  exact forall_comm

/-- A graph is bipartite exactly when the executable checker accepts some coloring. -/
theorem exists_checkBipartition_iff (A : DecFinStruct Vocabulary.graph) :
    (∃ color, checkBipartition A color = true) ↔ Bipartite A.toFinStruct :=
  exists_congr fun color => checkBipartition_eq_true A color

/-- The binary certificate for bipartiteness is exactly one color bit per vertex. -/
theorem checkEncoded_bipartite_colors (A : DecFinStruct Vocabulary.graph)
    (color : Fin A.card → Bool) :
    bipartiteSentence.checkEncoded bipartiteSentence_isExistSO
      (encodeStruct A) (List.ofFn color) = checkBipartition A color := by
  rw [SOSentence.checkEncoded_encodeStruct]
  have he := SOFormula.checkCertificate_soExist_append A (.all (.all bipartiteMatrix))
    bipartiteSentence_isExistSO (emptyEnv A.card) (DecREnv.empty A.card)
    ((DecREnv.empty A.card).cons (fun args => color (args 0))) []
  simp only [DecREnv.encode_unary, List.append_nil] at he
  exact he

/-- The binary certificate checker characterizes the ordinary bipartite-graph language. -/
theorem exists_checkEncoded_bipartite_iff (input : List Bool) :
    (∃ certificate, bipartiteSentence.checkEncoded bipartiteSentence_isExistSO
      input certificate = true) ↔ input ∈ queryLanguage Bipartite := by
  rw [SOSentence.exists_checkEncoded_iff]
  simp only [mem_queryLanguage_iff_decodeStruct, bipartiteSentence_models]

/-- Relabeling vertices preserves bipartiteness. -/
theorem bipartite_orderIndependent : Bipartite.IsOrderIndependent :=
  bipartite_existSODefinable.orderIndependent

/-- Every query FO-reducible to bipartiteness has an existential SO witness. -/
theorem existSODefinable_of_reduces_bipartite {V : Vocabulary} {Q : BooleanQuery V}
    (h : FOReduces Q Bipartite) : ExistSODefinable Q :=
  bipartite_existSODefinable.of_reduces h

end GraphQuery

end Complexity.DescriptiveComplexity

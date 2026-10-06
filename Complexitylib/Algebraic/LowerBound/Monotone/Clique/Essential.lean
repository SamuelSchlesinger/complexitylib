/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Basic
public import Complexitylib.Algebraic.LowerBound.FanIn.Size

/-!
# Constant clique sizes and essential edges

Two elementary facts about binary, constant-free AND/OR circuits and the
`CLIQUE` function of `Basic.lean`.  They give lower bounds for small clique
sizes, where the approximation method has nothing to say.

* Such a circuit outputs `false` on the empty graph, while `0`-CLIQUE and
  `1`-CLIQUE accept it.  So no such circuit computes either
  (`not_computes_of_le_one`).
* For `2 ≤ k ≤ n`, every edge variable is essential to `k`-CLIQUE: removing
  one edge from the minimal graph of a `k`-set through it destroys every
  `k`-clique.  The fan-in bound then gives `edgeCount n ≤ 1 + size`
  (`edgeCount_le_succ_size`), and `(n / 2)^2 ≤ edgeCount n`.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique

noncomputable section

/-- Every gate of a binary AND/OR program is `false` on the all-false input. -/
theorem program_eval_allFalse
    {inputCount gateCount : Nat}
    (program : Program AndOr.signature inputCount gateCount)
    (gate : Fin gateCount) :
    program.eval AndOr.boolInterpretation (fun _ => false) gate = false := by
  induction program with
  | empty => exact gate.elim0
  | gate program line inductionHypothesis =>
      induction gate using Fin.lastCases with
      | last =>
          rw [Program.eval_gate_last]
          obtain ⟨op, wires⟩ := line
          have wireFalse : ∀ argument, Wire.elim (fun _ => false)
              (program.eval AndOr.boolInterpretation (fun _ => false))
              (wires argument) = false := by
            intro argument
            cases wires argument with
            | input _ => rfl
            | gate earlier => exact inductionHypothesis earlier
          cases op <;>
            simp [Line.eval, AndOr.boolInterpretation, wireFalse]
      | cast gate =>
          rw [Program.eval_gate_castSucc]
          exact inductionHypothesis gate

/-- A binary AND/OR circuit outputs `false` on the all-false input. -/
theorem circuit_eval_allFalse
    {inputCount : Nat}
    (circuit : Circuit AndOr.signature inputCount 1) :
    circuit.eval AndOr.boolInterpretation (fun _ => false) 0 = false := by
  change circuit.program.trace AndOr.boolInterpretation (fun _ => false)
    (circuit.outputs 0) = false
  cases circuit.outputs 0 with
  | input _ => rfl
  | gate gate => exact program_eval_allFalse circuit.program gate

/-- With at most one vertex, a clique has no edges, so the empty graph
contains a `k`-clique whenever `k ≤ 1` and `k ≤ n`. -/
theorem function_allFalse
    {n k : Nat}
    (k_le_one : k ≤ 1)
    (k_le_n : k ≤ n) :
    function n k (fun _ => false) = true := by
  rw [function, decide_eq_true_eq]
  obtain ⟨vertices, present⟩ :=
    (Finset.powersetCard_nonempty (s := (Finset.univ : Finset (Fin n)))).2
      (by simpa using k_le_n)
  refine ⟨⟨vertices, present⟩, ?_⟩
  intro edge inside
  exfalso
  have small : vertices.card ≤ 1 :=
    (Finset.mem_powersetCard.mp present).2 ▸ k_le_one
  have endpointsEqual := Finset.card_le_one.1 small _ inside.1 _ inside.2
  exact (ne_of_lt edge.2) endpointsEqual

/-- No binary, constant-free AND/OR circuit computes `k`-CLIQUE for `k ≤ 1`
(when `k ≤ n`): the empty graph is accepted but the circuit rejects it. -/
theorem not_computes_of_le_one
    {n k : Nat}
    (k_le_one : k ≤ 1)
    (k_le_n : k ≤ n)
    (circuit : Circuit AndOr.signature (edgeCount n) 1) :
    ¬ ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment := by
  intro computes
  have allFalse := computes (fun _ => false)
  rw [circuit_eval_allFalse, function_allFalse k_le_one k_le_n] at allFalse
  exact Bool.false_ne_true allFalse

/-- For `2 ≤ k ≤ n`, every edge variable is essential to `k`-CLIQUE. -/
theorem essentialAt_function
    {n k : Nat}
    (two_le : 2 ≤ k)
    (k_le_n : k ≤ n)
    (input : Fin (edgeCount n)) :
    EssentialAt (fun assignment (_ : Fin 1) => function n k assignment) input := by
  classical
  let edge := (edgeEquiv n).symm input
  have endpointsSmall : ({edge.1.1, edge.1.2} : Finset (Fin n)).card ≤ k :=
    (Finset.card_le_two).trans two_le
  obtain ⟨vertices, endpoints_subset, -, card⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ _) endpointsSmall
      (by simpa using k_le_n)
  have verticesPresent :
      vertices ∈ (Finset.univ : Finset (Fin n)).powersetCard k :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, card⟩
  let left := cliqueAssignment vertices
  let right := Function.update left input false
  refine ⟨left, right, ?_, ?_⟩
  · intro other different
    simp [right, Function.update_of_ne different]
  · intro equal
    have leftTrue : function n k left = true :=
      function_cliqueAssignment ⟨vertices, verticesPresent⟩
    have rightFalse : function n k right = false := by
      rw [function, decide_eq_false_iff_not]
      rintro ⟨test, contains⟩
      have testCard : test.1.card = k := (Finset.mem_powersetCard.mp test.2).2
      have containsLeft : Contains left test.1 := by
        intro other inside
        have present := contains other inside
        by_cases same : edgeEquiv n other = input
        · rw [same] at present
          simp [right] at present
        · simpa [right, Function.update_of_ne same] using present
      have subset := subset_of_contains_cliqueAssignment (by omega) containsLeft
      have sameSet : test.1 = vertices :=
        Finset.eq_of_subset_of_card_le subset (by omega)
      have inside : edge.Inside test.1 := by
        rw [sameSet]
        exact ⟨endpoints_subset (by simp), endpoints_subset (by simp)⟩
      have present := contains edge inside
      simp [right, edge] at present
    have atOutput := congrFun equal 0
    simp only [leftTrue, rightFalse] at atOutput
    exact Bool.false_ne_true atOutput.symm

/-- Every binary AND/OR program has fan-in at most two. -/
theorem program_fanInAtMost_two
    {inputCount gateCount : Nat}
    (program : Program AndOr.signature inputCount gateCount) :
    program.FanInAtMost 2 := by
  induction program with
  | empty => trivial
  | gate program line inductionHypothesis =>
      exact ⟨inductionHypothesis, le_refl _⟩

/-- For `2 ≤ k ≤ n`, a binary AND/OR circuit computing `k`-CLIQUE reads every
edge variable, so it has at least `edgeCount n - 1` gates. -/
theorem edgeCount_le_succ_size
    {n k : Nat}
    (two_le : 2 ≤ k)
    (k_le_n : k ≤ n)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    edgeCount n ≤ 1 + circuit.size := by
  have computesWith : circuit.ComputesWith AndOr.boolInterpretation
      (fun assignment (_ : Fin 1) => function n k assignment) := by
    intro assignment
    funext output
    rw [Subsingleton.elim output 0]
    exact computes assignment
  have bound := circuit.essential_le_size computesWith
    (selected := Finset.univ)
    (fun input _ => essentialAt_function two_le k_le_n input)
    (program_fanInAtMost_two circuit.program)
  simpa using bound

/-- The edges between the first `n / 2` vertices and the next `n / 2`
vertices give `(n / 2)^2 ≤ edgeCount n`. -/
theorem sq_half_le_edgeCount (n : Nat) :
    (n / 2) ^ 2 ≤ edgeCount n := by
  let half := n / 2
  let embed : Fin half × Fin half → Edge n := fun pair =>
    ⟨(⟨pair.1.1, by omega⟩, ⟨half + pair.2.1, by omega⟩), by
      rw [Fin.lt_def]
      dsimp only
      omega⟩
  have injective : Function.Injective embed := by
    rintro ⟨first, second⟩ ⟨first', second'⟩ equal
    simp only [embed, Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq] at equal
    ext <;> simp only [Fin.val_inj] <;> omega
  simpa [pow_two, half] using Fintype.card_le_of_injective embed injective

end

end Clique
end Monotone
end Algebraic

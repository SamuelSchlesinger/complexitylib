/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Analysis.Frontier
public import Complexitylib.Algebraic.Basis.DeMorgan.ReadOnce
public import Complexitylib.Algebraic.Basis.DeMorgan.Complexity

/-!
# Tight binary-gate budgets force read-once semantics

This argument retains arbitrary sharing and free designated output wires.
Unfolding a selected wire increases the number of formula input occurrences
by at most the binary cost of that gate. Essential-input counting forces
every intermediate formula to remain read-once at the tight budget.
-/

@[expose] public section

namespace Algebraic.DeMorgan

private theorem arity_le_binaryCost (op : Op) : arity op ≤ binaryCost op + 1 := by
  cases op <;> decide

private theorem flatMap_length_le {α β : Type*} (items : List α) (replace : α → List β)
    (bounded : ∀ item ∈ items, (replace item).length ≤ 1) :
    (items.flatMap replace).length ≤ items.length := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    have first := bounded head (by simp)
    have rest := ih (fun item member => bounded item (by simp [member]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private theorem flatMap_length_le_one_exception {α β : Type*} [DecidableEq α]
    (items : List α) (once : items.Nodup) (replace : α → List β) (exception : α) (extra : Nat)
    (ordinary : ∀ item, item ≠ exception → (replace item).length ≤ 1)
    (exceptional : (replace exception).length ≤ extra + 1) :
    (items.flatMap replace).length ≤ items.length + extra := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨absent, tailOnce⟩ := List.nodup_cons.mp once
    by_cases same : head = exception
    · have rest := flatMap_length_le tail replace (by
        intro item member
        apply ordinary
        intro equal
        exact absent (by simpa [same, equal] using member))
      have first : (replace head).length ≤ extra + 1 := same ▸ exceptional
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
    · have first := ordinary head same
      have rest := ih tailOnce
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

private def lineExpression (line : Line signature n g) : Expression (n + g) :=
  match line with
  | ⟨.false, _⟩ => .constant false
  | ⟨.true, _⟩ => .constant true
  | ⟨.id, wires⟩ => .input (wires ⟨0, by decide⟩)
  | ⟨.not, wires⟩ => .not (.input (wires ⟨0, by decide⟩))
  | ⟨.and, wires⟩ => .and (.input (wires ⟨0, by decide⟩)) (.input (wires ⟨1, by decide⟩))
  | ⟨.or, wires⟩ => .or (.input (wires ⟨0, by decide⟩)) (.input (wires ⟨1, by decide⟩))

private theorem lineExpression_length (line : Line signature n g) :
    (lineExpression line).inputList.length ≤ binaryCost line.op + 1 := by
  obtain ⟨op, wires⟩ := line
  cases op <;> simp [lineExpression, Expression.inputList]

private theorem lineExpression_eval (program : Program signature n g) (line : Line signature n g)
    (input : Fin n → Bool) :
    (lineExpression line).eval (program.trace interpretation input) =
      line.eval interpretation input (program.eval interpretation input) := by
  obtain ⟨op, wires⟩ := line
  cases op <;> rfl

private def unrollLast (expression : Expression (n + (g + 1))) (line : Line signature n g) :
    Expression (n + g) :=
  expression.substitute (Fin.lastCases (lineExpression line) Expression.input)

private theorem unrollLast_eval (expression : Expression (n + (g + 1)))
    (program : Program signature n g) (line : Line signature n g) (input : Fin n → Bool) :
    (unrollLast expression line).eval (program.trace interpretation input) =
      expression.eval ((program.gate line).trace interpretation input) := by
  rw [unrollLast, Expression.eval_substitute]
  apply Expression.eval_congr_inputList
  intro wire _
  refine Fin.lastCases ?_ (fun wire => ?_) wire
  · simp only [Nat.add_eq, Fin.lastCases_last]
    rw [lineExpression_eval, Program.trace_gate_last]
  · simp only [Fin.lastCases_castSucc, Expression.eval, Program.trace_gate_castSucc]

private theorem unrollLast_length (expression : Expression (n + (g + 1)))
    (line : Line signature n g) (once : expression.ReadOnce) :
    (unrollLast expression line).inputList.length ≤ expression.inputList.length + binaryCost line.op := by
  rw [unrollLast, Expression.inputList_substitute]
  apply flatMap_length_le_one_exception expression.inputList once _ (Fin.last (n + g))
  · intro wire
    refine Fin.lastCases (by simp) (fun wire _ => ?_) wire
    simp [Expression.inputList]
  · simpa using lineExpression_length line

private theorem expression_dependsOn_frontier (program : Program signature n g)
    (expression : Expression (n + g)) :
    DependsOnlyOn (fun input => expression.eval (program.trace interpretation input))
      (program.frontierSupport expression.inputList.toFinset) := by
  intro left right agree
  apply Expression.eval_congr_inputList
  intro wire present
  apply Program.trace_congr
  intro i supported
  exact agree i (Finset.mem_biUnion.mpr ⟨wire, List.mem_toFinset.mpr present, supported⟩)

private theorem essential_le_frontier (program : Program signature n g)
    (expression : Expression (n + g))
    (essential : ∀ i, EssentialAt (fun input => expression.eval (program.trace interpretation input)) i) :
    n ≤ expression.inputList.toFinset.card + program.cost binaryCost := by
  have included : Finset.univ ⊆ program.frontierSupport expression.inputList.toFinset := by
    intro i _
    exact (essential i).mem_support (expression_dependsOn_frontier program expression)
  have lower := Finset.card_le_card included
  have upper := program.card_frontierSupport_le binaryCost arity_le_binaryCost expression.inputList.toFinset
  simp only [Finset.card_univ, Fintype.card_fin] at lower
  omega

private theorem exists_readOnce_of_tight_frontier (program : Program signature n g)
    (expression : Expression (n + g)) (once : expression.ReadOnce)
    (essential : ∀ i, EssentialAt (fun input => expression.eval (program.trace interpretation input)) i)
    (tight : expression.inputList.length + program.cost binaryCost ≤ n) :
    ∃ result : Expression n, result.ReadOnce ∧
      ∀ input, result.eval input = expression.eval (program.trace interpretation input) := by
  induction program with
  | empty =>
    refine ⟨expression, once, ?_⟩
    intro input
    apply Expression.eval_congr_inputList
    intro wire _
    change input wire = (Program.empty : Program signature n 0).trace interpretation input (Wire.input wire)
    exact (Program.trace_input _ _ _ _).symm
  | @gate g program line ih =>
    let next := unrollLast expression line
    have evalNext : (fun input => next.eval (program.trace interpretation input)) =
        (fun input => expression.eval ((program.gate line).trace interpretation input)) := by
      funext input
      exact unrollLast_eval expression program line input
    have nextEssential : ∀ i, EssentialAt (fun input => next.eval (program.trace interpretation input)) i := by
      simpa [evalNext] using essential
    have nextTight : next.inputList.length + program.cost binaryCost ≤ n := by
      have lengthBound := unrollLast_length expression line once
      simp only [Program.cost_gate] at tight
      change (unrollLast expression line).inputList.length + program.cost binaryCost ≤ n
      omega
    have nextOnce : next.ReadOnce := by
      have lower := essential_le_frontier program next nextEssential
      have cardinal := List.toFinset_card_le (l := next.inputList)
      have equal : next.inputList.toFinset.card = next.inputList.length := by omega
      exact (Multiset.toFinset_card_eq_card_iff_nodup (m := ⟦next.inputList⟧)).mp equal
    obtain ⟨result, resultOnce, computes⟩ := ih next nextOnce nextEssential nextTight
    exact ⟨result, resultOnce, fun input => (computes input).trans (unrollLast_eval expression program line input)⟩

/-- A shared circuit using the minimum possible number of binary gates has read-once semantics. -/
theorem exists_readOnce_of_binaryCost_le (circuit : Circuit signature n g 1)
    {function : ScalarFunction Bool n}
    (computes : circuit.ComputesWith interpretation (fun input _ => function input))
    (essential : ∀ i, EssentialAt function i) (tight : circuit.cost binaryCost + 1 ≤ n) :
    ∃ expression : Expression n, expression.ReadOnce ∧ expression.eval = function := by
  let output : Expression (n + g) := .input (circuit.outputs 0)
  have equal : (fun input => output.eval (circuit.program.trace interpretation input)) = function := by
    funext input
    exact congrFun (computes input) 0
  obtain ⟨expression, once, correct⟩ := exists_readOnce_of_tight_frontier circuit.program output
    (by simp [output, Expression.ReadOnce, Expression.inputList])
    (by simpa [equal] using essential) (by simpa [output, Expression.inputList, Circuit.cost, Nat.add_comm] using tight)
  refine ⟨expression, once, ?_⟩
  exact (funext correct).trans equal

/-- Unateness is forced at the tight binary-gate budget, even with arbitrary circuit sharing. -/
theorem unate_of_binaryCost_le (circuit : Circuit signature n g 1)
    {function : ScalarFunction Bool n}
    (computes : circuit.ComputesWith interpretation (fun input _ => function input))
    (essential : ∀ i, EssentialAt function i) (tight : circuit.cost binaryCost + 1 ≤ n) :
    Unate function := by
  obtain ⟨expression, once, equal⟩ := exists_readOnce_of_binaryCost_le circuit computes essential tight
  exact equal ▸ once.unate

private theorem binaryCost_le_gateCount (program : Program signature n g) :
    program.cost binaryCost ≤ g := by
  simpa using program.cost_le_mul_gateCount binaryCost (K := 1) (by intro op; cases op <;> decide)

private theorem trace_monotone_of_binaryCost_eq (program : Program signature n g)
    (allBinary : program.cost binaryCost = g) : Monotone (program.trace interpretation) := by
  induction program with
  | empty =>
    intro left right h wire
    change (Program.empty : Program signature n 0).trace interpretation left (Wire.input wire) ≤
      (Program.empty : Program signature n 0).trace interpretation right (Wire.input wire)
    simpa using h wire
  | @gate g program line ih =>
    have priorBound := binaryCost_le_gateCount program
    have lineBound : binaryCost line.op ≤ 1 := by cases line.op <;> decide
    have priorEqual : program.cost binaryCost = g := by simp only [Program.cost_gate] at allBinary; omega
    have charged : binaryCost line.op = 1 := by simp only [Program.cost_gate] at allBinary; omega
    have priorMonotone := ih priorEqual
    intro left right h wire
    refine Fin.lastCases ?_ (fun wire => ?_) wire
    · simp only [Nat.add_eq, Program.trace_gate_last]
      obtain ⟨op, wires⟩ := line
      cases op <;> simp only [binaryCost_false, binaryCost_true, binaryCost_id,
        binaryCost_not, binaryCost_and, binaryCost_or] at charged
      all_goals try contradiction
      all_goals
        have hl := priorMonotone h (wires ⟨0, by decide⟩)
        have hr := priorMonotone h (wires ⟨1, by decide⟩)
        simp only [Line.eval, interpretation, Function.comp_apply]
        change _ ≤ _ at hl hr
        cases a : program.trace interpretation left (wires ⟨0, by decide⟩) <;>
          cases b : program.trace interpretation right (wires ⟨0, by decide⟩) <;>
          cases c : program.trace interpretation left (wires ⟨1, by decide⟩) <;>
          cases d : program.trace interpretation right (wires ⟨1, by decide⟩) <;>
          simp_all [Program.trace]
    · simpa using priorMonotone h wire

/-- An essential non-unate function needs at least `n+1` native gates in an arbitrary shared circuit. -/
theorem size_ge_of_essential_nonunate (circuit : Circuit signature n g 1)
    {function : ScalarFunction Bool n}
    (computes : circuit.ComputesWith interpretation (fun input _ => function input))
    (essential : ∀ i, EssentialAt function i) (nonunate : ¬Unate function) : n + 1 ≤ g := by
  have binaryLower : n ≤ circuit.cost binaryCost := by
    by_contra small
    exact nonunate (unate_of_binaryCost_le circuit computes essential (by omega))
  have binaryBound := binaryCost_le_gateCount circuit.program
  change circuit.cost binaryCost ≤ g at binaryBound
  have strict : circuit.cost binaryCost < g := by
    by_contra large
    have equal : circuit.program.cost binaryCost = g := by change circuit.cost binaryCost = g; omega
    have monotone := trace_monotone_of_binaryCost_eq circuit.program equal
    apply nonunate
    apply unate_of_monotone
    intro left right h
    have relation := monotone h (circuit.outputs 0)
    change circuit.eval interpretation left 0 ≤ circuit.eval interpretation right 0 at relation
    simpa [computes left, computes right] using relation
  omega

/-- Minimum native circuit size inherits the essential non-unate lower bound. -/
theorem complexity_ge_of_essential_nonunate (function : ScalarFunction Bool n)
    (essential : ∀ i, EssentialAt function i) (nonunate : ¬Unate function) : n + 1 ≤ complexity function :=
  size_ge_of_essential_nonunate (minimumCircuit function).circuit
    (minimumCircuit function).computes essential nonunate

end Algebraic.DeMorgan

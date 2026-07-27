/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Batch
public import Complexitylib.Circuits.Unrolling.Transition.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Variable support of transition formulas

This internal module proves that every one-step transition formula reads only
its designated choice wire and the atom wires of the incoming configuration.
The resulting numeric bound is the topological-ordering premise needed by the
packed Boolean-formula compiler.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- A transition formula is supported by its choice and incoming-configuration wires. -/
private def FormulaSupported (tm : NTM k) (T base choiceWire : ℕ)
    (formula : BoolFormula) : Prop :=
  ∀ i ∈ formula.vars,
    i = choiceWire ∨ ∃ atom : ConfigAtom tm T, i = configWire tm T base atom

private theorem formulaSupported_tru (tm : NTM k) (T base choiceWire : ℕ) :
    FormulaSupported tm T base choiceWire .tru := by
  intro i hi
  simp [BoolFormula.vars] at hi

private theorem formulaSupported_fls (tm : NTM k) (T base choiceWire : ℕ) :
    FormulaSupported tm T base choiceWire .fls := by
  intro i hi
  simp [BoolFormula.vars] at hi

private theorem formulaSupported_configVar (tm : NTM k) (T base choiceWire : ℕ)
    (atom : ConfigAtom tm T) :
    FormulaSupported tm T base choiceWire (configVar tm T base atom) := by
  intro i hi
  exact Or.inr ⟨atom, by simpa [configVar, BoolFormula.vars] using hi⟩

private theorem formulaSupported_literal (tm : NTM k) (T base choiceWire : ℕ)
    (value : Bool) :
    FormulaSupported tm T base choiceWire (BoolFormula.literal choiceWire value) := by
  cases value <;> simp [FormulaSupported, BoolFormula.literal, BoolFormula.vars]

private theorem formulaSupported_neg {tm : NTM k} {T base choiceWire : ℕ}
    {formula : BoolFormula} (hformula : FormulaSupported tm T base choiceWire formula) :
    FormulaSupported tm T base choiceWire (.neg formula) := by
  simpa [FormulaSupported, BoolFormula.vars] using hformula

private theorem formulaSupported_conj {tm : NTM k} {T base choiceWire : ℕ}
    {left right : BoolFormula}
    (hleft : FormulaSupported tm T base choiceWire left)
    (hright : FormulaSupported tm T base choiceWire right) :
    FormulaSupported tm T base choiceWire (.conj left right) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hleft i hi
  · exact hright i hi

private theorem formulaSupported_disj {tm : NTM k} {T base choiceWire : ℕ}
    {left right : BoolFormula}
    (hleft : FormulaSupported tm T base choiceWire left)
    (hright : FormulaSupported tm T base choiceWire right) :
    FormulaSupported tm T base choiceWire (.disj left right) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hleft i hi
  · exact hright i hi

private theorem formulaSupported_conjs {tm : NTM k} {T base choiceWire : ℕ}
    (formulas : List BoolFormula)
    (hformulas : ∀ formula ∈ formulas, FormulaSupported tm T base choiceWire formula) :
    FormulaSupported tm T base choiceWire (BoolFormula.conjs formulas) := by
  induction formulas with
  | nil => exact formulaSupported_tru tm T base choiceWire
  | cons formula formulas ih =>
      apply formulaSupported_conj
      · exact hformulas formula (by simp)
      · apply ih
        intro tail htail
        exact hformulas tail (by simp [htail])

private theorem formulaSupported_disjs {tm : NTM k} {T base choiceWire : ℕ}
    (formulas : List BoolFormula)
    (hformulas : ∀ formula ∈ formulas, FormulaSupported tm T base choiceWire formula) :
    FormulaSupported tm T base choiceWire (BoolFormula.disjs formulas) := by
  induction formulas with
  | nil => exact formulaSupported_fls tm T base choiceWire
  | cons formula formulas ih =>
      apply formulaSupported_disj
      · exact hformulas formula (by simp)
      · apply ih
        intro tail htail
        exact hformulas tail (by simp [htail])

private theorem formulaSupported_readFormula (tm : NTM k) (T base choiceWire : ℕ)
    (tape : TapeSlot k) (symbol : Γ) :
    FormulaSupported tm T base choiceWire (readFormula tm T base tape symbol) := by
  unfold readFormula
  apply formulaSupported_disjs
  intro formula hformula
  rcases List.mem_ofFn.mp hformula with ⟨position, rfl⟩
  exact formulaSupported_conj
    (formulaSupported_configVar tm T base choiceWire (.head tape position))
    (formulaSupported_configVar tm T base choiceWire
      (.cell tape (headCellPosition position) symbol))

private theorem formulaSupported_caseFormula (tm : NTM k) (T base choiceWire : ℕ)
    (view : TransitionCase tm) :
    FormulaSupported tm T base choiceWire (caseFormula tm T base choiceWire view) := by
  unfold caseFormula
  apply formulaSupported_conjs
  intro formula hformula
  rcases List.mem_append.mp hformula with hprefix | houtput
  · rcases List.mem_append.mp hprefix with hfixed | hwork
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfixed
      rcases hfixed with rfl | rfl | rfl
      · exact formulaSupported_literal tm T base choiceWire view.choice
      · exact formulaSupported_configVar tm T base choiceWire (.state view.state)
      · exact formulaSupported_readFormula tm T base choiceWire .input view.inputRead
    · rcases List.mem_ofFn.mp hwork with ⟨i, rfl⟩
      exact formulaSupported_readFormula tm T base choiceWire (.work i) (view.workRead i)
  · rw [List.mem_singleton] at houtput
    subst formula
    exact formulaSupported_readFormula tm T base choiceWire .output view.outputRead

private theorem formulaSupported_effectFormula (tm : NTM k) (T base choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) :
    FormulaSupported tm T base choiceWire
      (effectFormula tm T base choiceWire selects) := by
  unfold effectFormula
  apply formulaSupported_disjs
  intro formula hformula
  rcases List.mem_map.mp hformula with ⟨view, _hview, rfl⟩
  split
  · exact formulaSupported_caseFormula tm T base choiceWire view
  · exact formulaSupported_fls tm T base choiceWire

private theorem formulaSupported_selectedStateFormula (tm : NTM k)
    (T base choiceWire : ℕ) (state : tm.Q) :
    FormulaSupported tm T base choiceWire
      (selectedStateFormula tm T base choiceWire state) := by
  unfold selectedStateFormula
  exact formulaSupported_effectFormula tm T base choiceWire _

private theorem formulaSupported_selectedMoveFormula (tm : NTM k)
    (T base choiceWire : ℕ) (tape : TapeSlot k) (direction : Dir3) :
    FormulaSupported tm T base choiceWire
      (selectedMoveFormula tm T base choiceWire tape direction) := by
  unfold selectedMoveFormula
  exact formulaSupported_effectFormula tm T base choiceWire _

private theorem formulaSupported_selectedWriteFormula (tm : NTM k)
    (T base choiceWire : ℕ) (tape : WritableSlot k) (symbol : Γ) :
    FormulaSupported tm T base choiceWire
      (selectedWriteFormula tm T base choiceWire tape symbol) := by
  unfold selectedWriteFormula
  exact formulaSupported_effectFormula tm T base choiceWire _

private theorem formulaSupported_predecessorHeadFormula (tm : NTM k)
    (T base choiceWire : ℕ) (tape : TapeSlot k) (target : Fin (T + 1))
    (direction : Dir3) :
    FormulaSupported tm T base choiceWire
      (predecessorHeadFormula tm T base tape target direction) := by
  unfold predecessorHeadFormula
  apply formulaSupported_disjs
  intro formula hformula
  rcases List.mem_ofFn.mp hformula with ⟨source, rfl⟩
  split
  · exact formulaSupported_configVar tm T base choiceWire (.head tape source)
  · exact formulaSupported_fls tm T base choiceWire

private theorem formulaSupported_movedHeadFormula (tm : NTM k)
    (T base choiceWire : ℕ) (tape : TapeSlot k) (target : Fin (T + 1)) :
    FormulaSupported tm T base choiceWire
      (movedHeadFormula tm T base choiceWire tape target) := by
  unfold movedHeadFormula
  apply formulaSupported_disjs
  intro formula hformula
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hformula
  rcases hformula with rfl | rfl | rfl
  · exact formulaSupported_conj
      (formulaSupported_selectedMoveFormula tm T base choiceWire tape .left)
      (formulaSupported_predecessorHeadFormula tm T base choiceWire tape target .left)
  · exact formulaSupported_conj
      (formulaSupported_selectedMoveFormula tm T base choiceWire tape .right)
      (formulaSupported_predecessorHeadFormula tm T base choiceWire tape target .right)
  · exact formulaSupported_conj
      (formulaSupported_selectedMoveFormula tm T base choiceWire tape .stay)
      (formulaSupported_predecessorHeadFormula tm T base choiceWire tape target .stay)

private theorem formulaSupported_headAtCellFormula (tm : NTM k)
    (T base choiceWire : ℕ) (tape : TapeSlot k) (position : Fin (T + 2)) :
    FormulaSupported tm T base choiceWire
      (headAtCellFormula tm T base tape position) := by
  unfold headAtCellFormula
  split
  · exact formulaSupported_configVar tm T base choiceWire _
  · exact formulaSupported_fls tm T base choiceWire

private theorem formulaSupported_haltedOrFormula {tm : NTM k}
    {T base choiceWire : ℕ} {oldValue nextValue : BoolFormula}
    (hold : FormulaSupported tm T base choiceWire oldValue)
    (hnext : FormulaSupported tm T base choiceWire nextValue) :
    FormulaSupported tm T base choiceWire
      (haltedOrFormula tm T base oldValue nextValue) := by
  unfold haltedOrFormula haltVar
  apply formulaSupported_disj
  · exact formulaSupported_conj
      (formulaSupported_configVar tm T base choiceWire (.state tm.qhalt)) hold
  · exact formulaSupported_conj
      (formulaSupported_neg
        (formulaSupported_configVar tm T base choiceWire (.state tm.qhalt))) hnext

private theorem formulaSupported_writtenCellFormula (tm : NTM k)
    (T base choiceWire : ℕ) (tape : WritableSlot k) (position : Fin (T + 2))
    (symbol : Γ) :
    FormulaSupported tm T base choiceWire
      (writtenCellFormula tm T base choiceWire tape position symbol) := by
  unfold writtenCellFormula
  apply formulaSupported_disj
  · exact formulaSupported_conj
      (formulaSupported_headAtCellFormula tm T base choiceWire tape.toTapeSlot position)
      (formulaSupported_selectedWriteFormula tm T base choiceWire tape symbol)
  · exact formulaSupported_conj
      (formulaSupported_neg
        (formulaSupported_headAtCellFormula tm T base choiceWire tape.toTapeSlot position))
      (formulaSupported_configVar tm T base choiceWire
        (.cell tape.toTapeSlot position symbol))

private theorem formulaSupported_nextFormula (tm : NTM k) (T base choiceWire : ℕ)
    (atom : ConfigAtom tm T) :
    FormulaSupported tm T base choiceWire (nextFormula tm T base choiceWire atom) := by
  cases atom with
  | state state =>
      exact formulaSupported_haltedOrFormula
        (formulaSupported_configVar tm T base choiceWire (.state state))
        (formulaSupported_selectedStateFormula tm T base choiceWire state)
  | head tape position =>
      exact formulaSupported_haltedOrFormula
        (formulaSupported_configVar tm T base choiceWire (.head tape position))
        (formulaSupported_movedHeadFormula tm T base choiceWire tape position)
  | cell tape position symbol =>
      cases tape with
      | input => exact formulaSupported_configVar tm T base choiceWire _
      | work i =>
          simp only [nextFormula]
          split
          · exact formulaSupported_configVar tm T base choiceWire _
          · exact formulaSupported_haltedOrFormula
              (formulaSupported_configVar tm T base choiceWire _)
              (formulaSupported_writtenCellFormula tm T base choiceWire
                (.work i) position symbol)
      | output =>
          simp only [nextFormula]
          split
          · exact formulaSupported_configVar tm T base choiceWire _
          · exact formulaSupported_haltedOrFormula
              (formulaSupported_configVar tm T base choiceWire _)
              (formulaSupported_writtenCellFormula tm T base choiceWire
                .output position symbol)

/-- Internal support law for every next-configuration formula variable. -/
theorem mem_vars_nextFormula_internal (tm : NTM k) (T base choiceWire : ℕ)
    (atom : ConfigAtom tm T) (i : ℕ)
    (hi : i ∈ (nextFormula tm T base choiceWire atom).vars) :
    i = choiceWire ∨
      ∃ oldAtom : ConfigAtom tm T, i = configWire tm T base oldAtom :=
  formulaSupported_nextFormula tm T base choiceWire atom i hi

/-- Internal numeric support bound used to compile a transition after a prefix. -/
theorem vars_nextFormula_lt_internal (tm : NTM k) (T base choiceWire available : ℕ)
    (atom : ConfigAtom tm T) (hchoice : choiceWire < available)
    (hconfig : base + configWidth tm T ≤ available) :
    ∀ i ∈ (nextFormula tm T base choiceWire atom).vars, i < available := by
  intro i hi
  rcases mem_vars_nextFormula_internal tm T base choiceWire atom i hi with
    rfl | ⟨oldAtom, rfl⟩
  · exact hchoice
  · unfold configWire
    have hindex := configIndex_lt tm T oldAtom
    omega

end CircuitUnrolling

end Complexity

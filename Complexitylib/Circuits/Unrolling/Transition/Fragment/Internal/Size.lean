/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Structure
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.Ring

/-!
# Size bounds for packed one-step transition fragments

This internal module bounds every formula in a bounded transition layer by a
machine-dependent linear function of the trace horizon. Since a configuration
block itself has linear width, the packed one-step fragment has quadratic size.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

@[nolint docBlame]
def caseSizeCoeff (k : ℕ) : ℕ :=
  4 * (k + 2) + 6

@[nolint docBlame]
noncomputable def effectSizeCoeff (tm : NTM k) : ℕ :=
  1 + (transitionCases tm).length * (caseSizeCoeff k + 1)

@[nolint docBlame]
noncomputable def nextSizeCoeff (tm : NTM k) : ℕ :=
  3 * effectSizeCoeff tm + 20

@[nolint docBlame]
def widthSizeCoeff (tm : NTM k) : ℕ :=
  Fintype.card tm.Q + 5 * (k + 2)

theorem sum_map_le_length_mul {alpha : Type*} (items : List alpha)
    (weight : alpha → ℕ) (bound : ℕ)
    (hbound : ∀ item ∈ items, weight item ≤ bound) :
    (items.map weight).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
      have hitem : weight item ≤ bound := hbound item (by simp)
      have htail : ∀ next ∈ items, weight next ≤ bound := by
        intro next hnext
        exact hbound next (by simp [hnext])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        weight item + (items.map weight).sum ≤
            bound + items.length * bound := Nat.add_le_add hitem (ih htail)
        _ = (items.length + 1) * bound := by ring

theorem size_disjs_le_of_succ_le (formulas : List BoolFormula)
    (bound : ℕ) (hbound : ∀ formula ∈ formulas, formula.size + 1 ≤ bound) :
    (BoolFormula.disjs formulas).size ≤ 1 + formulas.length * bound := by
  rw [BoolFormula.size_disjs]
  exact Nat.add_le_add_left
    (sum_map_le_length_mul formulas (fun formula => formula.size + 1) bound hbound) 1

/-- Internal exact size of a configuration-variable formula. -/
@[simp] theorem size_configVar_internal (tm : NTM k) (T base : ℕ)
    (atom : ConfigAtom tm T) :
    (configVar tm T base atom).size = 1 := by
  simp [configVar, BoolFormula.size]

/-- Internal exact size of the halted-state variable. -/
@[simp] theorem size_haltVar_internal (tm : NTM k) (T base : ℕ) :
    (haltVar tm T base).size = 1 := by
  simp [haltVar]

/-- A read formula plus its enclosing list connective costs at most four nodes
per represented head position. -/
theorem size_readFormula_succ_le_internal (tm : NTM k) (T base : ℕ)
    (tape : TapeSlot k) (symbol : Γ) :
    (readFormula tm T base tape symbol).size + 1 ≤ 4 * (T + 2) := by
  let formulas : List BoolFormula := List.ofFn fun position : Fin (T + 1) =>
    BoolFormula.conj (configVar tm T base (.head tape position))
      (configVar tm T base (.cell tape (headCellPosition position) symbol))
  change (BoolFormula.disjs formulas).size + 1 ≤ _
  have hsize := size_disjs_le_of_succ_le formulas 4 (by
    intro formula hformula
    dsimp only [formulas] at hformula
    rw [List.mem_ofFn] at hformula
    obtain ⟨position, rfl⟩ := hformula
    simp only [BoolFormula.size, size_configVar_internal]
    omega)
  have hlength : formulas.length = T + 1 := by simp [formulas]
  rw [hlength] at hsize
  omega

/-- Internal linear size bound for a complete local transition case. -/
theorem size_caseFormula_le_internal (tm : NTM k) (T base choiceWire : ℕ)
    (view : TransitionCase tm) :
    (caseFormula tm T base choiceWire view).size ≤
      caseSizeCoeff k * (T + 2) := by
  let workReads := List.ofFn fun i : Fin k =>
    readFormula tm T base (.work i) (view.workRead i)
  have hliteral :
      (BoolFormula.literal choiceWire view.choice).size + 1 ≤ 3 := by
    have := BoolFormula.size_literal_le_two choiceWire view.choice
    omega
  have hinput := size_readFormula_succ_le_internal tm T base .input view.inputRead
  have houtput := size_readFormula_succ_le_internal tm T base .output view.outputRead
  have hwork :
      (workReads.map fun formula => formula.size + 1).sum ≤
        k * (4 * (T + 2)) := by
    have h := sum_map_le_length_mul workReads
      (fun formula => formula.size + 1) (4 * (T + 2)) (by
        intro formula hformula
        dsimp only [workReads] at hformula
        rw [List.mem_ofFn] at hformula
        obtain ⟨i, rfl⟩ := hformula
        exact size_readFormula_succ_le_internal tm T base (.work i) (view.workRead i))
    simpa [workReads] using h
  rw [caseFormula, BoolFormula.size_conjs]
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil]
  have hraw :
      1 +
          (((BoolFormula.literal choiceWire view.choice).size + 1 +
              ((configVar tm T base (.state view.state)).size + 1) +
            ((readFormula tm T base .input view.inputRead).size + 1)) +
            (workReads.map fun formula => formula.size + 1).sum +
          ((readFormula tm T base .output view.outputRead).size + 1)) ≤
        6 + (k + 2) * (4 * (T + 2)) := by
    simp only [size_configVar_internal]
    calc
      1 + (((BoolFormula.literal choiceWire view.choice).size + 1 + (1 + 1) +
              ((readFormula tm T base .input view.inputRead).size + 1)) +
            (workReads.map fun formula => formula.size + 1).sum +
          ((readFormula tm T base .output view.outputRead).size + 1)) ≤
          6 + k * (4 * (T + 2)) + 2 * (4 * (T + 2)) := by omega
      _ = 6 + (k + 2) * (4 * (T + 2)) := by ring
  have hshape :
      1 +
          ((BoolFormula.literal choiceWire view.choice).size + 1 +
                ((configVar tm T base (.state view.state)).size + 1 +
                  ((readFormula tm T base .input view.inputRead).size + 1 + 0)) +
            (workReads.map fun formula => formula.size + 1).sum +
          ((readFormula tm T base .output view.outputRead).size + 1 + 0)) ≤
        6 + (k + 2) * (4 * (T + 2)) := by
    simpa only [Nat.add_zero, Nat.add_assoc] using hraw
  calc
    1 +
          ((BoolFormula.literal choiceWire view.choice).size + 1 +
                ((configVar tm T base (.state view.state)).size + 1 +
                  ((readFormula tm T base .input view.inputRead).size + 1 + 0)) +
            (workReads.map fun formula => formula.size + 1).sum +
          ((readFormula tm T base .output view.outputRead).size + 1 + 0)) ≤
        6 + (k + 2) * (4 * (T + 2)) := hshape
    _ ≤ 6 * (T + 2) + (k + 2) * (4 * (T + 2)) := by
      have hfactor : 6 ≤ 6 * (T + 2) := by
        calc
          6 = 6 * 1 := by simp
          _ ≤ 6 * (T + 2) := Nat.mul_le_mul_left _ (by omega)
      exact Nat.add_le_add_right hfactor _
    _ = caseSizeCoeff k * (T + 2) := by
      simp only [caseSizeCoeff]
      ring

/-- Internal linear size bound for a finite transition-effect selector. -/
theorem size_effectFormula_le_internal (tm : NTM k) (T base choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) :
    (effectFormula tm T base choiceWire selects).size ≤
      effectSizeCoeff tm * (T + 2) := by
  unfold effectFormula
  have hbranch : ∀ formula ∈
      (transitionCases tm).map (fun view =>
        if selects view.effect then caseFormula tm T base choiceWire view else .fls),
      formula.size + 1 ≤ (caseSizeCoeff k + 1) * (T + 2) := by
    intro formula hformula
    rw [List.mem_map] at hformula
    obtain ⟨view, _, rfl⟩ := hformula
    split
    · have hcase := size_caseFormula_le_internal tm T base choiceWire view
      calc
        (caseFormula tm T base choiceWire view).size + 1 ≤
            caseSizeCoeff k * (T + 2) + 1 := Nat.add_le_add_right hcase 1
        _ ≤ caseSizeCoeff k * (T + 2) + (T + 2) := by omega
        _ = (caseSizeCoeff k + 1) * (T + 2) := by ring
    · simp only [BoolFormula.size]
      have hcoeff : 2 ≤ caseSizeCoeff k + 1 := by
        simp only [caseSizeCoeff]
        omega
      have hhorizon : 1 ≤ T + 2 := by omega
      simpa using Nat.mul_le_mul hcoeff hhorizon
  have hdisj := size_disjs_le_of_succ_le _ _ hbranch
  rw [List.length_map] at hdisj
  calc
    (BoolFormula.disjs ((transitionCases tm).map fun view =>
        if selects view.effect then caseFormula tm T base choiceWire view else .fls)).size ≤
      1 + (transitionCases tm).length *
        ((caseSizeCoeff k + 1) * (T + 2)) := hdisj
    _ ≤ (T + 2) + (transitionCases tm).length *
        ((caseSizeCoeff k + 1) * (T + 2)) := by omega
    _ = effectSizeCoeff tm * (T + 2) := by
      simp only [effectSizeCoeff]
      ring

/-- Internal size bound for successor-state selection. -/
theorem size_selectedStateFormula_le_internal (tm : NTM k)
    (T base choiceWire : ℕ) (state : tm.Q) :
    (selectedStateFormula tm T base choiceWire state).size ≤
      effectSizeCoeff tm * (T + 2) := by
  exact size_effectFormula_le_internal tm T base choiceWire _

/-- Internal size bound for head-movement selection. -/
theorem size_selectedMoveFormula_le_internal (tm : NTM k)
    (T base choiceWire : ℕ) (tape : TapeSlot k) (direction : Dir3) :
    (selectedMoveFormula tm T base choiceWire tape direction).size ≤
      effectSizeCoeff tm * (T + 2) := by
  exact size_effectFormula_le_internal tm T base choiceWire _

/-- Internal size bound for write-symbol selection. -/
theorem size_selectedWriteFormula_le_internal (tm : NTM k)
    (T base choiceWire : ℕ) (tape : WritableSlot k) (symbol : Γ) :
    (selectedWriteFormula tm T base choiceWire tape symbol).size ≤
      effectSizeCoeff tm * (T + 2) := by
  exact size_effectFormula_le_internal tm T base choiceWire _

/-- Internal linear size bound for predecessor-head selection. -/
theorem size_predecessorHeadFormula_le_internal (tm : NTM k)
    (T base : ℕ) (tape : TapeSlot k) (target : Fin (T + 1))
    (direction : Dir3) :
    (predecessorHeadFormula tm T base tape target direction).size ≤
      2 * (T + 2) := by
  unfold predecessorHeadFormula
  have hdisj := size_disjs_le_of_succ_le
    (List.ofFn fun source : Fin (T + 1) =>
      if movedHeadPosition source.val direction = target.val then
        configVar tm T base (.head tape source)
      else
        BoolFormula.fls) 2 (by
          intro formula hformula
          rw [List.mem_ofFn] at hformula
          obtain ⟨source, rfl⟩ := hformula
          split <;> simp [BoolFormula.size])
  simp only [List.length_ofFn] at hdisj
  omega

/-- Internal linear size bound for a moved-head atom. -/
theorem size_movedHeadFormula_le_internal (tm : NTM k)
    (T base choiceWire : ℕ) (tape : TapeSlot k) (target : Fin (T + 1)) :
    (movedHeadFormula tm T base choiceWire tape target).size ≤
      (3 * effectSizeCoeff tm + 13) * (T + 2) := by
  let formulas : List BoolFormula :=
    [BoolFormula.conj (selectedMoveFormula tm T base choiceWire tape .left)
        (predecessorHeadFormula tm T base tape target .left),
      BoolFormula.conj (selectedMoveFormula tm T base choiceWire tape .right)
        (predecessorHeadFormula tm T base tape target .right),
      BoolFormula.conj (selectedMoveFormula tm T base choiceWire tape .stay)
        (predecessorHeadFormula tm T base tape target .stay)]
  have hdirection (direction : Dir3) :
      (BoolFormula.conj (selectedMoveFormula tm T base choiceWire tape direction)
        (predecessorHeadFormula tm T base tape target direction)).size + 1 ≤
          (effectSizeCoeff tm + 4) * (T + 2) := by
    simp only [BoolFormula.size]
    have hmove :=
      size_selectedMoveFormula_le_internal tm T base choiceWire tape direction
    have hpred :=
      size_predecessorHeadFormula_le_internal tm T base tape target direction
    calc
      _ ≤ effectSizeCoeff tm * (T + 2) + 2 * (T + 2) + 2 := by omega
      _ ≤ effectSizeCoeff tm * (T + 2) + 4 * (T + 2) := by omega
      _ = (effectSizeCoeff tm + 4) * (T + 2) := by ring
  have hchild : ∀ formula ∈ formulas,
      formula.size + 1 ≤ (effectSizeCoeff tm + 4) * (T + 2) := by
    intro formula hformula
    simp only [formulas, List.mem_cons, List.not_mem_nil, or_false] at hformula
    rcases hformula with rfl | rfl | rfl
    · exact hdirection .left
    · exact hdirection .right
    · exact hdirection .stay
  have hdisj := size_disjs_le_of_succ_le formulas
    ((effectSizeCoeff tm + 4) * (T + 2)) hchild
  have hlength : formulas.length = 3 := by simp [formulas]
  change (BoolFormula.disjs formulas).size ≤ _
  calc
    (BoolFormula.disjs formulas).size ≤
        1 + formulas.length * ((effectSizeCoeff tm + 4) * (T + 2)) := hdisj
    _ = 1 + 3 * ((effectSizeCoeff tm + 4) * (T + 2)) := by rw [hlength]
    _ ≤ (T + 2) + 3 * ((effectSizeCoeff tm + 4) * (T + 2)) := by omega
    _ = (3 * effectSizeCoeff tm + 13) * (T + 2) := by ring

/-- Internal exact size of the old-head-at-cell formula. -/
@[simp] theorem size_headAtCellFormula_internal (tm : NTM k) (T base : ℕ)
    (tape : TapeSlot k) (position : Fin (T + 2)) :
    (headAtCellFormula tm T base tape position).size = 1 := by
  unfold headAtCellFormula configVar
  split <;> rfl

/-- Internal exact overhead of halted-or-successor multiplexing. -/
@[simp] theorem size_haltedOrFormula_internal (tm : NTM k) (T base : ℕ)
    (oldValue nextValue : BoolFormula) :
    (haltedOrFormula tm T base oldValue nextValue).size =
      oldValue.size + nextValue.size + 6 := by
  simp [haltedOrFormula, BoolFormula.size]
  omega

/-- Internal linear size bound for a positive writable-cell formula. -/
theorem size_writtenCellFormula_le_internal (tm : NTM k)
    (T base choiceWire : ℕ) (tape : WritableSlot k)
    (position : Fin (T + 2)) (symbol : Γ) :
    (writtenCellFormula tm T base choiceWire tape position symbol).size ≤
      effectSizeCoeff tm * (T + 2) + 7 := by
  have hwrite :=
    size_selectedWriteFormula_le_internal tm T base choiceWire tape symbol
  simp only [writtenCellFormula, BoolFormula.size, size_configVar_internal,
    size_headAtCellFormula_internal]
  omega

/-- Every successor-configuration atom has size linear in the horizon. -/
theorem size_nextFormula_le_internal (tm : NTM k) (T base choiceWire : ℕ)
    (atom : ConfigAtom tm T) :
    (nextFormula tm T base choiceWire atom).size ≤
      nextSizeCoeff tm * (T + 2) := by
  have hhorizon : 1 ≤ T + 2 := by omega
  have hcoeff : 1 ≤ nextSizeCoeff tm := by
    simp only [nextSizeCoeff]
    omega
  have hone : 1 ≤ nextSizeCoeff tm * (T + 2) := by
    calc
      1 = 1 * 1 := by simp
      _ ≤ nextSizeCoeff tm * (T + 2) := Nat.mul_le_mul hcoeff hhorizon
  have hseven : 7 ≤ 7 * (T + 2) := by
    calc
      7 = 7 * 1 := by simp
      _ ≤ 7 * (T + 2) := Nat.mul_le_mul_left 7 hhorizon
  have hfourteen : 14 ≤ 14 * (T + 2) := by
    calc
      14 = 14 * 1 := by simp
      _ ≤ 14 * (T + 2) := Nat.mul_le_mul_left 14 hhorizon
  have hstateSlack :
      effectSizeCoeff tm * (T + 2) + 7 ≤ nextSizeCoeff tm * (T + 2) := by
    calc
      effectSizeCoeff tm * (T + 2) + 7 ≤
          effectSizeCoeff tm * (T + 2) + 7 * (T + 2) :=
        Nat.add_le_add_left hseven _
      _ = (effectSizeCoeff tm + 7) * (T + 2) := by ring
      _ ≤ (3 * effectSizeCoeff tm + 20) * (T + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = nextSizeCoeff tm * (T + 2) := by rw [nextSizeCoeff]
  have hheadSlack :
      (3 * effectSizeCoeff tm + 13) * (T + 2) + 7 ≤
        nextSizeCoeff tm * (T + 2) := by
    calc
      (3 * effectSizeCoeff tm + 13) * (T + 2) + 7 ≤
          (3 * effectSizeCoeff tm + 13) * (T + 2) + 7 * (T + 2) :=
        Nat.add_le_add_left hseven _
      _ = (3 * effectSizeCoeff tm + 20) * (T + 2) := by ring
      _ = nextSizeCoeff tm * (T + 2) := by rw [nextSizeCoeff]
  have hcellSlack :
      effectSizeCoeff tm * (T + 2) + 14 ≤ nextSizeCoeff tm * (T + 2) := by
    calc
      effectSizeCoeff tm * (T + 2) + 14 ≤
          effectSizeCoeff tm * (T + 2) + 14 * (T + 2) :=
        Nat.add_le_add_left hfourteen _
      _ = (effectSizeCoeff tm + 14) * (T + 2) := by ring
      _ ≤ (3 * effectSizeCoeff tm + 20) * (T + 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = nextSizeCoeff tm * (T + 2) := by rw [nextSizeCoeff]
  cases atom with
  | state state =>
      have hstate := size_selectedStateFormula_le_internal tm T base choiceWire state
      rw [nextFormula, size_haltedOrFormula_internal, size_configVar_internal]
      calc
        1 + (selectedStateFormula tm T base choiceWire state).size + 6 ≤
            effectSizeCoeff tm * (T + 2) + 7 := by omega
        _ ≤ nextSizeCoeff tm * (T + 2) := hstateSlack
  | head tape position =>
      have hhead := size_movedHeadFormula_le_internal tm T base choiceWire tape position
      rw [nextFormula, size_haltedOrFormula_internal, size_configVar_internal]
      calc
        1 + (movedHeadFormula tm T base choiceWire tape position).size + 6 ≤
            (3 * effectSizeCoeff tm + 13) * (T + 2) + 7 := by omega
        _ ≤ nextSizeCoeff tm * (T + 2) := hheadSlack
  | cell tape position symbol =>
      cases tape with
      | input =>
          simpa only [nextFormula, size_configVar_internal] using hone
      | work i =>
          simp only [nextFormula]
          split
          · simpa only [size_configVar_internal] using hone
          · have hcell := size_writtenCellFormula_le_internal tm T base choiceWire
                (.work i) position symbol
            rw [size_haltedOrFormula_internal, size_configVar_internal]
            calc
              1 + (writtenCellFormula tm T base choiceWire (.work i) position symbol).size +
                    6 ≤ effectSizeCoeff tm * (T + 2) + 14 := by omega
              _ ≤ nextSizeCoeff tm * (T + 2) := hcellSlack
      | output =>
          simp only [nextFormula]
          split
          · simpa only [size_configVar_internal] using hone
          · have hcell := size_writtenCellFormula_le_internal tm T base choiceWire
                .output position symbol
            rw [size_haltedOrFormula_internal, size_configVar_internal]
            calc
              1 + (writtenCellFormula tm T base choiceWire .output position symbol).size +
                    6 ≤ effectSizeCoeff tm * (T + 2) + 14 := by omega
              _ ≤ nextSizeCoeff tm * (T + 2) := hcellSlack

/-- The bounded configuration width is linear in the horizon. -/
theorem configWidth_le_linear_internal (tm : NTM k) (T : ℕ) :
    configWidth tm T ≤ widthSizeCoeff tm * (T + 2) := by
  have hhead : T + 1 ≤ T + 2 := by omega
  have hhead' := Nat.mul_le_mul_left (k + 2) hhead
  have hstate : Fintype.card tm.Q ≤ Fintype.card tm.Q * (T + 2) := by
    calc
      Fintype.card tm.Q = Fintype.card tm.Q * 1 := by simp
      _ ≤ Fintype.card tm.Q * (T + 2) :=
        Nat.mul_le_mul_left _ (by omega)
  simp only [configWidth, widthSizeCoeff]
  calc
    Fintype.card tm.Q + (k + 2) * (T + 1) + 4 * (k + 2) * (T + 2) ≤
        Fintype.card tm.Q + (k + 2) * (T + 2) +
          4 * (k + 2) * (T + 2) :=
      Nat.add_le_add_right (Nat.add_le_add_left hhead' _) _
    _ = Fintype.card tm.Q + 5 * (k + 2) * (T + 2) := by ring
    _ ≤ Fintype.card tm.Q * (T + 2) + 5 * (k + 2) * (T + 2) :=
      Nat.add_le_add_right hstate _
    _ = (Fintype.card tm.Q + 5 * (k + 2)) * (T + 2) := by ring

/-- Internal explicit form of the linear configuration-width bound. -/
theorem configWidth_le_explicit_internal (tm : NTM k) (T : ℕ) :
    configWidth tm T ≤
      (Fintype.card tm.Q + 5 * (k + 2)) * (T + 2) := by
  simpa [widthSizeCoeff] using configWidth_le_linear_internal tm T

theorem stepSizeCoeff_eq_internal (tm : NTM k) :
    stepSizeCoeff tm = widthSizeCoeff tm * (nextSizeCoeff tm + 1) := by
  simp only [stepSizeCoeff, widthSizeCoeff, nextSizeCoeff, effectSizeCoeff,
    caseSizeCoeff]
  ring

/-- The exact packed one-step gate count is quadratic in the trace horizon. -/
theorem stepFragmentSize_le_internal (tm : NTM k) (T configBase choiceWire : ℕ) :
    stepFragmentSize tm T configBase choiceWire ≤
      stepSizeCoeff tm * (T + 2) ^ 2 := by
  let formulas := stepFormulas tm T configBase choiceWire
  have hformula : ∀ formula ∈ formulas,
      formula.size ≤ nextSizeCoeff tm * (T + 2) := by
    intro formula hmem
    dsimp only [formulas, stepFormulas] at hmem
    rw [List.mem_map] at hmem
    obtain ⟨atom, _, rfl⟩ := hmem
    exact size_nextFormula_le_internal tm T configBase choiceWire atom
  have hsum :
      (formulas.map BoolFormula.size).sum ≤
        formulas.length * (nextSizeCoeff tm * (T + 2)) :=
    sum_map_le_length_mul formulas BoolFormula.size _ hformula
  have hlength : formulas.length = configWidth tm T := by
    simp [formulas, length_stepFormulas_internal]
  have hwidth := configWidth_le_linear_internal tm T
  have hone : 1 ≤ T + 2 := by omega
  rw [stepFragmentSize]
  change (formulas.map BoolFormula.size).sum + formulas.length ≤ _
  calc
    (formulas.map BoolFormula.size).sum + formulas.length ≤
        formulas.length * (nextSizeCoeff tm * (T + 2)) + formulas.length :=
      Nat.add_le_add_right hsum _
    _ = formulas.length * (nextSizeCoeff tm * (T + 2) + 1) := by ring
    _ ≤ formulas.length * ((nextSizeCoeff tm + 1) * (T + 2)) := by
      apply Nat.mul_le_mul_left
      calc
        nextSizeCoeff tm * (T + 2) + 1 ≤
            nextSizeCoeff tm * (T + 2) + (T + 2) := by omega
        _ = (nextSizeCoeff tm + 1) * (T + 2) := by ring
    _ ≤ widthSizeCoeff tm * (T + 2) *
        ((nextSizeCoeff tm + 1) * (T + 2)) := by
      rw [hlength]
      exact Nat.mul_le_mul_right _ hwidth
    _ = stepSizeCoeff tm * (T + 2) ^ 2 := by
      rw [stepSizeCoeff_eq_internal]
      ring

end CircuitUnrolling

end Complexity

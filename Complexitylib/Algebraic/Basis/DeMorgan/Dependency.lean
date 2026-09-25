/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Origin

/-!
# The charged dependency graph

The predicates in this module describe the circuit graph after contracting
zero-cost gates.  A charged gate reads an input or another charged gate when
one of its raw argument wires has that charged origin.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/-- An internal gate is charged exactly when it is an AND or OR gate. -/
def ChargedGate
    (program : Program signature n g)
    (gate : Fin g) : Prop :=
  binaryCost (program.lines gate).op = 1

/-- A charged internal gate reads an original input through only free gates. -/
def ReadsInput
    (program : Program signature n g)
    (gate : Fin g)
    (input : Fin n) : Prop :=
  ChargedGate program gate ∧
    ∃ argument negated,
      origins program ((program.lines gate).wires argument) =
        .wire negated (Wire.input input)

/-- Every argument of a charged gate contracts to a literal of one input. -/
def ReadsOnlyInput
    (program : Program signature n g)
    (gate : Fin g)
    (input : Fin n) : Prop :=
  ChargedGate program gate ∧
    ∀ argument, ∃ negated,
      origins program ((program.lines gate).wires argument) =
        .wire negated (Wire.input input)

/-- One charged internal gate feeds another through only free gates. -/
def UsesGate
    (program : Program signature n g)
    (source target : Fin g) : Prop :=
  ChargedGate program target ∧
    ∃ argument negated,
      origins program ((program.lines target).wires argument) =
        .wire negated (Wire.gate source)

/-- A contracted origin is simple when it is a constant or a signed input. -/
def SimpleOrigin : ResidualValue n g → Prop
  | .constant _ => True
  | .wire _ wire => ∃ input, wire = Wire.input input

/-- Simplicity is preserved when a program is extended by one gate. -/
theorem SimpleOrigin.map_castSucc
    {value : ResidualValue n g}
    (simple : SimpleOrigin value) :
    SimpleOrigin (value.mapWires Wire.Renaming.castSucc) := by
  cases value with
  | constant value => trivial
  | wire negated wire =>
      obtain ⟨input, rfl⟩ := simple
      exact ⟨input, by simp⟩

/-- A simple origin cannot be the output of a charged gate. -/
theorem SimpleOrigin.ne_gate
    {value : ResidualValue n g}
    (simple : SimpleOrigin value)
    (negated : Bool)
    (gate : Fin g) :
    value ≠ .wire negated (Wire.gate gate) := by
  cases value with
  | constant value => simp
  | wire sign wire =>
      obtain ⟨input, rfl⟩ := simple
      intro equal
      injection equal with _ wire_eq
      have values := congrArg Fin.val wire_eq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at values
      omega

/--
An initial charged gate, presented with its two named arguments.  Its arguments
have no charged predecessors after contracting the free gates.
-/
structure InitialChargedGate (program : Program signature n g) where
  /-- The selected gate. -/
  gate : Fin g
  /-- Its binary operation. -/
  op : BinaryOp
  /-- Its left input wire. -/
  left : Wire n g
  /-- Its right input wire. -/
  right : Wire n g
  /-- The widened program line has the claimed binary presentation. -/
  line_eq : program.lines gate = binaryLine op left right
  /-- The left contracted origin is a constant or literal. -/
  left_simple : SimpleOrigin (origins program left)
  /-- The right contracted origin is a constant or literal. -/
  right_simple : SimpleOrigin (origins program right)

/-- Every initial charged gate is charged in the weighted De Morgan model. -/
theorem InitialChargedGate.charged
    (initial : InitialChargedGate program) :
    ChargedGate program initial.gate := by
  rw [ChargedGate, initial.line_eq]
  simp

/-- The four structural possibilities for an initial charged gate. -/
inductive InitialGatePattern
    {program : Program signature n g}
    (initial : InitialChargedGate program) : Type
  | constantLeft (value : Bool) :
      origins program initial.left = .constant value →
      InitialGatePattern initial
  | constantRight (value : Bool) :
      origins program initial.right = .constant value →
      InitialGatePattern initial
  | singleInput (input : Fin n) (leftNegated rightNegated : Bool) :
      origins program initial.left = .wire leftNegated (Wire.input input) →
      origins program initial.right = .wire rightNegated (Wire.input input) →
      InitialGatePattern initial
  | distinctInputs
      (leftInput rightInput : Fin n)
      (leftNegated rightNegated : Bool) :
      leftInput ≠ rightInput →
      origins program initial.left = .wire leftNegated (Wire.input leftInput) →
      origins program initial.right = .wire rightNegated (Wire.input rightInput) →
      InitialGatePattern initial

/-- Classify the two simple origins of an initial charged gate. -/
noncomputable def InitialChargedGate.pattern
    {program : Program signature n g}
    (initial : InitialChargedGate program) :
    InitialGatePattern initial := by
  classical
  have leftSimple := initial.left_simple
  generalize left_eq : origins program initial.left = leftOrigin
    at leftSimple
  cases leftOrigin with
  | constant value => exact .constantLeft value left_eq
  | wire leftNegated leftWire =>
      let leftInput := Exists.choose leftSimple
      have leftWire_eq : leftWire = Wire.input leftInput :=
        Exists.choose_spec leftSimple
      rw [leftWire_eq] at left_eq
      have rightSimple := initial.right_simple
      generalize right_eq : origins program initial.right = rightOrigin
        at rightSimple
      cases rightOrigin with
      | constant value => exact .constantRight value right_eq
      | wire rightNegated rightWire =>
          let rightInput := Exists.choose rightSimple
          have rightWire_eq : rightWire = Wire.input rightInput :=
            Exists.choose_spec rightSimple
          rw [rightWire_eq] at right_eq
          by_cases same : leftInput = rightInput
          · rw [← same] at right_eq
            exact .singleInput leftInput leftNegated rightNegated left_eq right_eq
          · exact .distinctInputs leftInput rightInput leftNegated rightNegated
              same left_eq right_eq

/-- The left literal of an initial gate gives a direct-input edge. -/
theorem InitialChargedGate.readsInput_left
    {program : Program signature n g}
    (initial : InitialChargedGate program)
    {input : Fin n}
    {negated : Bool}
    (origin_eq : origins program initial.left =
      .wire negated (Wire.input input)) :
    ReadsInput program initial.gate input := by
  refine ⟨initial.charged, ?_⟩
  rw [initial.line_eq]
  cases initial.op with
  | and =>
      change ∃ argument : Fin 2, ∃ negated,
        origins program ((binaryLine .and initial.left initial.right).wires argument) = _
      exact ⟨0, negated, by simpa [binaryLine] using origin_eq⟩
  | or =>
      change ∃ argument : Fin 2, ∃ negated,
        origins program ((binaryLine .or initial.left initial.right).wires argument) = _
      exact ⟨0, negated, by simpa [binaryLine] using origin_eq⟩

/-- The right literal of an initial gate gives a direct-input edge. -/
theorem InitialChargedGate.readsInput_right
    {program : Program signature n g}
    (initial : InitialChargedGate program)
    {input : Fin n}
    {negated : Bool}
    (origin_eq : origins program initial.right =
      .wire negated (Wire.input input)) :
    ReadsInput program initial.gate input := by
  refine ⟨initial.charged, ?_⟩
  rw [initial.line_eq]
  cases initial.op with
  | and =>
      change ∃ argument : Fin 2, ∃ negated,
        origins program ((binaryLine .and initial.left initial.right).wires argument) = _
      refine ⟨1, negated, ?_⟩
      change origins program initial.right = _
      exact origin_eq
  | or =>
      change ∃ argument : Fin 2, ∃ negated,
        origins program ((binaryLine .or initial.left initial.right).wires argument) = _
      refine ⟨1, negated, ?_⟩
      change origins program initial.right = _
      exact origin_eq

/-- Two literals of the same input make an initial gate a single-input gate. -/
theorem InitialChargedGate.readsOnlyInput
    {program : Program signature n g}
    (initial : InitialChargedGate program)
    {input : Fin n}
    {leftNegated rightNegated : Bool}
    (leftOrigin : origins program initial.left =
      .wire leftNegated (Wire.input input))
    (rightOrigin : origins program initial.right =
      .wire rightNegated (Wire.input input)) :
    ReadsOnlyInput program initial.gate input := by
  refine ⟨initial.charged, ?_⟩
  rw [initial.line_eq]
  cases initial.op with
  | and =>
      change ∀ argument : Fin 2, ∃ negated,
        origins program ((binaryLine .and initial.left initial.right).wires argument) = _
      intro argument
      refine Fin.cases ⟨leftNegated, by simpa [binaryLine] using leftOrigin⟩
        (fun remaining => ?_) argument
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      refine ⟨rightNegated, ?_⟩
      change origins program initial.right = _
      exact rightOrigin
  | or =>
      change ∀ argument : Fin 2, ∃ negated,
        origins program ((binaryLine .or initial.left initial.right).wires argument) = _
      intro argument
      refine Fin.cases ⟨leftNegated, by simpa [binaryLine] using leftOrigin⟩
        (fun remaining => ?_) argument
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      refine ⟨rightNegated, ?_⟩
      change origins program initial.right = _
      exact rightOrigin

/-- No charged predecessor feeds an initial charged gate. -/
theorem InitialChargedGate.not_uses
    {program : Program signature n g}
    (initial : InitialChargedGate program)
    (source : Fin g) :
    ¬UsesGate program source initial.gate := by
  intro uses
  unfold UsesGate at uses
  rw [initial.line_eq] at uses
  rcases uses with ⟨_, argument, negated, origin_eq⟩
  rcases binaryLine_wire_eq_left_or_right initial.op initial.left initial.right
      argument with argument_eq | argument_eq
  · rw [argument_eq] at origin_eq
    exact initial.left_simple.ne_gate negated source origin_eq
  · rw [argument_eq] at origin_eq
    exact initial.right_simple.ne_gate negated source origin_eq
/-- Every nonempty collection of charged gates has an initial member. -/
theorem exists_initialChargedGate
    (program : Program signature n g)
    (existsCharged : ∃ gate, ChargedGate program gate) :
    Nonempty (InitialChargedGate program) := by
  induction program with
  | empty =>
      obtain ⟨gate, _⟩ := existsCharged
      exact Fin.elim0 gate
  | @gate g program line inductionHypothesis =>
      by_cases priorExists : ∃ gate, ChargedGate program gate
      · obtain ⟨initial⟩ := inductionHypothesis priorExists
        exact ⟨
          { gate := initial.gate.castSucc
            op := initial.op
            left := initial.left.castSucc
            right := initial.right.castSucc
            line_eq := by
              rw [Program.lines_gate_castSucc, initial.line_eq]
              simpa only [Wire.Renaming.castSucc_apply] using
                binaryLine_mapWires initial.op initial.left initial.right
                  Wire.Renaming.castSucc
            left_simple := by
              rw [origins_gate_castSucc]
              exact initial.left_simple.map_castSucc
            right_simple := by
              rw [origins_gate_castSucc]
              exact initial.right_simple.map_castSucc }⟩
      · have lastCharged :
            ChargedGate (program.gate line) (Fin.last g) := by
          obtain ⟨gate, charged⟩ := existsCharged
          revert charged
          refine Fin.lastCases (fun charged => charged) (fun oldGate charged => ?_) gate
          exact False.elim (priorExists ⟨oldGate,
            by simpa [ChargedGate] using charged⟩)
        have simpleRaw (wire : Wire n g) :
            SimpleOrigin (origins program wire) := by
          have valid := origins_valid program wire
          generalize origin_eq : origins program wire = origin at valid ⊢
          cases origin with
          | constant value => trivial
          | wire negated originWire =>
              rcases valid with ⟨input, wire_eq⟩ | ⟨gate, wire_eq, charged⟩
              · exact ⟨input, wire_eq⟩
              · exact False.elim (priorExists ⟨gate, charged⟩)
        rcases line with ⟨op, wires⟩
        cases op with
        | false | true | id | not => simp_all [ChargedGate, binaryCost]
        | and =>
            change (Fin 2 → Wire n g) at wires
            exact ⟨
              { gate := Fin.last g
                op := .and
                left := (wires 0).castSucc
                right := (wires 1).castSucc
                line_eq := by
                  rw [Program.lines_gate_last, andLine_eq_binaryLine,
                    binaryLine_mapWires]
                  simp only [Wire.Renaming.castSucc_apply]
                left_simple := by
                  rw [origins_gate_castSucc]
                  exact (simpleRaw (wires 0)).map_castSucc
                right_simple := by
                  rw [origins_gate_castSucc]
                  exact (simpleRaw (wires 1)).map_castSucc }⟩
        | or =>
            change (Fin 2 → Wire n g) at wires
            exact ⟨
              { gate := Fin.last g
                op := .or
                left := (wires 0).castSucc
                right := (wires 1).castSucc
                line_eq := by
                  rw [Program.lines_gate_last, orLine_eq_binaryLine,
                    binaryLine_mapWires]
                  simp only [Wire.Renaming.castSucc_apply]
                left_simple := by
                  rw [origins_gate_castSucc]
                  exact (simpleRaw (wires 0)).map_castSucc
                right_simple := by
                  rw [origins_gate_castSucc]
                  exact (simpleRaw (wires 1)).map_castSucc }⟩

@[simp] theorem chargedGate_gate_castSucc
    (program : Program signature n g)
    (line : Line signature n g)
    (gate : Fin g) :
    ChargedGate (program.gate line) gate.castSucc ↔
      ChargedGate program gate := by
  simp [ChargedGate]

/-- Extend a direct-input edge through an appended program gate. -/
theorem ReadsInput.castSucc
    {program : Program signature n g}
    (reads : ReadsInput program gate input)
    (line : Line signature n g) :
    ReadsInput (program.gate line) gate.castSucc input := by
  rcases reads with ⟨charged, argument, negated, origin_eq⟩
  refine ⟨(chargedGate_gate_castSucc program line gate).2 charged, ?_⟩
  rw [Program.lines_gate_castSucc]
  refine ⟨argument, negated, ?_⟩
  simp only [Line.mapWires_wires, Wire.Renaming.castSucc_apply]
  rw [origins_gate_castSucc, origin_eq]
  simp only [ResidualValue.mapWires, Wire.Renaming.apply_input]

/-- Reflect a direct-input edge from an appended program to its prefix. -/
theorem ReadsInput.of_castSucc
    {program : Program signature n g}
    (reads : ReadsInput (program.gate line) gate.castSucc input) :
    ReadsInput program gate input := by
  unfold ReadsInput at reads ⊢
  rw [Program.lines_gate_castSucc] at reads
  simp only [Line.mapWires_op, Line.mapWires_wires,
    Wire.Renaming.castSucc_apply] at reads
  rcases reads with ⟨charged, argument, negated, origin_eq⟩
  refine ⟨by simpa [ChargedGate] using charged, ?_⟩
  rw [origins_gate_castSucc] at origin_eq
  have target_eq :
      (ResidualValue.wire negated (Wire.input (g := g) input)).mapWires
          Wire.Renaming.castSucc =
        ResidualValue.wire negated (Wire.input (g := g + 1) input) := by
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_input]
  rw [← target_eq] at origin_eq
  have castSuccInjective : Function.Injective
      (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1)) := by
    intro left right equal
    exact Fin.castSucc_injective _ (by
      simpa only [Wire.Renaming.castSucc_apply] using equal)
  exact ⟨argument, negated,
    ResidualValue.mapWires_injective castSuccInjective origin_eq⟩

/-- Expose the prefix-level literal read by a charged newly-appended gate. -/
theorem ReadsInput.of_last
    {program : Program signature n g}
    {line : Line signature n g}
    (reads : ReadsInput (program.gate line) (Fin.last g) input) :
    binaryCost line.op = 1 ∧
      ∃ argument negated,
        origins program (line.wires argument) =
          .wire negated (Wire.input input) := by
  unfold ReadsInput ChargedGate at reads
  rw [Program.lines_gate_last] at reads
  simp only [Line.mapWires_op, Line.mapWires_wires,
    Wire.Renaming.castSucc_apply] at reads
  rcases reads with ⟨charged, argument, negated, origin_eq⟩
  rw [origins_gate_castSucc] at origin_eq
  have target_eq :
      (ResidualValue.wire negated (Wire.input (g := g) input)).mapWires
          Wire.Renaming.castSucc =
        ResidualValue.wire negated (Wire.input (g := g + 1) input) := by
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_input]
  rw [← target_eq] at origin_eq
  have castSuccInjective : Function.Injective
      (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1)) := by
    intro left right equal
    exact Fin.castSucc_injective _ (by
      simpa only [Wire.Renaming.castSucc_apply] using equal)
  exact ⟨charged, argument, negated,
    ResidualValue.mapWires_injective castSuccInjective origin_eq⟩

/-- Reflect a single-input charged gate from an appended program to its prefix. -/
theorem ReadsOnlyInput.of_castSucc
    {program : Program signature n g}
    (reads : ReadsOnlyInput (program.gate line) gate.castSucc input) :
    ReadsOnlyInput program gate input := by
  unfold ReadsOnlyInput at reads ⊢
  rw [Program.lines_gate_castSucc] at reads
  simp only [Line.mapWires_op, Line.mapWires_wires,
    Wire.Renaming.castSucc_apply] at reads
  rcases reads with ⟨charged, allArguments⟩
  refine ⟨by simpa [ChargedGate] using charged, ?_⟩
  intro argument
  obtain ⟨negated, origin_eq⟩ := allArguments argument
  rw [origins_gate_castSucc] at origin_eq
  have target_eq :
      (ResidualValue.wire negated (Wire.input (g := g) input)).mapWires
          Wire.Renaming.castSucc =
        ResidualValue.wire negated (Wire.input (g := g + 1) input) := by
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_input]
  rw [← target_eq] at origin_eq
  have castSuccInjective : Function.Injective
      (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1)) := by
    intro left right equal
    exact Fin.castSucc_injective _ (by
      simpa only [Wire.Renaming.castSucc_apply] using equal)
  exact ⟨negated,
    ResidualValue.mapWires_injective castSuccInjective origin_eq⟩

/-- Expose the prefix-level literals of a newly appended single-input gate. -/
theorem ReadsOnlyInput.of_last
    {program : Program signature n g}
    {line : Line signature n g}
    (reads : ReadsOnlyInput (program.gate line) (Fin.last g) input) :
    binaryCost line.op = 1 ∧
      ∀ argument, ∃ negated,
        origins program (line.wires argument) =
          .wire negated (Wire.input input) := by
  unfold ReadsOnlyInput ChargedGate at reads
  rw [Program.lines_gate_last] at reads
  simp only [Line.mapWires_op, Line.mapWires_wires,
    Wire.Renaming.castSucc_apply] at reads
  rcases reads with ⟨charged, allArguments⟩
  refine ⟨charged, ?_⟩
  intro argument
  obtain ⟨negated, origin_eq⟩ := allArguments argument
  rw [origins_gate_castSucc] at origin_eq
  have target_eq :
      (ResidualValue.wire negated (Wire.input (g := g) input)).mapWires
          Wire.Renaming.castSucc =
        ResidualValue.wire negated (Wire.input (g := g + 1) input) := by
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_input]
  rw [← target_eq] at origin_eq
  have castSuccInjective : Function.Injective
      (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1)) := by
    intro left right equal
    exact Fin.castSucc_injective _ (by
      simpa only [Wire.Renaming.castSucc_apply] using equal)
  exact ⟨negated,
    ResidualValue.mapWires_injective castSuccInjective origin_eq⟩

/-- Build a direct-input edge into a newly appended charged gate. -/
theorem ReadsInput.last
    {program : Program signature n g}
    {line : Line signature n g}
    {input : Fin n}
    (charged : binaryCost line.op = 1)
    {argument : Fin (signature.Arity line.op)}
    {negated : Bool}
    (origin_eq : origins program (line.wires argument) =
      .wire negated (Wire.input input)) :
    ReadsInput (program.gate line) (Fin.last g) input := by
  refine ⟨?_, ?_⟩
  · simpa [ChargedGate] using charged
  · rw [Program.lines_gate_last]
    refine ⟨argument, negated, ?_⟩
    simp only [Line.mapWires_wires, Wire.Renaming.castSucc_apply]
    rw [origins_gate_castSucc, origin_eq]
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_input]

/-- Extend a charged edge through an appended program gate. -/
theorem UsesGate.castSucc
    {program : Program signature n g}
    (uses : UsesGate program source target)
    (line : Line signature n g) :
    UsesGate (program.gate line) source.castSucc target.castSucc := by
  rcases uses with ⟨charged, argument, negated, origin_eq⟩
  refine ⟨(chargedGate_gate_castSucc program line target).2 charged, ?_⟩
  rw [Program.lines_gate_castSucc]
  refine ⟨argument, negated, ?_⟩
  simp only [Line.mapWires_wires, Wire.Renaming.castSucc_apply]
  rw [origins_gate_castSucc, origin_eq]
  simp only [ResidualValue.mapWires, Wire.Renaming.apply_gate,
    Wire.Renaming.castSucc]

/-- Reflect a charged edge from an appended program to its prefix. -/
theorem UsesGate.of_castSucc
    {program : Program signature n g}
    (uses : UsesGate (program.gate line) source.castSucc target.castSucc) :
    UsesGate program source target := by
  unfold UsesGate at uses ⊢
  rw [Program.lines_gate_castSucc] at uses
  simp only [Line.mapWires_op, Line.mapWires_wires,
    Wire.Renaming.castSucc_apply] at uses
  rcases uses with ⟨charged, argument, negated, origin_eq⟩
  refine ⟨by simpa [ChargedGate] using charged, ?_⟩
  rw [origins_gate_castSucc] at origin_eq
  have target_eq :
      (ResidualValue.wire negated (Wire.gate (n := n) source)).mapWires
          Wire.Renaming.castSucc =
        ResidualValue.wire negated
          (Wire.gate (n := n) source.castSucc) := by
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_gate,
      Wire.Renaming.castSucc]
  rw [← target_eq] at origin_eq
  have castSuccInjective : Function.Injective
      (Wire.Renaming.castSucc : Wire.Renaming n g (g + 1)) := by
    intro left right equal
    exact Fin.castSucc_injective _ (by
      simpa only [Wire.Renaming.castSucc_apply] using equal)
  exact ⟨argument, negated,
    ResidualValue.mapWires_injective castSuccInjective origin_eq⟩

/-- Build a charged edge into a newly appended charged gate. -/
theorem UsesGate.last
    {program : Program signature n g}
    {line : Line signature n g}
    {source : Fin g}
    (charged : binaryCost line.op = 1)
    {argument : Fin (signature.Arity line.op)}
    {negated : Bool}
    (origin_eq : origins program (line.wires argument) =
      .wire negated (Wire.gate source)) :
    UsesGate (program.gate line) source.castSucc (Fin.last g) := by
  refine ⟨?_, ?_⟩
  · simpa [ChargedGate] using charged
  · rw [Program.lines_gate_last]
    refine ⟨argument, negated, ?_⟩
    simp only [Line.mapWires_wires, Wire.Renaming.castSucc_apply]
    rw [origins_gate_castSucc, origin_eq]
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_gate,
      Wire.Renaming.castSucc]

private theorem mappedOrigin_ne_last
    (value : ResidualValue n g)
    (negated : Bool) :
    value.mapWires Wire.Renaming.castSucc ≠
      .wire negated (Wire.gate (Fin.last g)) := by
  cases value with
  | constant value => simp [ResidualValue.mapWires]
  | wire sign originWire =>
      simp only [ResidualValue.mapWires, Wire.Renaming.castSucc_apply]
      intro equal
      injection equal with _ wires
      have impossible : originWire.castSucc = Fin.last (n + g) := by
        simpa only [Fin.natAdd_last] using wires
      exact Fin.castSucc_ne_last originWire impossible

/-- A charged dependency edge cannot be a self-loop. -/
theorem UsesGate.ne
    {program : Program signature n g}
    {source target : Fin g}
    (uses : UsesGate program source target) :
    source ≠ target := by
  intro equal
  subst target
  induction program with
  | empty => exact Fin.elim0 source
  | @gate g program line inductionHypothesis =>
      revert uses
      refine Fin.lastCases (fun uses => ?_) (fun oldGate uses => ?_) source
      · unfold UsesGate at uses
        rw [Program.lines_gate_last] at uses
        simp only [Line.mapWires_op, Line.mapWires_wires,
          Wire.Renaming.castSucc_apply] at uses
        rcases uses with ⟨_, argument, negated, origin_eq⟩
        rw [origins_gate_castSucc] at origin_eq
        exact mappedOrigin_ne_last
          (origins program (line.wires argument)) negated origin_eq
      · exact inductionHypothesis uses.of_castSucc

end DeMorgan
end Algebraic

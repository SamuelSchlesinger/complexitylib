/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Dependency
public import Complexitylib.Algebraic.Basis.DeMorgan.Restriction

/-!
# Structural facts about De Morgan restriction

This module connects the origin graph to the concrete partial evaluator.  It
contains no circuit-specific XOR reasoning: the results say when a fixed input
turns an origin into a constant and how facts about an earlier source gate are
preserved while later gates are processed.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

namespace ProgramRestriction

/-- Following a constant origin produces that same constant. -/
theorem value_eq_constant_of_constant_origin
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : ProgramRestriction source selected fixedValue)
    {sourceWire : Wire (n + 1) g}
    {value : Bool}
    (origin_eq : origins source sourceWire = .constant value) :
    restriction.values sourceWire = .constant value := by
  rw [restriction.followsOrigins sourceWire, origin_eq]
  rfl

/-- Following a signed occurrence of the selected input produces a constant. -/
theorem value_eq_constant_of_selected_origin
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : ProgramRestriction source selected fixedValue)
    {sourceWire : Wire (n + 1) g}
    {negated : Bool}
    (origin_eq : origins source sourceWire =
      .wire negated (Wire.input selected)) :
    restriction.values sourceWire =
      .constant (if negated then !fixedValue else fixedValue) := by
  rw [restriction.followsOrigins sourceWire, origin_eq]
  cases negated <;> simp [restriction.selected_eq, ResidualValue.negate]

/-- Following a signed charged-gate origin preserves a known constant value. -/
theorem value_eq_constant_of_gate_origin
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : ProgramRestriction source selected fixedValue)
    {sourceWire : Wire (n + 1) g}
    {gate : Fin g}
    {negated value : Bool}
    (origin_eq : origins source sourceWire =
      .wire negated (Wire.gate gate))
    (gate_eq : restriction.values (Wire.gate gate) = .constant value) :
    restriction.values sourceWire =
      .constant (if negated then !value else value) := by
  rw [restriction.followsOrigins sourceWire, origin_eq]
  cases negated <;> simp [gate_eq, ResidualValue.negate]

end ProgramRestriction

/-- Deletion of an earlier charged gate survives processing one later line. -/
theorem restrictProgram_deleted_castSucc
    (source : Program signature (n + 1) g)
    (line : Line signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    {gate : Fin g}
    (deleted : gate ∈ (restrictProgram selected fixedValue source).deleted) :
    gate.castSucc ∈
      (restrictProgram selected fixedValue (source.gate line)).deleted := by
  classical
  rcases line with ⟨op, wires⟩
  cases op with
  | false | true | id | not =>
      simp only [restrictProgram]
      change gate.castSucc ∈
        (restrictProgram selected fixedValue source).deleted.map
          Fin.castSuccEmb
      exact Finset.mem_map.mpr ⟨gate, deleted, rfl⟩
  | and | or =>
      simp only [restrictProgram, ProgramRestriction.appendBinary]
      split <;>
        simp_all [ProgramRestriction.deleteLast,
          ProgramRestriction.retainLast]

/-- A constant value of an earlier source wire remains constant after one line. -/
theorem restrictProgram_value_castSucc_eq_constant
    (source : Program signature (n + 1) g)
    (line : Line signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue value : Bool)
    {sourceWire : Wire (n + 1) g}
    (constant :
      (restrictProgram selected fixedValue source).values sourceWire =
        .constant value) :
    (restrictProgram selected fixedValue (source.gate line)).values
        sourceWire.castSucc = .constant value := by
  classical
  rcases line with ⟨op, wires⟩
  cases op with
  | false | true | id | not =>
      simp only [restrictProgram]
      dsimp [ProgramRestriction.reuseLast]
      simpa only [Wire.lastCases_castSucc] using constant
  | and | or =>
      simp only [restrictProgram, ProgramRestriction.appendBinary]
      split <;>
        simp_all [ProgramRestriction.deleteLast,
          ProgramRestriction.retainLast, ResidualValue.mapWires]

/-- Processing a later line cannot turn an earlier nonconstant value constant. -/
theorem restrictProgram_value_eq_constant_of_castSucc
    (source : Program signature (n + 1) g)
    (line : Line signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue value : Bool)
    {sourceWire : Wire (n + 1) g}
    (constant :
      (restrictProgram selected fixedValue (source.gate line)).values
          sourceWire.castSucc = .constant value) :
    (restrictProgram selected fixedValue source).values sourceWire =
      .constant value := by
  classical
  rcases line with ⟨op, wires⟩
  cases op with
  | false | true | id | not =>
      dsimp [restrictProgram, ProgramRestriction.reuseLast] at constant
      rw [Wire.lastCases_castSucc] at constant
      exact constant
  | and | or =>
      simp only [restrictProgram, ProgramRestriction.appendBinary] at constant
      split at constant
      · dsimp [ProgramRestriction.deleteLast] at constant
        rw [Wire.lastCases_castSucc] at constant
        exact constant
      · dsimp [ProgramRestriction.retainLast] at constant
        generalize prior_eq :
          (restrictProgram selected fixedValue source).values sourceWire =
            priorValue at constant ⊢
        cases priorValue <;> simp_all [ResidualValue.mapWires]

private theorem restrictProgram_last_and_deleted_of_simplifies
    (source : Program signature (n + 1) g)
    (wires : Fin 2 → Wire (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    (result : ResidualValue n
      (restrictProgram selected fixedValue source).gateCount)
    (simplifies :
      simplifyBinary .and
          ((restrictProgram selected fixedValue source).values (wires 0))
          ((restrictProgram selected fixedValue source).values (wires 1)) =
        some result) :
    Fin.last g ∈ (restrictProgram selected fixedValue
      (source.gate ⟨Op.and, wires⟩)).deleted := by
  let prior := restrictProgram selected fixedValue source
  simp only [restrictProgram, ProgramRestriction.appendBinary]
  split
  · simp [ProgramRestriction.deleteLast]
  · rename_i actual
    have actualSimplifies :
        simplifyBinary .and (prior.values (wires 0))
            (prior.values (wires 1)) = some result := by
      simpa [prior] using simplifies
    have impossible : (none : Option (ResidualValue n prior.gateCount)) =
        some result := actual.symm.trans actualSimplifies
    contradiction

private theorem restrictProgram_last_or_deleted_of_simplifies
    (source : Program signature (n + 1) g)
    (wires : Fin 2 → Wire (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    (result : ResidualValue n
      (restrictProgram selected fixedValue source).gateCount)
    (simplifies :
      simplifyBinary .or
          ((restrictProgram selected fixedValue source).values (wires 0))
          ((restrictProgram selected fixedValue source).values (wires 1)) =
        some result) :
    Fin.last g ∈ (restrictProgram selected fixedValue
      (source.gate ⟨Op.or, wires⟩)).deleted := by
  let prior := restrictProgram selected fixedValue source
  simp only [restrictProgram, ProgramRestriction.appendBinary]
  split
  · simp [ProgramRestriction.deleteLast]
  · rename_i actual
    have actualSimplifies :
        simplifyBinary .or (prior.values (wires 0))
            (prior.values (wires 1)) = some result := by
      simpa [prior] using simplifies
    have impossible : (none : Option (ResidualValue n prior.gateCount)) =
        some result := actual.symm.trans actualSimplifies
    contradiction

/-- A charged gate is deleted whenever one of its final residual arguments is constant. -/
theorem restrictProgram_deleted_of_constant_argument
    (program : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool) :
    ∀ gate,
      ChargedGate program gate →
      (∃ argument value,
        (restrictProgram selected fixedValue program).values
            ((program.lines gate).wires argument) = .constant value) →
      gate ∈ (restrictProgram selected fixedValue program).deleted := by
  induction program with
  | empty =>
      intro impossible
      exact Fin.elim0 impossible
  | @gate g source line inductionHypothesis =>
      intro target
      revert target
      refine Fin.lastCases ?_ (fun oldGate => ?_)
      · intro charged constantArgument
        rw [Program.lines_gate_last] at constantArgument
        simp only [Line.mapWires_op, Line.mapWires_wires,
          Wire.Renaming.castSucc_apply] at constantArgument
        obtain ⟨argument, value, finalConstant⟩ := constantArgument
        have priorConstant := restrictProgram_value_eq_constant_of_castSucc
          source line selected fixedValue value finalConstant
        rcases line with ⟨op, wires⟩
        cases op with
        | false | true | id | not => simp_all [ChargedGate, binaryCost]
        | and =>
            change (Fin 2 → Wire (n + 1) g) at wires
            let prior := restrictProgram selected fixedValue source
            obtain ⟨result, simplifies⟩ :=
              simplifyBinary_of_argument_constant .and
                (fun index => prior.values (wires index)) argument value
                (by simpa [prior] using priorConstant)
            exact restrictProgram_last_and_deleted_of_simplifies source wires
              selected fixedValue result (by simpa [prior] using simplifies)
        | or =>
            change (Fin 2 → Wire (n + 1) g) at wires
            let prior := restrictProgram selected fixedValue source
            obtain ⟨result, simplifies⟩ :=
              simplifyBinary_of_argument_constant .or
                (fun index => prior.values (wires index)) argument value
                (by simpa [prior] using priorConstant)
            exact restrictProgram_last_or_deleted_of_simplifies source wires
              selected fixedValue result (by simpa [prior] using simplifies)
      · intro charged constantArgument
        have priorCharged : ChargedGate source oldGate := by
          simpa using charged
        rw [Program.lines_gate_castSucc] at constantArgument
        simp only [Line.mapWires_op, Line.mapWires_wires,
          Wire.Renaming.castSucc_apply] at constantArgument
        obtain ⟨argument, value, finalConstant⟩ := constantArgument
        have priorConstant := restrictProgram_value_eq_constant_of_castSucc
          source line selected fixedValue value finalConstant
        have priorDeleted := inductionHypothesis oldGate priorCharged
          ⟨argument, value, priorConstant⟩
        exact restrictProgram_deleted_castSucc source line selected fixedValue
          priorDeleted

/-- An initial gate with a constant left origin is deleted by every restriction. -/
theorem restrictProgram_deleted_of_initial_constant_left
    (program : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    (initial : InitialChargedGate program)
    {value : Bool}
    (origin_eq : origins program initial.left = .constant value) :
    initial.gate ∈ (restrictProgram selected fixedValue program).deleted := by
  apply restrictProgram_deleted_of_constant_argument program selected fixedValue
    initial.gate initial.charged
  rw [initial.line_eq]
  cases initial.op with
  | and =>
      change ∃ argument : Fin 2, ∃ value,
        (restrictProgram selected fixedValue program).values
          ((binaryLine .and initial.left initial.right).wires argument) =
            .constant value
      refine ⟨0, value, ?_⟩
      simpa [binaryLine] using
        (restrictProgram selected fixedValue program).value_eq_constant_of_constant_origin
          origin_eq
  | or =>
      change ∃ argument : Fin 2, ∃ value,
        (restrictProgram selected fixedValue program).values
          ((binaryLine .or initial.left initial.right).wires argument) =
            .constant value
      refine ⟨0, value, ?_⟩
      simpa [binaryLine] using
        (restrictProgram selected fixedValue program).value_eq_constant_of_constant_origin
          origin_eq

/-- An initial gate with a constant right origin is deleted by every restriction. -/
theorem restrictProgram_deleted_of_initial_constant_right
    (program : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    (initial : InitialChargedGate program)
    {value : Bool}
    (origin_eq : origins program initial.right = .constant value) :
    initial.gate ∈ (restrictProgram selected fixedValue program).deleted := by
  apply restrictProgram_deleted_of_constant_argument program selected fixedValue
    initial.gate initial.charged
  rw [initial.line_eq]
  cases initial.op with
  | and =>
      change ∃ argument : Fin 2, ∃ value,
        (restrictProgram selected fixedValue program).values
          ((binaryLine .and initial.left initial.right).wires argument) =
            .constant value
      refine ⟨1, value, ?_⟩
      change (restrictProgram selected fixedValue program).values initial.right = _
      exact (restrictProgram selected fixedValue program).value_eq_constant_of_constant_origin
        origin_eq
  | or =>
      change ∃ argument : Fin 2, ∃ value,
        (restrictProgram selected fixedValue program).values
          ((binaryLine .or initial.left initial.right).wires argument) =
            .constant value
      refine ⟨1, value, ?_⟩
      change (restrictProgram selected fixedValue program).values initial.right = _
      exact (restrictProgram selected fixedValue program).value_eq_constant_of_constant_origin
        origin_eq

/-- Fixing an input deletes every charged gate that reads that input directly. -/
theorem restrictProgram_deleted_of_readsInput
    (program : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    {gate : Fin g}
    (reads : ReadsInput program gate selected) :
    gate ∈ (restrictProgram selected fixedValue program).deleted := by
  rcases reads with ⟨charged, argument, negated, origin_eq⟩
  let restriction := restrictProgram selected fixedValue program
  have constant := restriction.value_eq_constant_of_selected_origin origin_eq
  exact restrictProgram_deleted_of_constant_argument program selected fixedValue
    gate charged ⟨argument, _, by simpa [restriction] using constant⟩

/-- A charged gate whose arguments are literals of one input is always deleted. -/
theorem restrictProgram_deleted_of_readsOnlyInput
    (program : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    (input : Fin (n + 1)) :
    ∀ gate,
      ReadsOnlyInput program gate input →
      gate ∈ (restrictProgram selected fixedValue program).deleted := by
  induction program with
  | empty =>
      intro impossible
      exact Fin.elim0 impossible
  | @gate g source line inductionHypothesis =>
      intro target reads
      revert reads
      refine Fin.lastCases (fun reads => ?_) (fun oldGate reads => ?_) target
      · obtain ⟨lineCharged, allArguments⟩ := reads.of_last
        rcases line with ⟨op, wires⟩
        cases op with
        | false | true | id | not => simp_all [binaryCost]
        | and =>
            change (Fin 2 → Wire (n + 1) g) at wires
            obtain ⟨leftNegated, leftOrigin⟩ := allArguments (0 : Fin 2)
            obtain ⟨rightNegated, rightOrigin⟩ := allArguments (1 : Fin 2)
            let prior := restrictProgram selected fixedValue source
            let common := prior.values (Wire.input input)
            have leftValue : prior.values (wires 0) =
                if leftNegated then common.negate else common := by
              rw [prior.followsOrigins, leftOrigin]
              cases leftNegated <;> rfl
            have rightValue : prior.values (wires 1) =
                if rightNegated then common.negate else common := by
              rw [prior.followsOrigins, rightOrigin]
              cases rightNegated <;> rfl
            obtain ⟨result, simplifies⟩ := simplifyBinary_of_common_value
              .and common leftNegated rightNegated
            apply restrictProgram_last_and_deleted_of_simplifies source wires
              selected fixedValue result
            rw [leftValue, rightValue]
            exact simplifies
        | or =>
            change (Fin 2 → Wire (n + 1) g) at wires
            obtain ⟨leftNegated, leftOrigin⟩ := allArguments (0 : Fin 2)
            obtain ⟨rightNegated, rightOrigin⟩ := allArguments (1 : Fin 2)
            let prior := restrictProgram selected fixedValue source
            let common := prior.values (Wire.input input)
            have leftValue : prior.values (wires 0) =
                if leftNegated then common.negate else common := by
              rw [prior.followsOrigins, leftOrigin]
              cases leftNegated <;> rfl
            have rightValue : prior.values (wires 1) =
                if rightNegated then common.negate else common := by
              rw [prior.followsOrigins, rightOrigin]
              cases rightNegated <;> rfl
            obtain ⟨result, simplifies⟩ := simplifyBinary_of_common_value
              .or common leftNegated rightNegated
            apply restrictProgram_last_or_deleted_of_simplifies source wires
              selected fixedValue result
            rw [leftValue, rightValue]
            exact simplifies
      · have priorDeleted := inductionHypothesis oldGate reads.of_castSucc
        exact restrictProgram_deleted_castSucc source line selected fixedValue
          priorDeleted

/-- A constant deleted source forces every charged successor to simplify. -/
theorem restrictProgram_deleted_of_usesGate_constant
    (program : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    {source target : Fin g}
    (uses : UsesGate program source target)
    {value : Bool}
    (sourceConstant :
      (restrictProgram selected fixedValue program).values
          (Wire.gate source) = .constant value) :
    target ∈ (restrictProgram selected fixedValue program).deleted := by
  rcases uses with ⟨charged, argument, negated, origin_eq⟩
  let restriction := restrictProgram selected fixedValue program
  have constant := restriction.value_eq_constant_of_gate_origin
    origin_eq sourceConstant
  exact restrictProgram_deleted_of_constant_argument program selected fixedValue
    target charged ⟨argument, _, by simpa [restriction] using constant⟩

private theorem restrictProgram_last_and_of_simplifies
    (source : Program signature (n + 1) g)
    (wires : Fin 2 → Wire (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    (outputValue : Bool)
    (simplifies :
      simplifyBinary .and
          ((restrictProgram selected fixedValue source).values (wires 0))
          ((restrictProgram selected fixedValue source).values (wires 1)) =
        some (.constant outputValue)) :
    let restricted := restrictProgram selected fixedValue
      (source.gate ⟨Op.and, wires⟩)
    Fin.last g ∈ restricted.deleted ∧
      restricted.values (Wire.gate (Fin.last g)) =
        .constant outputValue := by
  let prior := restrictProgram selected fixedValue source
  dsimp only
  simp only [restrictProgram, ProgramRestriction.appendBinary]
  split
  · rename_i value actual
    have actualSimplifies :
        simplifyBinary .and (prior.values (wires 0))
            (prior.values (wires 1)) = some (.constant outputValue) := by
      simpa [prior] using simplifies
    have value_eq : value = .constant outputValue :=
      Option.some.inj (actual.symm.trans actualSimplifies)
    subst value
    constructor
    · simp [ProgramRestriction.deleteLast]
    · simp [ProgramRestriction.deleteLast]
  · rename_i actual
    have actualSimplifies :
        simplifyBinary .and (prior.values (wires 0))
            (prior.values (wires 1)) = some (.constant outputValue) := by
      simpa [prior] using simplifies
    have impossible : (none : Option (ResidualValue n prior.gateCount)) =
        some (.constant outputValue) := actual.symm.trans actualSimplifies
    contradiction

private theorem restrictProgram_last_or_of_simplifies
    (source : Program signature (n + 1) g)
    (wires : Fin 2 → Wire (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool)
    (outputValue : Bool)
    (simplifies :
      simplifyBinary .or
          ((restrictProgram selected fixedValue source).values (wires 0))
          ((restrictProgram selected fixedValue source).values (wires 1)) =
        some (.constant outputValue)) :
    let restricted := restrictProgram selected fixedValue
      (source.gate ⟨Op.or, wires⟩)
    Fin.last g ∈ restricted.deleted ∧
      restricted.values (Wire.gate (Fin.last g)) =
        .constant outputValue := by
  let prior := restrictProgram selected fixedValue source
  dsimp only
  simp only [restrictProgram, ProgramRestriction.appendBinary]
  split
  · rename_i value actual
    have actualSimplifies :
        simplifyBinary .or (prior.values (wires 0))
            (prior.values (wires 1)) = some (.constant outputValue) := by
      simpa [prior] using simplifies
    have value_eq : value = .constant outputValue :=
      Option.some.inj (actual.symm.trans actualSimplifies)
    subst value
    constructor
    · simp [ProgramRestriction.deleteLast]
    · simp [ProgramRestriction.deleteLast]
  · rename_i actual
    have actualSimplifies :
        simplifyBinary .or (prior.values (wires 0))
            (prior.values (wires 1)) = some (.constant outputValue) := by
      simpa [prior] using simplifies
    have impossible : (none : Option (ResidualValue n prior.gateCount)) =
        some (.constant outputValue) := actual.symm.trans actualSimplifies
    contradiction

/--
A restriction that both deletes a chosen charged gate and makes its source value
constant.  The latter fact is what forces a charged successor to simplify.
-/
structure GateAnnihilation
    (source : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (gate : Fin g) where
  /-- Value assigned to the selected input. -/
  fixedValue : Bool
  /-- Constant value produced by the annihilated gate. -/
  outputValue : Bool
  /-- The gate is recorded among the deleted charged gates. -/
  deleted : gate ∈ (restrictProgram selected fixedValue source).deleted
  /-- Its source wire is represented by the stated constant. -/
  value_eq :
    (restrictProgram selected fixedValue source).values (Wire.gate gate) =
      .constant outputValue

/-- A direct input of the newest charged gate can be set to annihilate it. -/
private theorem annihilate_last_of_readsInput
    (source : Program signature (n + 1) g)
    (line : Line signature (n + 1) g)
    (selected : Fin (n + 1))
    (reads : ReadsInput (source.gate line) (Fin.last g) selected) :
    Nonempty (GateAnnihilation (source.gate line) selected (Fin.last g)) := by
  obtain ⟨charged, argument, negated, origin_eq⟩ := reads.of_last
  rcases line with ⟨op, wires⟩
  cases op with
  | false | true | id | not => simp_all [binaryCost]
  | and =>
      change (Fin 2 → Wire (n + 1) g) at wires
      let prior := restrictProgram selected negated source
      have argumentConstant :
          prior.values (wires argument) = .constant false := by
        have resolved := prior.value_eq_constant_of_selected_origin origin_eq
        cases negated <;> simpa [prior] using resolved
      have simplifies :
          simplifyBinary .and (prior.values (wires 0))
              (prior.values (wires 1)) = some (.constant false) :=
        simplifyBinary_and_of_argument_false
          (fun index => prior.values (wires index)) argument argumentConstant
      have restricted := restrictProgram_last_and_of_simplifies source wires
        selected negated false (by simpa [prior] using simplifies)
      refine ⟨
        { fixedValue := negated
          outputValue := false
          deleted := restricted.1
          value_eq := restricted.2 }⟩
  | or =>
      change (Fin 2 → Wire (n + 1) g) at wires
      let fixedValue := !negated
      let prior := restrictProgram selected fixedValue source
      have argumentConstant :
          prior.values (wires argument) = .constant true := by
        have resolved := prior.value_eq_constant_of_selected_origin origin_eq
        cases negated <;> simpa [prior, fixedValue] using resolved
      have simplifies :
          simplifyBinary .or (prior.values (wires 0))
              (prior.values (wires 1)) = some (.constant true) :=
        simplifyBinary_or_of_argument_true
          (fun index => prior.values (wires index)) argument argumentConstant
      have restricted := restrictProgram_last_or_of_simplifies source wires
        selected fixedValue true (by simpa [prior] using simplifies)
      refine ⟨
        { fixedValue := fixedValue
          outputValue := true
          deleted := restricted.1
          value_eq := restricted.2 }⟩

/-- Every charged gate directly reading an input admits an annihilating fix. -/
theorem annihilate_of_readsInput
    (program : Program signature (n + 1) g)
    (selected : Fin (n + 1)) :
    ∀ gate, ReadsInput program gate selected →
      Nonempty (GateAnnihilation program selected gate) := by
  induction program with
  | empty =>
      intro impossible
      exact Fin.elim0 impossible
  | @gate g source line inductionHypothesis =>
      intro target reads
      revert reads
      refine Fin.lastCases ?_ (fun oldGate => ?_) target
      · exact annihilate_last_of_readsInput source line selected
      · intro reads
        obtain ⟨prior⟩ := inductionHypothesis oldGate reads.of_castSucc
        exact ⟨
          { fixedValue := prior.fixedValue
            outputValue := prior.outputValue
            deleted := restrictProgram_deleted_castSucc source line selected
              prior.fixedValue prior.deleted
            value_eq := by
              have lifted := restrictProgram_value_castSucc_eq_constant
                source line selected prior.fixedValue prior.outputValue
                prior.value_eq
              exact lifted }⟩

end DeMorgan
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Residual
public import Complexitylib.Algebraic.Support

/-!
# Charged origins in De Morgan programs

`origins` follows zero-cost constants, identities, and negations, but
stops at an input or an AND/OR gate.  It is the structural view used by gate
elimination: zero-cost chains disappear without changing the underlying
`Program`/`Circuit` representation.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/--
Evaluate one source line symbolically from already-computed origins. `fresh`
names the line's own output and is used exactly for charged binary operations.
-/
def lineOrigin
    (line : Line signature n g)
    (values : Wire n g → ResidualValue n h)
    (fresh : Wire n h) : ResidualValue n h :=
  match line with
  | ⟨.false, _⟩ => .constant false
  | ⟨.true, _⟩ => .constant true
  | ⟨.id, wires⟩ => values (wires ⟨0, by decide⟩)
  | ⟨.not, wires⟩ => (values (wires ⟨0, by decide⟩)).negate
  | ⟨.and, _⟩ | ⟨.or, _⟩ => .wire false fresh

@[simp] theorem lineOrigin_not
    (wires : Fin 1 → Wire n g)
    (values : Wire n g → ResidualValue n h)
    (fresh : Wire n h) :
    lineOrigin ⟨Op.not, wires⟩ values fresh =
      (values (wires 0)).negate := rfl

/-- The charged origin of each internal gate output. -/
def gateOrigins :
    (program : Program signature n g) → Fin g → ResidualValue n g
  | .empty, gate => Fin.elim0 gate
  | @Program.gate _ _ g program line, gate =>
      let prior : Fin g → ResidualValue n (g + 1) := fun oldGate =>
        (gateOrigins program oldGate).mapWires Wire.Renaming.castSucc
      let values : Wire n g → ResidualValue n (g + 1) :=
        Fin.addCases
          (fun input => .wire false (Wire.input input))
          prior
      let fresh : Wire n (g + 1) := Wire.gate (Fin.last g)
      Fin.lastCases (lineOrigin line values fresh) prior gate

/--
The charged origin of every wire: a constant, a signed input, or a signed
AND/OR-gate output.  Free internal gates are followed transitively.
-/
def origins
    (program : Program signature n g) : Wire n g → ResidualValue n g :=
  Fin.addCases
    (fun input => .wire false (Wire.input input))
    (gateOrigins program)

@[simp] theorem origins_input
    (program : Program signature n g)
    (input : Fin n) :
    origins program (Wire.input input) =
      .wire false (Wire.input input) := by
  simp [origins]

@[simp] theorem origins_gateWire
    (program : Program signature n g)
    (gate : Fin g) :
    origins program (Wire.gate gate) = gateOrigins program gate := by
  simp [origins]

/-- The origin map lifted through one appended gate. -/
@[simp] theorem liftedOrigins_apply
    (program : Program signature n g)
    (wire : Wire n g) :
    Fin.addCases
        (fun input => ResidualValue.wire false (Wire.input input))
        (fun oldGate =>
          (gateOrigins program oldGate).mapWires Wire.Renaming.castSucc)
        wire =
      (origins program wire).mapWires Wire.Renaming.castSucc := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · rw [Fin.addCases_left, origins_input]
    simp only [ResidualValue.mapWires, Wire.Renaming.apply_input]
  · simp [origins]

@[simp] theorem gateOrigins_gate_castSucc
    (program : Program signature n g)
    (line : Line signature n g)
    (gate : Fin g) :
    gateOrigins (program.gate line) gate.castSucc =
      (gateOrigins program gate).mapWires Wire.Renaming.castSucc := by
  simp [gateOrigins]

@[simp] theorem gateOrigins_gate_last
    (program : Program signature n g)
    (line : Line signature n g) :
    gateOrigins (program.gate line) (Fin.last g) =
      lineOrigin line
        (Fin.addCases
          (fun input => .wire false (Wire.input input))
          (fun oldGate =>
            (gateOrigins program oldGate).mapWires Wire.Renaming.castSucc))
        (Wire.gate (Fin.last g)) := by
  simp [gateOrigins]

@[simp] theorem origins_gate_castSucc
    (program : Program signature n g)
    (line : Line signature n g)
    (wire : Wire n g) :
    origins (program.gate line) wire.castSucc =
      (origins program wire).mapWires Wire.Renaming.castSucc := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · have castInput :
        (Wire.input (g := g) input).castSucc =
          Wire.input (g := g + 1) input := Fin.castSucc_castAdd input
    rw [castInput, origins_input, origins_input,
      ResidualValue.mapWires, Wire.Renaming.castSucc_apply, castInput]
  · have castGate :
        (Wire.gate (n := n) gate).castSucc =
          Wire.gate (n := n) gate.castSucc := Fin.natAdd_castSucc.symm
    rw [castGate, origins_gateWire, origins_gateWire,
      gateOrigins_gate_castSucc]

theorem origins_gate_last
    (program : Program signature n g)
    (line : Line signature n g) :
    origins (program.gate line) (Wire.gate (Fin.last g)) =
      lineOrigin line
        (Fin.addCases
          (fun input => .wire false (Wire.input input))
          (fun oldGate =>
            (gateOrigins program oldGate).mapWires Wire.Renaming.castSucc))
        (Wire.gate (Fin.last g)) := by
  rw [origins_gateWire, gateOrigins_gate_last]

/-- A charged newly-appended gate is its own origin. -/
theorem origins_gateWire_last_of_charged
    (program : Program signature n g)
    (line : Line signature n g)
    (charged : binaryCost line.op = 1) :
    origins (program.gate line) (Wire.gate (Fin.last g)) =
      .wire false (Wire.gate (Fin.last g)) := by
  rw [origins_gate_last]
  rcases line with ⟨op, wires⟩
  cases op <;> simp_all [lineOrigin]

/-- `Fin.last` spelling of `origins_gateWire_last_of_charged`. -/
theorem origins_last_of_charged
    (program : Program signature n g)
    (line : Line signature n g)
    (charged : binaryCost line.op = 1) :
    origins (program.gate line) (Fin.last (n + g)) =
      .wire false (Fin.last (n + g)) := by
  rw [← Fin.natAdd_last (n := n) (m := g)]
  exact origins_gateWire_last_of_charged program line charged

theorem origins_gateWire_last_false
    (program : Program signature n g)
    (wires : Fin 0 → Wire n g) :
    origins (program.gate ⟨Op.false, wires⟩)
      (Wire.gate (Fin.last g)) = .constant false := by
  rw [origins_gate_last]
  rfl

theorem origins_gateWire_last_true
    (program : Program signature n g)
    (wires : Fin 0 → Wire n g) :
    origins (program.gate ⟨Op.true, wires⟩)
      (Wire.gate (Fin.last g)) = .constant true := by
  rw [origins_gate_last]
  rfl

theorem origins_gateWire_last_id
    (program : Program signature n g)
    (wires : Fin 1 → Wire n g) :
    origins (program.gate ⟨Op.id, wires⟩)
      (Wire.gate (Fin.last g)) =
      (origins program (wires 0)).mapWires Wire.Renaming.castSucc := by
  rw [origins_gate_last]
  exact liftedOrigins_apply program (wires 0)

theorem origins_gateWire_last_not
    (program : Program signature n g)
    (wires : Fin 1 → Wire n g) :
    origins (program.gate ⟨Op.not, wires⟩)
      (Wire.gate (Fin.last g)) =
      ((origins program (wires 0)).mapWires
        Wire.Renaming.castSucc).negate := by
  rw [origins_gate_last]
  rw [lineOrigin_not, liftedOrigins_apply]

/-- A residual value's structural input support. -/
def originSupport
    (program : Program signature n g) :
    ResidualValue n g → Finset (Fin n) := fun value =>
  match value with
  | .constant _ => ∅
  | .wire _ wire => program.wireSupport wire

@[simp] theorem originSupport_constant
    (program : Program signature n g)
    (value : Bool) :
    originSupport program
      (ResidualValue.constant value : ResidualValue n g) = ∅ :=
  rfl

@[simp] theorem originSupport_wire
    (program : Program signature n g)
    (negated : Bool)
    (wire : Wire n g) :
    originSupport program (ResidualValue.wire negated wire) =
      program.wireSupport wire := rfl

@[simp] theorem originSupport_negate
    (value : ResidualValue n g)
    (program : Program signature n g) :
    originSupport program value.negate = originSupport program value := by
  cases value <;> rfl

@[simp] theorem originSupport_map_castSucc
    (value : ResidualValue n g)
    (program : Program signature n g)
    (line : Line signature n g) :
    originSupport (program.gate line)
        (value.mapWires Wire.Renaming.castSucc) =
      originSupport program value := by
  cases value with
  | constant value => rfl
  | wire negated wire =>
      simp [ResidualValue.mapWires]

@[simp] theorem eval_map_castSucc
    (value : ResidualValue n g)
    (program : Program signature n g)
    (line : Line signature n g)
    (input : Fin n → Bool) :
    (value.mapWires Wire.Renaming.castSucc).eval
        (program.gate line) input =
      value.eval program input := by
  apply ResidualValue.eval_mapWires
  intro sourceWire
  simpa only [Wire.Renaming.castSucc_apply] using
    Program.trace_gate_castSucc program line interpretation input sourceWire

/-- Following free gates preserves structural input support exactly. -/
theorem origins_support
    (program : Program signature n g)
    (wire : Wire n g) :
    originSupport program (origins program wire) =
      program.wireSupport wire := by
  induction program with
  | empty =>
      refine Fin.addCases (fun input => ?_)
        (fun impossible => Fin.elim0 impossible) wire
      rw [origins_input, originSupport_wire,
        Program.wireSupport_input]
  | @gate g program line inductionHypothesis =>
      refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
      · rw [origins_input, originSupport_wire,
          Program.wireSupport_input]
      · refine Fin.lastCases ?_ (fun oldGate => ?_) gate
        · rw [origins_gateWire, gateOrigins_gate_last,
            Program.wireSupport_gate]
          simp only [Program.gateSupport, Fin.lastCases_last]
          rcases line with ⟨op, wires⟩
          cases op with
          | false =>
              rw [lineOrigin, originSupport_constant]
              change ∅ = Finset.univ.biUnion
                (fun argument : Fin 0 => program.wireSupport (wires argument))
              simp
          | true =>
              rw [lineOrigin, originSupport_constant]
              change ∅ = Finset.univ.biUnion
                (fun argument : Fin 0 => program.wireSupport (wires argument))
              simp
          | id =>
              rw [lineOrigin, liftedOrigins_apply,
                originSupport_map_castSucc, inductionHypothesis]
              change program.wireSupport (wires ⟨0, by decide⟩) =
                Finset.univ.biUnion
                  (fun argument : Fin 1 => program.wireSupport (wires argument))
              simp
          | not =>
              rw [lineOrigin, liftedOrigins_apply,
                originSupport_negate, originSupport_map_castSucc,
                inductionHypothesis]
              change program.wireSupport (wires ⟨0, by decide⟩) =
                Finset.univ.biUnion
                  (fun argument : Fin 1 => program.wireSupport (wires argument))
              simp
          | and | or =>
              rw [lineOrigin, originSupport_wire,
                Program.wireSupport_gate]
              simp [Program.gateSupport]
        · rw [origins_gateWire, gateOrigins_gate_castSucc,
            originSupport_map_castSucc, Program.wireSupport_gate]
          simp only [Program.gateSupport, Fin.lastCases_castSucc]
          simpa using inductionHypothesis (Wire.gate oldGate)

/-- An origin is an input or the output of a charged internal gate. -/
def ValidOrigin
    (program : Program signature n g) : ResidualValue n g → Prop
  | .constant _ => True
  | .wire _ wire =>
      ( ∃ input, wire = Wire.input input ) ∨
      ∃ gate, wire = Wire.gate gate ∧
        binaryCost (program.lines gate).op = 1

theorem validOrigin_negate
    {program : Program signature n g}
    {value : ResidualValue n g}
    (valid : ValidOrigin program value) :
    ValidOrigin program value.negate := by
  cases value with
  | constant value => trivial
  | wire negated wire => exact valid

theorem validOrigin_map_castSucc
    {program : Program signature n g}
    (line : Line signature n g)
    {value : ResidualValue n g}
    (valid : ValidOrigin program value) :
    ValidOrigin (program.gate line)
      (value.mapWires Wire.Renaming.castSucc) := by
  cases value with
  | constant value => trivial
  | wire negated originWire =>
      change ValidOrigin (program.gate line)
        (.wire negated (Wire.Renaming.castSucc originWire))
      rcases valid with ⟨input, rfl⟩ | ⟨gate, rfl, charged⟩
      · exact Or.inl ⟨input, by
          rw [Wire.Renaming.castSucc_apply]
          exact Fin.castSucc_castAdd input⟩
      · exact Or.inr ⟨gate.castSucc, by
          constructor
          · rw [Wire.Renaming.castSucc_apply]
            exact Fin.natAdd_castSucc.symm
          · simpa [Line.mapWires] using charged⟩

/-- Every value returned by `Program.origins` is a valid charged origin. -/
theorem origins_valid
    (program : Program signature n g)
    (wire : Wire n g) :
    ValidOrigin program (origins program wire) := by
  induction program with
  | empty =>
      refine Fin.addCases (fun input => ?_) (fun impossible => Fin.elim0 impossible) wire
      rw [origins_input]
      change (∃ sourceInput,
        Wire.input (g := 0) input = Wire.input sourceInput) ∨ _
      exact Or.inl ⟨input, rfl⟩
  | @gate g program line inductionHypothesis =>
      refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
      · rw [origins_input]
        exact Or.inl ⟨input, rfl⟩
      · refine Fin.lastCases ?_ (fun oldGate => ?_) gate
        · rw [origins_gateWire, gateOrigins_gate_last]
          rcases line with ⟨op, wires⟩
          cases op with
          | false | true => trivial
          | id =>
              rw [lineOrigin, liftedOrigins_apply]
              have valid := inductionHypothesis (wires ⟨0, by decide⟩)
              exact validOrigin_map_castSucc ⟨Op.id, wires⟩ valid
          | not =>
              rw [lineOrigin, liftedOrigins_apply]
              have valid := inductionHypothesis (wires ⟨0, by decide⟩)
              exact validOrigin_negate
                (validOrigin_map_castSucc ⟨Op.not, wires⟩ valid)
          | and | or =>
              exact Or.inr ⟨Fin.last g, by
                constructor
                · rfl
                · simp [Line.mapWires]⟩
        · rw [origins_gateWire, gateOrigins_gate_castSucc]
          have valid := inductionHypothesis (Wire.gate oldGate)
          rw [origins_gateWire] at valid
          exact validOrigin_map_castSucc line valid

/-- Origins evaluate to the values of the source wires they summarize. -/
theorem origins_eval
    (program : Program signature n g)
    (input : Fin n → Bool)
    (wire : Wire n g) :
    (origins program wire).eval program input =
      program.trace interpretation input wire := by
  induction program with
  | empty =>
      refine Fin.addCases (fun sourceInput => ?_)
        (fun impossible => Fin.elim0 impossible) wire
      rw [origins_input]
      rfl
  | @gate g program line inductionHypothesis =>
      refine Fin.addCases (fun sourceInput => ?_) (fun gate => ?_) wire
      · rw [origins_input]
        rfl
      · refine Fin.lastCases ?_ (fun oldGate => ?_) gate
        · rw [origins_gateWire, gateOrigins_gate_last,
            Program.trace_gateWire, Program.gateFunction_gate_last]
          rcases line with ⟨op, wires⟩
          cases op with
          | false | true => rfl
          | id =>
              rw [lineOrigin, liftedOrigins_apply, eval_map_castSucc,
                inductionHypothesis]
              rfl
          | not =>
              rw [lineOrigin, liftedOrigins_apply,
                ResidualValue.eval_negate, eval_map_castSucc,
                inductionHypothesis]
              rfl
          | and | or =>
              rw [lineOrigin, ResidualValue.eval_wire_false,
                Program.trace_gateWire, Program.gateFunction_gate_last]
        · rw [origins_gateWire, gateOrigins_gate_castSucc,
            eval_map_castSucc]
          have gateEval := inductionHypothesis (Wire.gate oldGate)
          rw [origins_gateWire] at gateEval
          calc
            (gateOrigins program oldGate).eval program input =
                program.trace interpretation input (Wire.gate oldGate) :=
              gateEval
            _ = (program.gate line).trace interpretation input
                (Wire.gate oldGate.castSucc) := by
              symm
              change (program.gate line).trace interpretation input
                (Fin.natAdd n oldGate.castSucc) = _
              rw [Fin.natAdd_castSucc]
              exact Program.trace_gate_castSucc program line interpretation input
                (Wire.gate oldGate)

end DeMorgan
end Algebraic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Counting.Normalization
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Factorial-improved Shannon counting

After semantic normalization, all internal gate functions are distinct. Each
computed function can therefore be encoded under all `g!` gate relabelings,
and those encodings are distinct. This removes the artificial topological
ordering from the leading Shannon count.
-/

@[expose] public section

namespace Algebraic

/-! ## Loose presentations and relabeling -/

/-- A circuit presentation whose internal gates need not be topologically ordered. -/
structure LooseCircuit (σ : Signature) (n g m : Nat) where
  /-- One defining line for every labeled internal gate. -/
  internal : Fin g → Line σ n g
  /-- One designated wire for every output. -/
  outputs : Fin m → Wire n g

/-- A loose circuit is equivalently a pair of indexed line collections. -/
def looseCircuitEquiv (σ : Signature) (n g m : Nat) :
    LooseCircuit σ n g m ≃
      (Fin g → Line σ n g) × (Fin m → Wire n g) where
  toFun circuit := (circuit.internal, circuit.outputs)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [Fintype σ.Op] : Fintype (LooseCircuit σ n g m) :=
  Fintype.ofEquiv
    ((Fin g → Line σ n g) × (Fin m → Wire n g))
    (looseCircuitEquiv σ n g m).symm

/-- Exact count of loose labeled circuit presentations. -/
theorem card_looseCircuit [Fintype σ.Op] :
    Fintype.card (LooseCircuit σ n g m) =
      σ.lineCount (n + g) ^ g * (n + g) ^ m := by
  rw [Fintype.card_congr (looseCircuitEquiv σ n g m), Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin, card_line, Wire.card,
    Signature.lineCount]

/-- A loose circuit valuation solves all of its internal gate equations. -/
def LooseCircuit.Satisfies
    (circuit : LooseCircuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (values : Fin g → U) : Prop :=
  ∀ gate, values gate =
    (circuit.internal gate).eval interpretation input values

/-- Read designated output wires under a chosen internal-gate valuation. -/
def LooseCircuit.evalOutputs
    (circuit : LooseCircuit σ n g m)
    (_interpretation : Interpretation σ U)
    (input : Fin n → U)
    (values : Fin g → U) : Fin m → U :=
  fun output => Wire.elim input values (circuit.outputs output)

/-- Rename gate wires along a bijection of gate labels, fixing every input. -/
def _root_.Cslib.Circuits.Wire.Renaming.ofEquiv
    (labels : Fin g ≃ Fin h) : Wire.Renaming n g h where
  gates := fun gate => Wire.gate (labels gate)

export Cslib.Circuits (Wire.Renaming.ofEquiv)

theorem _root_.Cslib.Circuits.Wire.value_ofEquiv
    (labels : Fin g ≃ Fin h)
    (inputs : Fin n → U)
    (values : Fin g → U)
    (wire : Wire n g) :
    Wire.elim inputs (values ∘ labels.symm) (Wire.Renaming.ofEquiv labels wire) =
      Wire.elim inputs values wire := by
  cases wire <;> simp [Wire.Renaming.ofEquiv, Function.comp_apply]

export Cslib.Circuits (Wire.value_ofEquiv)

theorem _root_.Cslib.Circuits.Wire.value_permutation
    (permutation : Equiv.Perm (Fin g))
    (inputs : Fin n → U)
    (values : Fin g → U)
    (wire : Wire n g) :
    Wire.elim inputs (values ∘ permutation.symm)
        (Wire.Renaming.ofPermutation permutation wire) =
      Wire.elim inputs values wire :=
  Wire.value_ofEquiv permutation inputs values wire

export Cslib.Circuits (Wire.value_permutation)

/-- Forget topological order, then rename every internal gate along a bijection
onto the labels `Fin g`. -/
def _root_.Cslib.Circuits.Circuit.relabel
    (circuit : Circuit σ n m)
    (labels : Fin circuit.size ≃ Fin g) : LooseCircuit σ n g m where
  internal := fun gate =>
    (circuit.program.lines (labels.symm gate)).mapWires
      (Wire.Renaming.ofEquiv labels)
  outputs := fun output =>
    Wire.Renaming.ofEquiv labels (circuit.outputs output)

export Cslib.Circuits (Circuit.relabel)

theorem _root_.Cslib.Circuits.Circuit.relabel_satisfies
    (circuit : Circuit σ n m)
    (labels : Fin circuit.size ≃ Fin g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (circuit.relabel labels).Satisfies interpretation input
      (circuit.program.eval interpretation input ∘ labels.symm) := by
  intro gate
  unfold Circuit.relabel
  simp only [Function.comp_apply]
  rw [Line.eval_mapWires]
  · exact (circuit.program.lines_eval interpretation input
      (labels.symm gate)).symm
  · intro wire
    exact Wire.value_ofEquiv labels input
      (circuit.program.eval interpretation input) wire

export Cslib.Circuits (Circuit.relabel_satisfies)

theorem _root_.Cslib.Circuits.Circuit.relabel_evalOutputs
    (circuit : Circuit σ n m)
    (labels : Fin circuit.size ≃ Fin g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (circuit.relabel labels).evalOutputs interpretation input
        (circuit.program.eval interpretation input ∘ labels.symm) =
      circuit.eval interpretation input := by
  funext output
  unfold Circuit.relabel LooseCircuit.evalOutputs Circuit.eval
  exact Wire.value_ofEquiv labels input
    (circuit.program.eval interpretation input) (circuit.outputs output)

/-! ## Acyclicity and unique valuations -/

export Cslib.Circuits (Circuit.relabel_evalOutputs)

/-- Inputs are always available; a gate wire is below a numeric rank bound. -/
def _root_.Cslib.Circuits.Wire.Below
    (rank : Fin g → Nat)
    (bound : Nat)
    (wire : Wire n g) : Prop :=
  Wire.elim (fun _ => True) (fun gate => rank gate < bound) wire

export Cslib.Circuits (Wire.Below)

theorem _root_.Cslib.Circuits.Wire.below_castSucc
    (wire : Wire n g)
    (gate : Fin g) :
    Wire.Below (fun gate : Fin (g + 1) => gate.val) gate.castSucc.val
        wire.castSucc ↔
      Wire.Below (fun gate : Fin g => gate.val) gate.val wire := by
  cases wire <;> simp [Wire.Below]

export Cslib.Circuits (Wire.below_castSucc)

theorem _root_.Cslib.Circuits.Wire.below_last
    (wire : Wire n g) :
    Wire.Below (fun gate : Fin (g + 1) => gate.val) (Fin.last g).val
      wire.castSucc := by
  cases wire <;> simp [Wire.Below]

export Cslib.Circuits (Wire.below_last)

theorem _root_.Cslib.Circuits.Program.lines_below
    (program : Program σ n g)
    (gate : Fin g)
    (argument : Fin (σ.Arity (program.lines gate).op)) :
    Wire.Below (fun gate : Fin g => gate.val) gate.val
      ((program.lines gate).wires argument) := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate g program line ih =>
      revert argument
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · rw [Program.lines_gate_last]
        intro argument
        change Wire.Below (fun gate : Fin (g + 1) => gate.val)
          (Fin.last g).val
          (Wire.Renaming.castSucc (line.wires argument))
        rw [Wire.Renaming.castSucc_apply]
        exact Wire.below_last (line.wires argument)
      · rw [Program.lines_gate_castSucc]
        intro argument
        change Wire.Below (fun gate : Fin (g + 1) => gate.val)
          priorGate.castSucc.val
          (Wire.Renaming.castSucc
            ((program.lines priorGate).wires argument))
        rw [Wire.Renaming.castSucc_apply, Wire.below_castSucc]
        exact ih priorGate argument

export Cslib.Circuits (Program.lines_below)

/-- A rank strictly decreases along every internal gate dependency. -/
def LooseCircuit.AcyclicUnder
    (circuit : LooseCircuit σ n g m)
    (rank : Fin g → Nat) : Prop :=
  ∀ gate argument,
    Wire.Below rank (rank gate) ((circuit.internal gate).wires argument)

theorem _root_.Cslib.Circuits.Wire.below_permutation
    (permutation : Equiv.Perm (Fin g))
    (gate : Fin g)
    (wire : Wire n g) :
    Wire.Below (fun renamed => (permutation.symm renamed).val)
        (permutation.symm gate).val
        (Wire.Renaming.ofPermutation permutation wire) ↔
      Wire.Below (fun original : Fin g => original.val)
        (permutation.symm gate).val wire := by
  cases wire <;> simp [Wire.Below, Wire.Renaming.ofPermutation]

export Cslib.Circuits (Wire.below_permutation)

theorem _root_.Cslib.Circuits.Wire.below_ofEquiv
    (labels : Fin g ≃ Fin h)
    (gate : Fin h)
    (wire : Wire n g) :
    Wire.Below (fun renamed => (labels.symm renamed).val)
        (labels.symm gate).val
        (Wire.Renaming.ofEquiv labels wire) ↔
      Wire.Below (fun original : Fin g => original.val)
        (labels.symm gate).val wire := by
  cases wire <;> simp [Wire.Below, Wire.Renaming.ofEquiv]

export Cslib.Circuits (Wire.below_ofEquiv)

theorem _root_.Cslib.Circuits.Circuit.relabel_acyclic
    (circuit : Circuit σ n m)
    (labels : Fin circuit.size ≃ Fin g) :
    (circuit.relabel labels).AcyclicUnder
      (fun gate => (labels.symm gate).val) := by
  intro gate
  change ∀ argument : Fin
      (σ.Arity (circuit.program.lines (labels.symm gate)).op), _
  intro argument
  change Wire.Below (fun gate => (labels.symm gate).val)
    (labels.symm gate).val
    (Wire.Renaming.ofEquiv labels
      ((circuit.program.lines (labels.symm gate)).wires argument))
  rw [Wire.below_ofEquiv]
  exact circuit.program.lines_below (labels.symm gate) argument

export Cslib.Circuits (Circuit.relabel_acyclic)

theorem _root_.Cslib.Circuits.Wire.values_eq_of_below
    (rank : Fin g → Nat)
    (bound : Nat)
    (wire : Wire n g)
    (below : wire.Below rank bound)
    (inputs : Fin n → U)
    (left right : Fin g → U)
    (agree : ∀ gate, rank gate < bound → left gate = right gate) :
    Wire.elim inputs left wire = Wire.elim inputs right wire := by
  cases wire with
  | input originalInput => rfl
  | gate dependency =>
    simpa using agree dependency (by simpa [Wire.Below] using below)

export Cslib.Circuits (Wire.values_eq_of_below)

/-- An acyclic loose presentation has at most one solution to its gate equations. -/
theorem LooseCircuit.satisfies_unique
    (circuit : LooseCircuit σ n g m)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (rank : Fin g → Nat)
    (acyclic : circuit.AcyclicUnder rank)
    {left right : Fin g → U}
    (leftSatisfies : circuit.Satisfies interpretation input left)
    (rightSatisfies : circuit.Satisfies interpretation input right) :
    left = right := by
  have agreeBelow : ∀ bound, ∀ gate,
      rank gate < bound → left gate = right gate := by
    intro bound
    induction bound with
    | zero =>
        intro gate impossible
        omega
    | succ bound ih =>
        intro gate gateBelow
        calc
          left gate =
              (circuit.internal gate).eval interpretation input left :=
            leftSatisfies gate
          _ = (circuit.internal gate).eval interpretation input right := by
            unfold Line.eval
            congr 1
            funext argument
            let wire := (circuit.internal gate).wires argument
            have below := acyclic gate argument
            exact Wire.values_eq_of_below rank (rank gate) wire
              (by simpa [wire] using below) input left right fun dependency lower =>
                ih dependency <|
                  Nat.lt_of_lt_of_le lower (Nat.le_of_lt_succ gateBelow)
          _ = right gate := (rightSatisfies gate).symm
  funext gate
  exact agreeBelow (rank gate + 1) gate (Nat.lt_succ_self _)

/-! ## The factorial encoding -/

/-- A target together with evidence that an irredundant `g`-gate circuit
computes it. -/
abbrev _root_.Cslib.Circuits.Circuit.IrredundantTarget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n g m : Nat) :=
  { target : Target U n m //
    target ∈ Circuit.irredundantFunctions interpretation n g m }

export Cslib.Circuits (Circuit.IrredundantTarget)

/-- Choose one irredundant representative circuit for a target. -/
noncomputable def _root_.Cslib.Circuits.Circuit.irredundantRepresentative
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m) :
    Circuit σ n m :=
  Classical.choose
    (Circuit.mem_irredundantFunctions_iff.mp target.property)

export Cslib.Circuits (Circuit.irredundantRepresentative)

theorem _root_.Cslib.Circuits.Circuit.irredundantRepresentative_size
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m) :
    (Circuit.irredundantRepresentative interpretation target).size = g :=
  (Classical.choose_spec
    (Circuit.mem_irredundantFunctions_iff.mp target.property)).1

export Cslib.Circuits (Circuit.irredundantRepresentative_size)

theorem _root_.Cslib.Circuits.Circuit.irredundantRepresentative_irredundant
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m) :
    (Circuit.irredundantRepresentative interpretation target).Irredundant
      interpretation :=
  (Classical.choose_spec
    (Circuit.mem_irredundantFunctions_iff.mp target.property)).2.1

export Cslib.Circuits (Circuit.irredundantRepresentative_irredundant)

theorem _root_.Cslib.Circuits.Circuit.irredundantRepresentative_eval
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m) :
    (Circuit.irredundantRepresentative interpretation target).eval interpretation =
      target.val :=
  (Classical.choose_spec
    (Circuit.mem_irredundantFunctions_iff.mp target.property)).2.2

export Cslib.Circuits (Circuit.irredundantRepresentative_eval)

/-- Gate labels of the chosen representative, renamed by a permutation of
`Fin g`. -/
noncomputable def _root_.Cslib.Circuits.Circuit.representativeLabels
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (target : Circuit.IrredundantTarget interpretation n g m)
    (permutation : Equiv.Perm (Fin g)) :
    Fin (Circuit.irredundantRepresentative interpretation target).size ≃ Fin g :=
  (finCongr (Circuit.irredundantRepresentative_size interpretation target)).trans
    permutation

export Cslib.Circuits (Circuit.representativeLabels)

/-- Encode one chosen irredundant circuit for a function under a gate renaming. -/
noncomputable def _root_.Cslib.Circuits.Circuit.sharpEncoding
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) :
    Circuit.IrredundantTarget interpretation n g m × Equiv.Perm (Fin g) →
      LooseCircuit σ n g m :=
    fun pair =>
      (Circuit.irredundantRepresentative interpretation pair.1).relabel
        (Circuit.representativeLabels interpretation pair.1 pair.2)

export Cslib.Circuits (Circuit.sharpEncoding)

/-- The target fixes the unique acyclic valuation of an encoded presentation;
irredundancy then makes its gate permutation recoverable. -/
theorem _root_.Cslib.Circuits.Circuit.sharpEncoding_injective
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) :
    Function.Injective (Circuit.sharpEncoding (n := n) (g := g) (m := m)
      interpretation) := by
  classical
  rintro ⟨leftTarget, leftPermutation⟩ ⟨rightTarget, rightPermutation⟩ encodedEqual
  let leftCircuit := Circuit.irredundantRepresentative interpretation leftTarget
  let rightCircuit := Circuit.irredundantRepresentative interpretation rightTarget
  let leftLabels :=
    Circuit.representativeLabels interpretation leftTarget leftPermutation
  let rightLabels :=
    Circuit.representativeLabels interpretation rightTarget rightPermutation
  have relabelEqual :
      leftCircuit.relabel leftLabels =
        rightCircuit.relabel rightLabels := encodedEqual
  have valuationEqual (input : Fin n → U) :
      leftCircuit.program.eval interpretation input ∘ leftLabels.symm =
        rightCircuit.program.eval interpretation input ∘ rightLabels.symm := by
    apply LooseCircuit.satisfies_unique
      (leftCircuit.relabel leftLabels) interpretation input
      (fun gate => (leftLabels.symm gate).val)
      (leftCircuit.relabel_acyclic leftLabels)
      (leftCircuit.relabel_satisfies leftLabels interpretation input)
    rw [relabelEqual]
    exact rightCircuit.relabel_satisfies rightLabels interpretation input
  have circuitEvalEqual :
      leftCircuit.eval interpretation = rightCircuit.eval interpretation := by
    funext input
    rw [← leftCircuit.relabel_evalOutputs leftLabels interpretation input,
      ← rightCircuit.relabel_evalOutputs rightLabels interpretation input,
      relabelEqual, valuationEqual input]
  have targetValueEqual : leftTarget.val = rightTarget.val := by
    calc
      leftTarget.val = leftCircuit.eval interpretation :=
        (Circuit.irredundantRepresentative_eval interpretation leftTarget).symm
      _ = rightCircuit.eval interpretation := circuitEvalEqual
      _ = rightTarget.val :=
        Circuit.irredundantRepresentative_eval interpretation rightTarget
  have targetEqual : leftTarget = rightTarget := Subtype.ext targetValueEqual
  subst rightTarget
  have labelsEqual : leftLabels = rightLabels := by
    apply Equiv.ext
    intro gate
    have gateFunctionsEqual :
        leftCircuit.program.gateFunction interpretation gate =
          leftCircuit.program.gateFunction interpretation
            (rightLabels.symm (leftLabels gate)) := by
      funext input
      have atRenamedGate := congrFun (valuationEqual input) (leftLabels gate)
      simpa only [leftCircuit, rightCircuit, Function.comp_apply,
        Equiv.symm_apply_apply, Program.gateFunction] using atRenamedGate
    have gateEqual :=
      Circuit.irredundantRepresentative_irredundant interpretation leftTarget
        gateFunctionsEqual
    have renamedEqual := congrArg rightLabels gateEqual
    simpa using renamedEqual.symm
  have permutationEqual : leftPermutation = rightPermutation := by
    apply Equiv.ext
    intro gate
    have atGate := congrArg (fun labels => labels
      ((finCongr (Circuit.irredundantRepresentative_size interpretation
        leftTarget)).symm gate)) labelsEqual
    simpa [leftLabels, rightLabels, Circuit.representativeLabels] using atGate
  subst rightPermutation
  rfl

/-! ## Counting consequences -/

export Cslib.Circuits (Circuit.sharpEncoding_injective)

/-- Sharp fixed-size Shannon count, including the full `g!` relabeling gain. -/
theorem _root_.Cslib.Circuits.Circuit.card_irredundantFunctions_mul_factorial_le
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n g m : Nat) :
    (Circuit.irredundantFunctions interpretation n g m).card * g.factorial ≤
      σ.lineCount (n + g) ^ g * (n + g) ^ m := by
  classical
  have encoded := Fintype.card_le_of_injective
    (Circuit.sharpEncoding (n := n) (g := g) (m := m) interpretation)
    (Circuit.sharpEncoding_injective (n := n) (g := g) (m := m)
      interpretation)
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    card_looseCircuit] at encoded
  simpa only [Fintype.card_coe] using encoded

export Cslib.Circuits (Circuit.card_irredundantFunctions_mul_factorial_le)

/-- Sharp number of possible functions at exactly `g` internal gates. -/
def _root_.Cslib.Circuits.Signature.sharpCount
    (σ : Signature) [Fintype σ.Op]
    (n g m : Nat) : Nat :=
  (σ.lineCount (n + g) ^ g * (n + g) ^ m) / g.factorial

export Cslib.Circuits (Signature.sharpCount)

theorem _root_.Cslib.Circuits.Circuit.card_irredundantFunctions_le_sharpCount
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n g m : Nat) :
    (Circuit.irredundantFunctions interpretation n g m).card ≤
      σ.sharpCount n g m := by
  apply (Nat.le_div_iff_mul_le (Nat.factorial_pos g)).2
  exact Circuit.card_irredundantFunctions_mul_factorial_le
    interpretation n g m

export Cslib.Circuits (Circuit.card_irredundantFunctions_le_sharpCount)

/-- Sharp Shannon budget for all circuits with at most `G` internal gates. -/
def _root_.Cslib.Circuits.Signature.sharpBudget
    (σ : Signature) [Fintype σ.Op]
    (n m G : Nat) : Nat :=
  ∑ g ∈ Finset.range (G + 1), σ.sharpCount n g m

export Cslib.Circuits (Signature.sharpBudget)

theorem _root_.Cslib.Circuits.Circuit.card_functionsAtMost_le_sharpBudget
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m G : Nat) :
    (Circuit.functionsAtMost interpretation n m G).card ≤
      σ.sharpBudget n m G := by
  refine (Circuit.card_functionsAtMost_le_sum_irredundant
    interpretation n m G).trans ?_
  unfold Signature.sharpBudget
  exact Finset.sum_le_sum fun g _ =>
    Circuit.card_irredundantFunctions_le_sharpCount interpretation n g m

export Cslib.Circuits (Circuit.card_functionsAtMost_le_sharpBudget)

/-- A family larger than the sharp budget contains a size-hard function. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_in_family_sharp
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (large : σ.sharpBudget n m G < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_in_family_of_card_lt interpretation family
  exact (Circuit.card_functionsAtMost_le_sharpBudget
    interpretation n m G).trans_lt large

export Cslib.Circuits (Circuit.exists_hard_in_family_sharp)

/-- Full-universe sharp Shannon lower bound. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_sharp
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (large : σ.sharpBudget n m G < Target.count U n m) :
    ∃ target : Target U n m,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_of_card_lt interpretation
  exact (Circuit.card_functionsAtMost_le_sharpBudget
    interpretation n m G).trans_lt large

export Cslib.Circuits (Circuit.exists_hard_sharp)

/-- Under functional completeness, a target outside the sharp budget is both
hard below `G` and computable at some finite size. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_sharp_of_complete
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (complete : interpretation.FunctionallyComplete)
    (large : σ.sharpBudget n m G < Target.count U n m) :
    ∃ target : Target U n m,
      Circuit.GateHard interpretation G target ∧
      ∃ circuit : Circuit σ n m,
        circuit.ComputesWith interpretation target := by
  obtain ⟨target, hard⟩ := Circuit.exists_hard_sharp interpretation large
  exact ⟨target, hard, complete n m target⟩

export Cslib.Circuits (Circuit.exists_hard_sharp_of_complete)

/-- Boolean specialization of the sharp Shannon theorem. -/
theorem _root_.Cslib.Circuits.Circuit.exists_boolean_hard_sharp
    [Fintype σ.Op]
    (interpretation : Interpretation σ Bool)
    (large : σ.sharpBudget n m G < Target.count Bool n m) :
    ∃ target : Target Bool n m,
      Circuit.GateHard interpretation G target :=
  Circuit.exists_hard_sharp interpretation large

export Cslib.Circuits (Circuit.exists_boolean_hard_sharp)

end Algebraic

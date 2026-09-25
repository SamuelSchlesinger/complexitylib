/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity.Relative
public import Complexitylib.Algebraic.Analysis.Frontier
public import Complexitylib.Algebraic.LowerBound.FanIn.Size

/-!
# Relative lower bounds from necessary source values

`SourceSupport` says that a selected subset of a supplied family determines
the target. `sourceSupportSize` minimizes the number of selected sources,
independently of a circuit basis. Weighted frontier counting then bounds this
semantic minimum by the number of outputs plus the circuit cost.
-/

@[expose] public section

namespace Algebraic

/-- Agreement on selected supplied values forces agreement of the target. -/
def SourceSupport (target : X → Fin m → U) (sources : X → Fin n → U)
    (selected : Finset (Fin n)) : Prop :=
  ∀ x y, (∀ i ∈ selected, sources x i = sources y i) → target x = target y

/-- Fewest source coordinates determining the target, or infinity if even
the whole supplied family does not determine it. -/
noncomputable def sourceSupportSize (target : X → Fin m → U)
    (sources : X → Fin n → U) : ℕ∞ :=
  ⨅ selected : Finset (Fin n), ⨅ _ : SourceSupport target sources selected,
    (selected.card : ℕ∞)

/-- Any determining set bounds the minimum number of required source values. -/
theorem sourceSupportSize_le {target : X → Fin m → U} {sources : X → Fin n → U}
    {selected : Finset (Fin n)} (determines : SourceSupport target sources selected) :
    sourceSupportSize target sources ≤ selected.card :=
  iInf_le_of_le selected (iInf_le_of_le determines le_rfl)

/-- A uniform bound on determining sets bounds the semantic minimum. -/
theorem le_sourceSupportSize {target : X → Fin m → U} {sources : X → Fin n → U}
    (lower : ℕ∞)
    (bounded : ∀ selected, SourceSupport target sources selected → lower ≤ selected.card) :
    lower ≤ sourceSupportSize target sources :=
  le_iInf fun selected => le_iInf fun determines => bounded selected determines

/-- A finite source budget is witnessed by a determining set. -/
theorem sourceSupportSize_le_iff (target : X → Fin m → U) (sources : X → Fin n → U)
    (budget : Nat) :
    sourceSupportSize target sources ≤ budget ↔
      ∃ selected, SourceSupport target sources selected ∧ selected.card ≤ budget := by
  constructor
  · intro bounded
    have below : sourceSupportSize target sources < ((budget + 1 : Nat) : ℕ∞) :=
      bounded.trans_lt (by exact_mod_cast Nat.lt_succ_self budget)
    simp only [sourceSupportSize, iInf_lt_iff] at below
    obtain ⟨selected, determines, small⟩ := below
    refine ⟨selected, determines, ?_⟩
    have small' : selected.card < budget + 1 := by exact_mod_cast small
    omega
  · rintro ⟨selected, determines, bounded⟩
    exact (sourceSupportSize_le determines).trans (by exact_mod_cast bounded)

end Algebraic

open Algebraic

namespace Cslib.Circuits.Circuit

/-- Every relative implementation uses a source subset determining its target. -/
theorem ComputesFrom.sourceSupport
    {circuit : Circuit σ n gates m} {interpretation : Interpretation σ U}
    {target : X → Fin m → U} {sources : X → Fin n → U}
    (computes : circuit.ComputesFrom interpretation target sources) :
    SourceSupport target sources circuit.inputSupport := by
  intro x y agrees
  rw [← computes x, ← computes y]
  exact circuit.eval_dependsOnlyOn interpretation _ _ agrees

/-- The weighted frontier bound specialized to all designated output wires. -/
theorem card_inputSupport_le_cost
    (circuit : Circuit σ n gates m) (weight : OperationCost σ)
    (bounded : ∀ op, σ.Arity op ≤ weight op + 1) :
    circuit.inputSupport.card ≤ m + circuit.cost weight := by
  have bound := circuit.program.card_frontierSupport_le weight bounded
    (Finset.univ.image circuit.outputs)
  have equal : circuit.program.frontierSupport (Finset.univ.image circuit.outputs) =
      circuit.inputSupport := by
    ext i
    simp [Program.frontierSupport, Circuit.mem_inputSupport]
  rw [equal] at bound
  exact bound.trans (Nat.add_le_add_right
    (Finset.card_image_le.trans_eq (Fintype.card_fin m)) _)

/-- Necessary supplied values lower-bound weighted relative complexity. -/
theorem sourceSupportSize_le_relativeCostComplexity
    (interpretation : Interpretation σ U) (weight : OperationCost σ)
    (bounded : ∀ op, σ.Arity op ≤ weight op + 1)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    sourceSupportSize target sources ≤ (m : ℕ∞) +
      relativeCostComplexity interpretation weight target sources := by
  unfold relativeCostComplexity
  simp only [ENat.add_iInf]
  refine le_iInf fun gates => le_iInf fun circuit => le_iInf fun computes => ?_
  exact (sourceSupportSize_le computes.sourceSupport).trans
    (by exact_mod_cast circuit.card_inputSupport_le_cost weight bounded)

/-- A bounded-fan-in implementation must touch enough supplied values. -/
theorem sourceSupportSize_le_size
    {circuit : Circuit σ n gates m} {interpretation : Interpretation σ U}
    {target : X → Fin m → U} {sources : X → Fin n → U}
    (computes : circuit.ComputesFrom interpretation target sources)
    (bounded : circuit.FanInAtMost b) :
    sourceSupportSize target sources ≤ ((m + (b - 1) * circuit.size : Nat) : ℕ∞) :=
  (sourceSupportSize_le computes.sourceSupport).trans
    (by exact_mod_cast circuit.card_inputSupport_le_size bounded)

/-- The semantic source count bounds minimum gate complexity for any basis
of fan-in at most `b`, with `b ≥ 2` so infinite complexities cause no `0 * ∞`. -/
theorem sourceSupportSize_le_relativeGateComplexity
    (interpretation : Interpretation σ U) (b : Nat) (positive : 2 ≤ b)
    (bounded : ∀ op, σ.Arity op ≤ b)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    sourceSupportSize target sources ≤ (m : ℕ∞) +
      ((b - 1 : Nat) : ℕ∞) * relativeGateComplexity interpretation target sources := by
  have nonzero : ((b - 1 : Nat) : ℕ∞) ≠ 0 := by
    exact_mod_cast (show b - 1 ≠ 0 by omega)
  unfold relativeGateComplexity relativeCostComplexity
  simp only [ENat.mul_iInf_of_ne nonzero, ENat.add_iInf]
  refine le_iInf fun gates => le_iInf fun circuit => le_iInf fun computes => ?_
  have fanIn : circuit.FanInAtMost b := by
    have allPrograms : ∀ {g} (program : Program σ n g), program.FanInAtMost b := by
      intro g program
      induction program with
      | empty => trivial
      | gate prior line ih => exact ⟨ih, bounded line.op⟩
    exact allPrograms circuit.program
  simpa only [cost_unit, ENat.natCast_add, ENat.natCast_mul] using
    sourceSupportSize_le_size computes fanIn

end Cslib.Circuits.Circuit

namespace Algebraic.Circuit

export Cslib.Circuits.Circuit
  (card_inputSupport_le_cost sourceSupportSize_le_relativeCostComplexity
   sourceSupportSize_le_size sourceSupportSize_le_relativeGateComplexity)

end Algebraic.Circuit

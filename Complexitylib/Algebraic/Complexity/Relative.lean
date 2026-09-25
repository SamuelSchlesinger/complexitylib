/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity
public import Complexitylib.Algebraic.Parallel

/-!
# Circuit complexity relative to a supplied family

For arbitrary sets `X` and `U`, a source family `sources : X → Fin n → U`
supplies the formal inputs to a circuit computing `target : X → Fin m → U`.
`Circuit.relativeCostComplexity` minimizes the weighted cost of such circuits.
No coordinates of `X` are implicitly available.

This is the general framework of Definition 2.1 and Proposition 2.2 in
Stephen Wayne Boyack, *The Robustness of Combinatorial Measures of Boolean
Matrix Complexity*, MIT PhD thesis (1985), pp. 29–31. The signature here has
arbitrary finite arities and natural-number costs, rather than only binary
operations. Constants must be explicitly supplied or implemented by gates;
there is no implicit free zero at disconnected outputs.

The extension and section theorems make the domains in Proposition 2.2.1
explicit. A partial function on `Set.range sources` must be extended before
using ordinary circuit complexity. Surjective sources avoid this issue.

Source: https://hdl.handle.net/1721.1/15322.
-/

@[expose] public section

open Algebraic

namespace Cslib.Circuits.Circuit

/-- A circuit computes a target family when its formal inputs are supplied
by `sources`. The common domain need not be a product or a finite type. -/
def ComputesFrom (circuit : Circuit σ n gates m)
    (interpretation : Interpretation σ U)
    (target : X → Fin m → U) (sources : X → Fin n → U) : Prop :=
  ∀ x, circuit.eval interpretation (sources x) = target x

/-- Minimum cost of computing `target` from exactly the supplied source
family. No implementation of the sources is charged or required. -/
noncomputable def relativeCostComplexity
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) : ℕ∞ :=
  ⨅ gates, ⨅ circuit : Circuit σ n gates m,
    ⨅ _ : circuit.ComputesFrom interpretation target sources,
      (circuit.cost operationCost : ℕ∞)

/-- Minimum number of operation gates computing a target from a source family. -/
noncomputable def relativeGateComplexity
    (interpretation : Interpretation σ U)
    (target : X → Fin m → U) (sources : X → Fin n → U) : ℕ∞ :=
  relativeCostComplexity interpretation OperationCost.unit target sources

/-- A concrete implementation bounds relative complexity. -/
theorem relativeCostComplexity_le
    {circuit : Circuit σ n gates m} {interpretation : Interpretation σ U}
    {target : X → Fin m → U} {sources : X → Fin n → U}
    (operationCost : OperationCost σ)
    (computes : circuit.ComputesFrom interpretation target sources) :
    relativeCostComplexity interpretation operationCost target sources ≤
      circuit.cost operationCost := by
  unfold relativeCostComplexity
  exact iInf_le_of_le gates <| iInf_le_of_le circuit <| iInf_le_of_le computes le_rfl

/-- A lower bound for all implementations bounds relative complexity. -/
theorem le_relativeCostComplexity
    {interpretation : Interpretation σ U}
    {target : X → Fin m → U} {sources : X → Fin n → U}
    (operationCost : OperationCost σ) (bound : ℕ∞)
    (lowerBound : ∀ {gates} (circuit : Circuit σ n gates m),
      circuit.ComputesFrom interpretation target sources → bound ≤ circuit.cost operationCost) :
    bound ≤ relativeCostComplexity interpretation operationCost target sources := by
  unfold relativeCostComplexity
  exact le_iInf fun _ => le_iInf fun circuit => le_iInf fun computes => lowerBound circuit computes

/-- A finite relative budget is witnessed by a concrete circuit. -/
theorem relativeCostComplexity_le_iff
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) (budget : Nat) :
    relativeCostComplexity interpretation operationCost target sources ≤ budget ↔
      ∃ gates, ∃ circuit : Circuit σ n gates m,
        circuit.ComputesFrom interpretation target sources ∧ circuit.cost operationCost ≤ budget := by
  constructor
  · intro bounded
    have below : relativeCostComplexity interpretation operationCost target sources <
        ((budget + 1 : Nat) : ℕ∞) := bounded.trans_lt (by exact_mod_cast Nat.lt_succ_self budget)
    simp only [relativeCostComplexity, iInf_lt_iff] at below
    obtain ⟨gates, circuit, computes, costLt⟩ := below
    have costLt' : circuit.cost operationCost < budget + 1 := by exact_mod_cast costLt
    exact ⟨gates, circuit, computes, Nat.le_of_lt_succ costLt'⟩
  · rintro ⟨gates, circuit, computes, bounded⟩
    exact (relativeCostComplexity_le operationCost computes).trans (by exact_mod_cast bounded)

/-- Finiteness is exactly representability from the supplied family. -/
theorem relativeCostComplexity_lt_top_iff
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost target sources < ⊤ ↔
      ∃ gates, ∃ circuit : Circuit σ n gates m,
        circuit.ComputesFrom interpretation target sources := by
  simp only [relativeCostComplexity, iInf_lt_iff, ENat.natCast_lt_top, exists_prop, and_true]

/-- Nonrepresentable targets have infinite relative complexity. -/
@[simp] theorem relativeCostComplexity_eq_top_iff
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost target sources = ⊤ ↔
      ¬ ∃ gates, ∃ circuit : Circuit σ n gates m,
        circuit.ComputesFrom interpretation target sources := by
  rw [eq_top_iff, ← not_lt, relativeCostComplexity_lt_top_iff]

/-- A relative gate bound is witnessed by a circuit with at most that many gates. -/
theorem relativeGateComplexity_le_iff
    (interpretation : Interpretation σ U)
    (target : X → Fin m → U) (sources : X → Fin n → U) (budget : Nat) :
    relativeGateComplexity interpretation target sources ≤ budget ↔
      ∃ gates ≤ budget, ∃ circuit : Circuit σ n gates m,
        circuit.ComputesFrom interpretation target sources := by
  simp only [relativeGateComplexity, relativeCostComplexity_le_iff,
    cost_unit, size, exists_and_left, and_comm]

/-- With unit gate costs, zero complexity means selecting fixed source wires.
This characterization need not hold when operations can have zero weight. -/
theorem relativeGateComplexity_eq_zero_iff
    (interpretation : Interpretation σ U)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeGateComplexity interpretation target sources = 0 ↔
      ∃ select : Fin m → Fin n, ∀ x, sources x ∘ select = target x := by
  constructor
  · intro zero
    obtain ⟨gates, bounded, circuit, computes⟩ :=
      (relativeGateComplexity_le_iff interpretation target sources 0).mp zero.le
    have gatesZero : gates = 0 := Nat.eq_zero_of_le_zero bounded
    subst gates
    let select : Fin m → Fin n := fun i => Fin.cast (Nat.add_zero n) (circuit.outputs i)
    have outputEq (i : Fin m) : circuit.outputs i = Wire.input (select i) := Fin.ext rfl
    refine ⟨select, fun x => ?_⟩
    rw [← computes x]
    funext i
    simp only [eval, Function.comp_apply, outputEq, Program.trace_input]
  · rintro ⟨select, agrees⟩
    apply le_antisymm _ zero_le
    have computes : ((Circuit.id σ n).mapOutputs select).ComputesFrom
        interpretation target sources := by
      intro x
      simpa using agrees x
    simpa [relativeGateComplexity, size] using relativeCostComplexity_le OperationCost.unit computes

/-- Ordinary complexity is relative complexity with the identity family supplied. -/
@[simp] theorem relativeCostComplexity_id
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : Target U n m) :
    relativeCostComplexity interpretation operationCost target (fun x => x) =
      costComplexity interpretation operationCost target := rfl

/-- Selecting, duplicating, or reordering supplied values requires no gates. -/
theorem relativeCostComplexity_select
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (sources : X → Fin n → U) (select : Fin m → Fin n) :
    relativeCostComplexity interpretation operationCost
      (fun x i => sources x (select i)) sources = 0 := by
  apply le_antisymm _ zero_le
  have computes : ((Circuit.id σ n).mapOutputs select).ComputesFrom interpretation
      (fun x i => sources x (select i)) sources := by
    intro x
    simp [Function.comp_def]
  simpa using relativeCostComplexity_le operationCost computes

/-- A family is free relative to itself. -/
@[simp] theorem relativeCostComplexity_self
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) :
    relativeCostComplexity interpretation operationCost target target = 0 :=
  relativeCostComplexity_select interpretation operationCost target (fun i => i)

/-- Boyack's Proposition 2.2 for arbitrary domains, interpretations, arities,
and natural-number operation costs. Compose the two implementing circuits. -/
theorem relativeCostComplexity_triangle
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (middle : X → Fin l → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost target sources ≤
      relativeCostComplexity interpretation operationCost target middle +
        relativeCostComplexity interpretation operationCost middle sources := by
  conv_rhs =>
    unfold relativeCostComplexity
    simp only [ENat.iInf_add, ENat.add_iInf]
  refine le_iInf fun innerGates => le_iInf fun inner => le_iInf fun innerComputes =>
    le_iInf fun outerGates => le_iInf fun outer => le_iInf fun outerComputes => ?_
  have computes : (outer.comp inner).ComputesFrom interpretation target sources := by
    intro x
    rw [eval_comp, innerComputes x]
    exact outerComputes x
  simpa [ENat.natCast_add, add_comm] using relativeCostComplexity_le operationCost computes

/-- The relative triangle inequality for unit gate cost. -/
theorem relativeGateComplexity_triangle
    (interpretation : Interpretation σ U)
    (target : X → Fin m → U) (middle : X → Fin l → U) (sources : X → Fin n → U) :
    relativeGateComplexity interpretation target sources ≤
      relativeGateComplexity interpretation target middle +
        relativeGateComplexity interpretation middle sources :=
  relativeCostComplexity_triangle interpretation OperationCost.unit target middle sources

/-- Mutually free changes of supplied representation preserve every relative
complexity. This includes removing duplicated or redundant source wires. -/
theorem relativeCostComplexity_eq_of_mutually_free
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (first : X → Fin n → U) (second : X → Fin k → U)
    (forward : relativeCostComplexity interpretation operationCost first second = 0)
    (backward : relativeCostComplexity interpretation operationCost second first = 0) :
    relativeCostComplexity interpretation operationCost target first =
      relativeCostComplexity interpretation operationCost target second := by
  apply le_antisymm
  · simpa only [backward, add_zero] using
      relativeCostComplexity_triangle interpretation operationCost target second first
  · simpa only [forward, add_zero] using
      relativeCostComplexity_triangle interpretation operationCost target first second

/-- Compute two target families in parallel from the same supplied values. -/
theorem relativeCostComplexity_pair_le
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (first : X → Fin m → U) (second : X → Fin l → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost
      (fun x => Fin.append (first x) (second x)) sources ≤
      relativeCostComplexity interpretation operationCost first sources +
        relativeCostComplexity interpretation operationCost second sources := by
  conv_rhs =>
    unfold relativeCostComplexity
    simp only [ENat.iInf_add, ENat.add_iInf]
  refine le_iInf fun rightGates => le_iInf fun right => le_iInf fun rightComputes =>
    le_iInf fun leftGates => le_iInf fun left => le_iInf fun leftComputes => ?_
  have computes : (left.parallel right).ComputesFrom interpretation
      (fun x => Fin.append (first x) (second x)) sources := by
    intro x
    rw [eval_parallel, leftComputes x, rightComputes x]
  simpa [ENat.natCast_add] using relativeCostComplexity_le operationCost computes

/-- Supplying a family containing all the old sources cannot increase cost. -/
theorem relativeCostComplexity_mono_sources
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) (more : X → Fin k → U)
    (select : Fin n → Fin k) (agrees : ∀ x i, more x (select i) = sources x i) :
    relativeCostComplexity interpretation operationCost target more ≤
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_relativeCostComplexity
  intro gates circuit computes
  have reindexed : (circuit.mapInputs select).ComputesFrom interpretation target more := by
    intro x
    rw [eval_mapInputs]
    have equal : more x ∘ select = sources x := funext (agrees x)
    rw [equal]
    exact computes x
  simpa using relativeCostComplexity_le operationCost reindexed

/-- Selecting some of the target outputs cannot increase cost. -/
theorem relativeCostComplexity_map_outputs_le
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) (select : Fin l → Fin m) :
    relativeCostComplexity interpretation operationCost (fun x i => target x (select i)) sources ≤
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_relativeCostComplexity
  intro gates circuit computes
  have selected : (circuit.mapOutputs select).ComputesFrom interpretation
      (fun x i => target x (select i)) sources := by
    intro x
    rw [eval_mapOutputs, computes x]
    rfl
  simpa using relativeCostComplexity_le operationCost selected

/-- Adding outputs that are free from the sources does not change complexity. -/
theorem relativeCostComplexity_pair_eq_of_left_eq_zero
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (first : X → Fin m → U) (second : X → Fin l → U) (sources : X → Fin n → U)
    (free : relativeCostComplexity interpretation operationCost first sources = 0) :
    relativeCostComplexity interpretation operationCost
      (fun x => Fin.append (first x) (second x)) sources =
      relativeCostComplexity interpretation operationCost second sources := by
  apply le_antisymm
  · simpa only [free, zero_add] using
      relativeCostComplexity_pair_le interpretation operationCost first second sources
  · simpa only [Fin.append_right] using relativeCostComplexity_map_outputs_le
      interpretation operationCost (fun x => Fin.append (first x) (second x)) sources (Fin.natAdd m)

/-- Boyack's extension characterization with an explicit total extension:
minimize ordinary complexity over functions agreeing on `Set.range sources`. -/
theorem relativeCostComplexity_eq_iInf
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost target sources =
      ⨅ h : Target U n m, ⨅ _ : ∀ x, h (sources x) = target x,
        costComplexity interpretation operationCost h := by
  apply le_antisymm
  · refine le_iInf fun h => le_iInf fun agrees => ?_
    apply le_costComplexity
    intro gates circuit computes
    exact relativeCostComplexity_le operationCost (fun x => (computes _).trans (agrees x))
  · apply le_relativeCostComplexity
    intro gates circuit computes
    exact iInf_le_of_le (circuit.eval interpretation) <|
      iInf_le_of_le computes <| costComplexity_le operationCost (fun _ => rfl)

/-- Restricting the common domain can only remove correctness obligations. -/
theorem relativeCostComplexity_precomp_le
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) (map : Y → X) :
    relativeCostComplexity interpretation operationCost (target ∘ map) (sources ∘ map) ≤
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_relativeCostComplexity
  intro gates circuit computes
  exact relativeCostComplexity_le operationCost (fun y => computes (map y))

/-- Relative computation after a change of domain can use any implementation
of the restricted sources from a new supplied family. -/
theorem relativeCostComplexity_precomp_triangle
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U)
    (map : Y → X) (supplied : Y → Fin k → U) :
    relativeCostComplexity interpretation operationCost (target ∘ map) supplied ≤
      relativeCostComplexity interpretation operationCost target sources +
        relativeCostComplexity interpretation operationCost (sources ∘ map) supplied :=
  (relativeCostComplexity_triangle interpretation operationCost
    (target ∘ map) (sources ∘ map) supplied).trans
      (add_le_add (relativeCostComplexity_precomp_le
        interpretation operationCost target sources map) le_rfl)

/-- A surjective reindexing of the common domain preserves complexity. This
includes permuting the columns of a finite table of functions. -/
theorem relativeCostComplexity_precomp_eq
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U)
    (map : Y → X) (onto : Function.Surjective map) :
    relativeCostComplexity interpretation operationCost (target ∘ map) (sources ∘ map) =
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_antisymm (relativeCostComplexity_precomp_le ..)
  apply le_relativeCostComplexity
  intro gates circuit computes
  apply relativeCostComplexity_le operationCost
  intro x
  obtain ⟨y, rfl⟩ := onto x
  exact computes y

/-- Equal supplied values must give equal target values whenever a circuit
computes the target. This necessary condition does not assume completeness. -/
theorem ComputesFrom.agrees_on_fibers
    {circuit : Circuit σ n gates m} {interpretation : Interpretation σ U}
    {target : X → Fin m → U} {sources : X → Fin n → U}
    (computes : circuit.ComputesFrom interpretation target sources)
    {x y : X} (equal : sources x = sources y) : target x = target y := by
  rw [← computes x, ← computes y, equal]

/-- Circuit computation factors through the supplied values. -/
theorem ComputesFrom.factorsThrough
    {circuit : Circuit σ n gates m} {interpretation : Interpretation σ U}
    {target : X → Fin m → U} {sources : X → Fin n → U}
    (computes : circuit.ComputesFrom interpretation target sources) :
    Function.FactorsThrough target sources :=
  fun _ _ equal => computes.agrees_on_fibers equal

/-- If the supplied values identify two inputs that the target distinguishes,
no circuit can compute the target from those values, over any interpretation. -/
theorem relativeCostComplexity_eq_top_of_fiber_collision
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U)
    {x y : X} (same : sources x = sources y) (different : target x ≠ target y) :
    relativeCostComplexity interpretation operationCost target sources = ⊤ := by
  rw [relativeCostComplexity_eq_top_iff]
  rintro ⟨gates, circuit, computes⟩
  exact different (computes.agrees_on_fibers same)

/-- For a functionally complete interpretation, equality on source fibers is
also sufficient. A nonempty output space permits total extensions off the
image of the supplied family. This generalizes the complete-basis case of
Boyack's Theorem 7.1.5 without asserting its algorithmic running time. -/
theorem relativeCostComplexity_lt_top_iff_factorsThrough
    [Nonempty (Fin m → U)]
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (complete : interpretation.FunctionallyComplete)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost target sources < ⊤ ↔
      Function.FactorsThrough target sources := by
  rw [relativeCostComplexity_lt_top_iff]
  constructor
  · rintro ⟨gates, circuit, computes⟩
    exact computes.factorsThrough
  · intro factors
    obtain ⟨extension, equal⟩ := (Function.factorsThrough_iff target).mp factors
    obtain ⟨gates, circuit, computes⟩ := complete n m extension
    refine ⟨gates, circuit, fun x => ?_⟩
    rw [equal]
    exact computes (sources x)

/-- Boyack's Corollary 2.2.1.2: for surjective sources and a target constant
on their fibers, any right inverse reduces relative to ordinary complexity. -/
theorem relativeCostComplexity_eq_of_rightInverse
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U)
    (sectionMap : (Fin n → U) → X) (sectionLaw : Function.RightInverse sectionMap sources)
    (respects : ∀ x y, sources x = sources y → target x = target y) :
    relativeCostComplexity interpretation operationCost target sources =
      costComplexity interpretation operationCost (target ∘ sectionMap) := by
  apply le_antisymm
  · apply le_costComplexity
    intro gates circuit computes
    apply relativeCostComplexity_le operationCost
    intro x
    exact (computes (sources x)).trans (respects _ _ (sectionLaw (sources x)))
  · apply le_relativeCostComplexity
    intro gates circuit computes
    apply costComplexity_le operationCost
    intro input
    simpa only [sectionLaw input, Function.comp_apply] using computes (sectionMap input)

/-- Boyack's Corollary 2.2.1.3: an invertible source family converts relative
complexity into ordinary complexity after composing with its inverse. -/
theorem relativeCostComplexity_eq_of_equiv
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X ≃ (Fin n → U)) :
    relativeCostComplexity interpretation operationCost target sources =
      costComplexity interpretation operationCost (target ∘ sources.symm) :=
  relativeCostComplexity_eq_of_rightInverse interpretation operationCost target sources
    sources.symm sources.apply_symm_apply (sources.injective.factorsThrough target)

/-- Permuting the supplied wires preserves relative complexity. -/
theorem relativeCostComplexity_reindex_sources
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) (indices : Fin k ≃ Fin n) :
    relativeCostComplexity interpretation operationCost target (fun x => sources x ∘ indices) =
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_antisymm
  · exact relativeCostComplexity_mono_sources interpretation operationCost target sources
      (fun x => sources x ∘ indices) indices.symm (by simp)
  · exact relativeCostComplexity_mono_sources interpretation operationCost target
      (fun x => sources x ∘ indices) sources indices (fun _ _ => rfl)

/-- Permuting the target outputs preserves relative complexity. Together
with domain reindexing this gives the structural row/column invariance
behind Boyack's Proposition 7.1.4.2. -/
theorem relativeCostComplexity_reindex_outputs
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) (indices : Fin l ≃ Fin m) :
    relativeCostComplexity interpretation operationCost (fun x => target x ∘ indices) sources =
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_antisymm (relativeCostComplexity_map_outputs_le interpretation operationCost
    target sources indices)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using
    relativeCostComplexity_map_outputs_le interpretation operationCost
    (fun x => target x ∘ indices) sources indices.symm

/-- Retaining the supplied family as additional outputs is free. -/
@[simp] theorem relativeCostComplexity_append_sources
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost
      (fun x => Fin.append (sources x) (target x)) sources =
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_antisymm
  · simpa using relativeCostComplexity_pair_le interpretation operationCost sources target sources
  · simpa only [Fin.append_right] using relativeCostComplexity_map_outputs_le
      interpretation operationCost (fun x => Fin.append (sources x) (target x)) sources (Fin.natAdd n)

/-- Retaining the sources after the other outputs is also free. -/
@[simp] theorem relativeCostComplexity_append_sources_right
    (interpretation : Interpretation σ U) (operationCost : OperationCost σ)
    (target : X → Fin m → U) (sources : X → Fin n → U) :
    relativeCostComplexity interpretation operationCost
      (fun x => Fin.append (target x) (sources x)) sources =
      relativeCostComplexity interpretation operationCost target sources := by
  apply le_antisymm
  · simpa using relativeCostComplexity_pair_le interpretation operationCost target sources sources
  · simpa only [Fin.append_left] using relativeCostComplexity_map_outputs_le
      interpretation operationCost (fun x => Fin.append (target x) (sources x)) sources (Fin.castAdd n)

end Cslib.Circuits.Circuit

namespace Algebraic.Circuit

export Cslib.Circuits.Circuit
  (ComputesFrom relativeCostComplexity relativeGateComplexity relativeCostComplexity_le
   le_relativeCostComplexity relativeCostComplexity_le_iff relativeCostComplexity_lt_top_iff
   relativeCostComplexity_eq_top_iff relativeGateComplexity_le_iff relativeGateComplexity_eq_zero_iff
   relativeCostComplexity_id relativeCostComplexity_select relativeCostComplexity_self
   relativeCostComplexity_triangle relativeGateComplexity_triangle relativeCostComplexity_pair_le
   relativeCostComplexity_eq_of_mutually_free
   relativeCostComplexity_mono_sources relativeCostComplexity_map_outputs_le
   relativeCostComplexity_pair_eq_of_left_eq_zero
   relativeCostComplexity_eq_iInf relativeCostComplexity_precomp_le
   relativeCostComplexity_precomp_triangle relativeCostComplexity_precomp_eq
   relativeCostComplexity_eq_top_of_fiber_collision
   relativeCostComplexity_lt_top_iff_factorsThrough relativeCostComplexity_eq_of_rightInverse
   relativeCostComplexity_eq_of_equiv relativeCostComplexity_reindex_sources
   relativeCostComplexity_reindex_outputs relativeCostComplexity_append_sources
   relativeCostComplexity_append_sources_right)

end Algebraic.Circuit

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation.Optimal
public import Complexitylib.Algebraic.Translation.Metric
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.ENat.Lattice

/-!
# Minimum circuit complexity

Complexity is the infimum of the costs of all circuits computing a target,
valued in the extended natural numbers. Nonrepresentable targets therefore
have complexity `⊤`, while representable targets recover an ordinary minimum.
-/

@[expose] public section

namespace Algebraic

/-- Minimum weighted cost of a target. The value is `⊤` when no circuit
computes the target. -/
noncomputable def _root_.Cslib.Circuits.Circuit.costComplexity
    (interpretation : Interpretation σ U)
    (operationCost : OperationCost σ)
    (target : Target U n m) : ℕ∞ :=
  ⨅ g, ⨅ circuit : Circuit σ n g m,
    ⨅ _ : circuit.ComputesWith interpretation target,
      (circuit.cost operationCost : ℕ∞)

export Cslib.Circuits (Circuit.costComplexity)

/-- Minimum gate count of a target. -/
noncomputable def _root_.Cslib.Circuits.Circuit.gateComplexity
    (interpretation : Interpretation σ U)
    (target : Target U n m) : ℕ∞ :=
  Circuit.costComplexity interpretation OperationCost.unit target

export Cslib.Circuits (Circuit.gateComplexity)

namespace Circuit

/-- Any concrete implementation upper-bounds minimum weighted complexity. -/
theorem _root_.Cslib.Circuits.Circuit.costComplexity_le
    {circuit : Circuit σ n g m}
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (operationCost : OperationCost σ)
    (computes : circuit.ComputesWith interpretation target) :
    Circuit.costComplexity interpretation operationCost target ≤
      circuit.cost operationCost := by
  unfold Circuit.costComplexity
  exact iInf_le_of_le g <| iInf_le_of_le circuit <|
    iInf_le_of_le computes le_rfl

export Cslib.Circuits.Circuit (costComplexity_le)

/-- A uniform lower bound on all implementations lower-bounds minimum
weighted complexity. -/
theorem _root_.Cslib.Circuits.Circuit.le_costComplexity
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (operationCost : OperationCost σ)
    (bound : ℕ∞)
    (lowerBound : ∀ {g} (circuit : Circuit σ n g m),
      circuit.ComputesWith interpretation target →
        bound ≤ circuit.cost operationCost) :
    bound ≤ Circuit.costComplexity interpretation operationCost target := by
  unfold Circuit.costComplexity
  refine le_iInf fun g => le_iInf fun circuit => le_iInf fun computes => ?_
  exact lowerBound circuit computes

export Cslib.Circuits.Circuit (le_costComplexity)

/-- Characterization of a weighted complexity lower bound by all concrete
implementations. -/
theorem _root_.Cslib.Circuits.Circuit.le_costComplexity_iff
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (operationCost : OperationCost σ)
    (bound : ℕ∞) :
    bound ≤ Circuit.costComplexity interpretation operationCost target ↔
      ∀ {g} (circuit : Circuit σ n g m),
        circuit.ComputesWith interpretation target →
          bound ≤ circuit.cost operationCost := by
  constructor
  · intro bounded g circuit computes
    exact bounded.trans (circuit.costComplexity_le operationCost computes)
  · exact Circuit.le_costComplexity operationCost bound

export Cslib.Circuits.Circuit (le_costComplexity_iff)

/-- Weighted complexity is finite exactly when the target is representable. -/
theorem _root_.Cslib.Circuits.Circuit.costComplexity_lt_top_iff
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (operationCost : OperationCost σ) :
    Circuit.costComplexity interpretation operationCost target < ⊤ ↔
      ∃ g, ∃ circuit : Circuit σ n g m,
        circuit.ComputesWith interpretation target := by
  constructor
  · intro finite
    unfold Circuit.costComplexity at finite
    rw [iInf_lt_iff] at finite
    obtain ⟨g, finite⟩ := finite
    rw [iInf_lt_iff] at finite
    obtain ⟨circuit, finite⟩ := finite
    rw [iInf_lt_iff] at finite
    obtain ⟨computes, _⟩ := finite
    exact ⟨g, circuit, computes⟩
  · rintro ⟨g, circuit, computes⟩
    exact (circuit.costComplexity_le operationCost computes).trans_lt
      (ENat.natCast_lt_top _)

export Cslib.Circuits.Circuit (costComplexity_lt_top_iff)

@[simp] theorem _root_.Cslib.Circuits.Circuit.costComplexity_eq_top_iff
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (operationCost : OperationCost σ) :
    Circuit.costComplexity interpretation operationCost target = ⊤ ↔
      ¬ ∃ g, ∃ circuit : Circuit σ n g m,
        circuit.ComputesWith interpretation target := by
  rw [eq_top_iff, ← not_lt, Circuit.costComplexity_lt_top_iff]

export Cslib.Circuits.Circuit (costComplexity_eq_top_iff)

/-- A minimum-cost concrete circuit realizes the extended-natural complexity. -/
theorem _root_.Cslib.Circuits.Circuit.costComplexity_eq
    {circuit : Circuit σ n g m}
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (operationCost : OperationCost σ)
    (computes : circuit.ComputesWith interpretation target)
    (minimal : circuit.CostMinimal operationCost interpretation target) :
    Circuit.costComplexity interpretation operationCost target =
      circuit.cost operationCost := by
  apply le_antisymm (circuit.costComplexity_le operationCost computes)
  apply Circuit.le_costComplexity
  intro h competitor competitorComputes
  exact_mod_cast minimal competitor competitorComputes

export Cslib.Circuits.Circuit (costComplexity_eq)

/-- Any concrete implementation upper-bounds minimum gate complexity. -/
theorem _root_.Cslib.Circuits.Circuit.gateComplexity_le
    {circuit : Circuit σ n g m}
    {interpretation : Interpretation σ U}
    {target : Target U n m}
    (computes : circuit.ComputesWith interpretation target) :
    Circuit.gateComplexity interpretation target ≤ circuit.size := by
  simpa [Circuit.gateComplexity] using
    circuit.costComplexity_le OperationCost.unit computes

export Cslib.Circuits.Circuit (gateComplexity_le)

end Circuit

namespace Translation

/-- Compilation makes target-basis weighted complexity no larger than source
complexity charged by the exact pulled-back cost. -/
theorem costComplexity_le
    (translation : Translation σ τ)
    (interpretation : Interpretation τ U)
    (operationCost : OperationCost τ)
    (target : Target U n m) :
    Circuit.costComplexity interpretation operationCost target ≤
      Circuit.costComplexity (translation.pull interpretation)
        (translation.pullCost operationCost) target := by
  apply Circuit.le_costComplexity
  intro g circuit computes
  have compiledComputes :
      (translation.compile circuit).ComputesWith interpretation target := by
    intro input
    exact (translation.compile_eval circuit interpretation input).trans
      (computes input)
  have upper := (translation.compile circuit).costComplexity_le
    operationCost compiledComputes
  simpa [translation.compile_cost circuit operationCost] using upper

/-- A uniform local `K`-gate simulation gives the conventional multiplicative
gate-complexity comparison. The positivity assumption avoids the indeterminate
`0 * ⊤` case. -/
theorem gateComplexity_le_mul
    (translation : Translation σ τ)
    (interpretation : Interpretation τ U)
    (target : Target U n m)
    (positive : 1 ≤ K)
    (bounded : ∀ op, (translation.operation op).size ≤ K) :
    Circuit.gateComplexity interpretation target ≤
      (K : ℕ∞) * Circuit.gateComplexity
        (translation.pull interpretation) target := by
  let sourceComplexity := Circuit.gateComplexity
    (translation.pull interpretation) target
  have pointwise : ∀ {g} (circuit : Circuit σ n g m),
      circuit.ComputesWith (translation.pull interpretation) target →
        Circuit.gateComplexity interpretation target ≤
          (K : ℕ∞) * circuit.size := by
    intro g circuit computes
    have compiledComputes :
        (translation.compile circuit).ComputesWith interpretation target := by
      intro input
      exact (translation.compile_eval circuit interpretation input).trans
        (computes input)
    exact (translation.compile circuit).gateComplexity_le compiledComputes |>.trans
      (by exact_mod_cast translation.compile_size_le_mul circuit bounded)
  change Circuit.gateComplexity interpretation target ≤
    (K : ℕ∞) * sourceComplexity
  change Circuit.gateComplexity interpretation target ≤
    (K : ℕ∞) *
      (⨅ g, ⨅ circuit : Circuit σ n g m,
        ⨅ _ : circuit.ComputesWith (translation.pull interpretation) target,
          (circuit.cost OperationCost.unit : ℕ∞))
  have nonzero : (K : ℕ∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  rw [ENat.mul_iInf_of_ne nonzero]
  refine le_iInf fun g => ?_
  rw [ENat.mul_iInf_of_ne nonzero]
  refine le_iInf fun circuit => ?_
  rw [ENat.mul_iInf_of_ne nonzero]
  refine le_iInf fun computes => ?_
  simpa using pointwise circuit computes

/-- Transport a target-basis size lower bound through a uniformly bounded
translation, without introducing a global complexity value. -/
theorem transport_sizeLowerBound
    (translation : Translation σ τ)
    (interpretation : Interpretation τ U)
    (target : Target U n m)
    (lowerBound : ∀ {h} (targetCircuit : Circuit τ n h m),
      targetCircuit.ComputesWith interpretation target →
        L ≤ targetCircuit.size)
    (bounded : ∀ op, (translation.operation op).size ≤ K)
    (circuit : Circuit σ n g m)
    (computes : circuit.ComputesWith (translation.pull interpretation) target) :
    L ≤ K * circuit.size := by
  have compiledComputes :
      (translation.compile circuit).ComputesWith interpretation target := by
    intro input
    exact (translation.compile_eval circuit interpretation input).trans
      (computes input)
  exact (lowerBound (translation.compile circuit) compiledComputes).trans
    (translation.compile_size_le_mul circuit bounded)

/-- Division form of `transport_sizeLowerBound`. -/
theorem transport_sizeLowerBound_ceilDiv
    (translation : Translation σ τ)
    (interpretation : Interpretation τ U)
    (target : Target U n m)
    (positive : 0 < K)
    (lowerBound : ∀ {h} (targetCircuit : Circuit τ n h m),
      targetCircuit.ComputesWith interpretation target →
        L ≤ targetCircuit.size)
    (bounded : ∀ op, (translation.operation op).size ≤ K)
    (circuit : Circuit σ n g m)
    (computes : circuit.ComputesWith (translation.pull interpretation) target) :
    L ⌈/⌉ K ≤ circuit.size := by
  rw [ceilDiv_le_iff_le_mul positive]
  exact translation.transport_sizeLowerBound interpretation target lowerBound
    bounded circuit computes

end Translation

namespace Realization

/-- Intrinsic operation cost is exactly the target-basis complexity of that
source operation. -/
theorem operation_costComplexity_eq_minimumCost
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (operationCost : OperationCost τ)
    (op : σ.Op) :
    Circuit.costComplexity targetInterpretation operationCost
        (source.operationTarget op) =
      realization.minimumCost operationCost op := by
  let optimal := realization.minimize operationCost
  change Circuit.costComplexity targetInterpretation operationCost
      (source.operationTarget op) =
    (optimal.operation op).cost operationCost
  exact Circuit.costComplexity_eq operationCost
    (optimal.toRealization.operation_computes op) (optimal.optimal op)

/-- Complexity comparison specialized to a realization of named source and
target interpretations. -/
theorem costComplexity_le
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (operationCost : OperationCost τ)
    (target : Target U n m) :
    Circuit.costComplexity targetInterpretation operationCost target ≤
      Circuit.costComplexity source
        (realization.pullCost operationCost) target := by
  calc
    Circuit.costComplexity targetInterpretation operationCost target ≤
        Circuit.costComplexity
          (realization.toTranslation.pull targetInterpretation)
          (realization.toTranslation.pullCost operationCost) target :=
      realization.toTranslation.costComplexity_le targetInterpretation
        operationCost target
    _ = Circuit.costComplexity source
        (realization.toTranslation.pullCost operationCost) target :=
      congrArg
        (fun interpretation => Circuit.costComplexity interpretation
          (realization.toTranslation.pullCost operationCost) target)
        realization.realizes
    _ = _ := rfl

/-- The intrinsic, minimum-operation-cost form of complexity transport. -/
theorem costComplexity_le_minimumCost
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (operationCost : OperationCost τ)
    (target : Target U n m) :
    Circuit.costComplexity targetInterpretation operationCost target ≤
      Circuit.costComplexity source
        (realization.minimumCost operationCost) target := by
  exact (realization.minimize operationCost).toRealization.costComplexity_le
    operationCost target

/-- Uniformly bounded realization gadgets give the conventional
multiplicative comparison of gate complexities. -/
theorem gateComplexity_le_mul
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (target : Target U n m)
    (positive : 1 ≤ K)
    (bounded : ∀ op, (realization.operation op).size ≤ K) :
    Circuit.gateComplexity targetInterpretation target ≤
      (K : ℕ∞) * Circuit.gateComplexity source target := by
  calc
    Circuit.gateComplexity targetInterpretation target ≤
        (K : ℕ∞) * Circuit.gateComplexity
          (realization.toTranslation.pull targetInterpretation) target :=
      realization.toTranslation.gateComplexity_le_mul
        targetInterpretation target positive bounded
    _ = (K : ℕ∞) * Circuit.gateComplexity source target :=
      congrArg (fun interpretation =>
        (K : ℕ∞) * Circuit.gateComplexity interpretation target)
        realization.realizes

/-- Gate complexity changes by at most the selected realization's normalized
local overhead. -/
theorem gateComplexity_le_mul_overhead
    [Fintype σ.Op]
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (target : Target U n m) :
    Circuit.gateComplexity targetInterpretation target ≤
      (realization.overhead : ℕ∞) *
        Circuit.gateComplexity source target :=
  realization.gateComplexity_le_mul target realization.one_le_overhead
    realization.operation_size_le_overhead

/-- Per-circuit constant-factor lower-bound transport through a realization. -/
theorem transport_sizeLowerBound
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (target : Target U n m)
    (lowerBound : ∀ {h} (targetCircuit : Circuit τ n h m),
      targetCircuit.ComputesWith targetInterpretation target →
        L ≤ targetCircuit.size)
    (bounded : ∀ op, (realization.operation op).size ≤ K)
    (circuit : Circuit σ n g m)
    (computes : circuit.ComputesWith source target) :
    L ≤ K * circuit.size := by
  have computesPull :
      circuit.ComputesWith
        (realization.toTranslation.pull targetInterpretation) target := by
    intro input
    rw [realization.realizes]
    exact computes input
  exact realization.toTranslation.transport_sizeLowerBound
    targetInterpretation target lowerBound bounded circuit computesPull

/-- Division form of constant-factor lower-bound transport through a
realization. -/
theorem transport_sizeLowerBound_ceilDiv
    {source : Interpretation σ U}
    {targetInterpretation : Interpretation τ U}
    (realization : Realization σ τ source targetInterpretation)
    (target : Target U n m)
    (positive : 0 < K)
    (lowerBound : ∀ {h} (targetCircuit : Circuit τ n h m),
      targetCircuit.ComputesWith targetInterpretation target →
        L ≤ targetCircuit.size)
    (bounded : ∀ op, (realization.operation op).size ≤ K)
    (circuit : Circuit σ n g m)
    (computes : circuit.ComputesWith source target) :
    L ⌈/⌉ K ≤ circuit.size := by
  rw [ceilDiv_le_iff_le_mul positive]
  exact realization.transport_sizeLowerBound target lowerBound bounded circuit
    computes

end Realization

namespace Interpretation

/-- Two finite, functionally complete interpreted signatures have linearly
equivalent gate complexities, with explicit constants supplied by realizations
of their operation sets. -/
theorem _root_.Cslib.Circuits.Interpretation.gateComplexity_linearlyEquivalent_of_functionallyComplete
    [Fintype σ.Op] [Fintype τ.Op]
    (first : Interpretation σ U)
    (second : Interpretation τ U)
    (firstComplete : first.FunctionallyComplete)
    (secondComplete : second.FunctionallyComplete) :
    ∃ forward backward : Nat,
      1 ≤ forward ∧ 1 ≤ backward ∧
      (∀ {n m} (target : Target U n m),
        Circuit.gateComplexity second target ≤
          (forward : ℕ∞) * Circuit.gateComplexity first target) ∧
      (∀ {n m} (target : Target U n m),
        Circuit.gateComplexity first target ≤
          (backward : ℕ∞) * Circuit.gateComplexity second target) := by
  let toSecond := Realization.ofFunctionalCompleteness first second
    secondComplete
  let toFirst := Realization.ofFunctionalCompleteness second first
    firstComplete
  exact ⟨toSecond.overhead, toFirst.overhead,
    toSecond.one_le_overhead, toFirst.one_le_overhead,
    fun target => toSecond.gateComplexity_le_mul_overhead target,
    fun target => toFirst.gateComplexity_le_mul_overhead target⟩

export Cslib.Circuits.Interpretation (gateComplexity_linearlyEquivalent_of_functionallyComplete)

end Interpretation

end Algebraic

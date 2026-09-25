/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian
public import Complexitylib.Algebraic.Complexity.Relative
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Hessian lower bounds with arbitrary polynomial sources

Pass to the quotient by the span of the supplied Hessians. In this quotient
the free inputs have zero feature, so interaction-span Fusion applies. Lift
the resulting span membership back to matrices: subtracting a linear
combination of source Hessians leaves rank at most twice multiplication cost.
All statements use formal polynomial equality and work in every characteristic.
-/

@[expose] public section

namespace Algebraic.Fusion.Arithmetic.Interaction.Hessian

open Cardinal

noncomputable section

variable {K : Type} {σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

/-- Arbitrary supplied polynomial values contribute their Hessians for free.
The coefficients may depend on both the circuit and the evaluation point. -/
theorem exists_source_hessian_residual
    (constant : C → K) (problem : Problem (MvPolynomial σ K)) (point : σ → K)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation (fun scalar => MvPolynomial.C (constant scalar)))) :
    ∃ coefficients : Fin problem.inputCount → K,
      LinearMap.rank (linearMap point problem.target -
        ∑ i, coefficients i • linearMap point (problem.inputs i)) ≤
          2 * (circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := C)) : Cardinal) := by
  classical
  let sources := Submodule.span K (Set.range fun i => linearMap point (problem.inputs i))
  let certificate : Certificate (K := K)
      (Q := (((σ → K) →ₗ[K] (σ → K)) ⧸ sources))
      (fun scalar => MvPolynomial.C (constant scalar)) problem := {
    feature := fun value => sources.mkQ (linearMap point value)
    interaction := fun left right => sources.mkQ (interaction point left right)
    input_zero := fun i => (Submodule.Quotient.mk_eq_zero sources).mpr
      (Submodule.subset_span ⟨i, rfl⟩)
    feature_add := fun left right => by simp
    constant_zero := fun scalar => by simp
    feature_mul := fun left right =>
      ⟨MvPolynomial.eval point right, MvPolynomial.eval point left, by
        simp only [linearMap_mul, map_add, map_smul]⟩
  }
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation (fun scalar => MvPolynomial.C (constant scalar)))
      problem.inputs
  let terms := (multiplicationArguments atoms).map fun arguments =>
    interaction point (arguments 0) (arguments 1)
  let residuals := Submodule.span K (Set.range fun i => terms.get i)
  have terms_eq : interactions certificate atoms = terms.map sources.mkQ := by
    rw [interactions_eq_map_multiplicationArguments]
    simp only [terms, List.map_map]
    rfl
  have target_mem : sources.mkQ (linearMap point problem.target) ∈
      residuals.map sources.mkQ := by
    apply (Submodule.span_le.mpr ?_)
      (targetFeature_mem_circuitSubmodule certificate circuit constructs)
    have included : ∀ value, value ∈ interactions certificate atoms →
        value ∈ residuals.map sources.mkQ := by
      intro value present
      rw [terms_eq, List.mem_map] at present
      obtain ⟨term, present, equal⟩ := present
      obtain ⟨j, equalTerm⟩ := List.mem_iff_get.mp present
      exact Submodule.mem_map.mpr
        ⟨term, Submodule.subset_span ⟨j, equalTerm⟩, equal⟩
    rintro value ⟨i, rfl⟩
    exact included _ (List.get_mem _ i)
  obtain ⟨residual, residual_mem, same_quotient⟩ := Submodule.mem_map.mp target_mem
  have source_mem : linearMap point problem.target - residual ∈ sources := by
    apply (Submodule.Quotient.mk_eq_zero sources).mp
    change sources.mkQ (linearMap point problem.target - residual) = 0
    rw [map_sub, same_quotient, sub_self]
  obtain ⟨coefficients, decomposition⟩ :=
    (Submodule.mem_span_range_iff_exists_fun K).mp source_mem
  refine ⟨coefficients, ?_⟩
  rw [decomposition, sub_sub_cancel]
  have bound := LinearMap.rank_le_sum_of_mem_span residual
    (fun i => terms.get i) (fun _ => 2) residual_mem (fun i => ?_)
  · have length_eq : terms.length =
        circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
      simp only [terms, List.length_map, multiplicationArguments_length]
      exact circuitAtoms_cost _ _ _ _
    simpa [length_eq, mul_comm] using bound
  · have present := List.get_mem terms i
    obtain ⟨arguments, _, equal⟩ := List.mem_map.mp present
    rw [← equal]
    exact rank_interaction_le_two point _ _

/-- With raw polynomial generators and helpers supplied, only the helpers
need coefficients in the residual: the raw generators have zero Hessian. -/
theorem exists_helper_hessian_residual
    (constant : C → K) (target : MvPolynomial (Fin n) K)
    (supplied : Fin k → MvPolynomial (Fin n) K) (point : Fin n → K)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (n + k) g 1)
    (computes : circuit.eval
      (Algebraic.Arithmetic.interpretation (fun scalar => MvPolynomial.C (constant scalar)))
      (Fin.append MvPolynomial.X supplied) 0 = target) :
    ∃ coefficients : Fin k → K,
      LinearMap.rank (linearMap point target -
        ∑ j, coefficients j • linearMap point (supplied j)) ≤
          2 * (circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := C)) : Cardinal) := by
  let problem : Problem (MvPolynomial (Fin n) K) :=
    ⟨n + k, Fin.append MvPolynomial.X supplied, target⟩
  obtain ⟨coefficients, bound⟩ :=
    exists_source_hessian_residual constant problem point circuit computes
  refine ⟨fun j => coefficients (Fin.natAdd n j), ?_⟩
  simpa only [problem, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    linearMap_X, smul_zero, Finset.sum_const_zero, zero_add] using bound

/-- Minimum rank remaining after subtracting a linear combination of the
supplied Hessians. This is an ordinary matrix rank, recorded in `ℕ∞`. -/
def residualRank (point : σ → K) (target : MvPolynomial σ K)
    (sources : Fin n → MvPolynomial σ K) : ℕ∞ :=
  ⨅ coefficients : Fin n → K,
    (Module.finrank K (LinearMap.range (linearMap point target -
      ∑ i, coefficients i • linearMap point (sources i))) : ℕ∞)

/-- Minimum residual Hessian rank is at most twice relative multiplication
complexity, including the case of unrepresentable targets. -/
theorem residualRank_le_twice_relativeCostComplexity
    (constant : C → K) (target : MvPolynomial σ K)
    (sources : Fin n → MvPolynomial σ K) (point : σ → K) :
    residualRank point target sources ≤ 2 * Circuit.relativeCostComplexity
      (Algebraic.Arithmetic.interpretation (fun scalar => MvPolynomial.C (constant scalar)))
      (Algebraic.Arithmetic.multiplicationCost (K := C))
      (fun (_ : Unit) (_ : Fin 1) => target) (fun _ => sources) := by
  unfold Circuit.relativeCostComplexity
  simp only [ENat.mul_iInf_of_ne (by decide : (2 : ℕ∞) ≠ 0)]
  refine le_iInf fun gates => le_iInf fun circuit => le_iInf fun computes => ?_
  let problem : Problem (MvPolynomial σ K) := ⟨n, sources, target⟩
  obtain ⟨coefficients, bound⟩ := exists_source_hessian_residual constant problem point
    circuit (congrFun (computes ()) 0)
  have natural : Module.finrank K (LinearMap.range (linearMap point target -
      ∑ i, coefficients i • linearMap point (sources i))) ≤
        2 * circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
    rw [LinearMap.rank, ← Module.finrank_eq_rank] at bound
    exact_mod_cast bound
  exact (iInf_le_of_le coefficients le_rfl).trans (by exact_mod_cast natural)

/-- Conditional form of the rank bound, with the original polynomial
variables available for free alongside the helper polynomials. -/
theorem residualRank_le_twice_with_helpers
    (constant : C → K) (target : MvPolynomial (Fin n) K)
    (supplied : Fin k → MvPolynomial (Fin n) K) (point : Fin n → K) :
    residualRank point target supplied ≤ 2 * Circuit.relativeCostComplexity
      (Algebraic.Arithmetic.interpretation (fun scalar => MvPolynomial.C (constant scalar)))
      (Algebraic.Arithmetic.multiplicationCost (K := C))
      (fun (_ : Unit) (_ : Fin 1) => target)
      (fun _ => Fin.append MvPolynomial.X supplied) := by
  have discard_variables : residualRank point target supplied ≤
      residualRank point target (Fin.append MvPolynomial.X supplied) := by
    unfold residualRank
    refine le_iInf fun coefficients => ?_
    have sum_eq : ∑ i, coefficients i • linearMap point (Fin.append MvPolynomial.X supplied i) =
        ∑ j, coefficients (Fin.natAdd n j) • linearMap point (supplied j) := by
      simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
        linearMap_X, smul_zero, Finset.sum_const_zero, zero_add]
    rw [sum_eq]
    exact iInf_le_of_le (fun j => coefficients (Fin.natAdd n j)) le_rfl
  exact discard_variables.trans
    (residualRank_le_twice_relativeCostComplexity constant target _ point)

/-- A uniform lower bound on every source-adjusted Hessian bounds relative
multiplication complexity. The source family can be completely arbitrary. -/
theorem relativeCostComplexity_lowerBound
    (constant : C → K) (target : MvPolynomial σ K)
    (sources : Fin n → MvPolynomial σ K) (point : σ → K) (lower : Nat)
    (hard : ∀ coefficients : Fin n → K,
      (2 * lower : Cardinal) ≤ LinearMap.rank
        (linearMap point target - ∑ i, coefficients i • linearMap point (sources i))) :
    (lower : ℕ∞) ≤ Circuit.relativeCostComplexity
      (Algebraic.Arithmetic.interpretation (fun scalar => MvPolynomial.C (constant scalar)))
      (Algebraic.Arithmetic.multiplicationCost (K := C))
      (fun (_ : Unit) (_ : Fin 1) => target) (fun _ => sources) := by
  apply Circuit.le_relativeCostComplexity
  intro gates circuit computes
  let problem : Problem (MvPolynomial σ K) := ⟨n, sources, target⟩
  have constructs : problem.Constructs circuit _ := congrFun (computes ()) 0
  obtain ⟨coefficients, bound⟩ :=
    exists_source_hessian_residual constant problem point circuit constructs
  have inequality := (hard coefficients).trans bound
  have natural : 2 * lower ≤
      2 * circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
    exact_mod_cast inequality
  exact_mod_cast (by omega : lower ≤
    circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := C)))

end

end Algebraic.Fusion.Arithmetic.Interaction.Hessian

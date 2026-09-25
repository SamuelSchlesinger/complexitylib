/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank

/-!
# Circuit-local interaction-rank bounds

The base rank certificate asks for a uniform rank bound on every possible
semantic multiplication interaction.  Restricted arithmetic models usually
only control the products that actually occur at circuit gates.

This module provides that local interface.  If every multiplication
interaction extracted from one evaluated circuit has rank at most `r`, while
the target feature has rank at least `R`, then `ceil(R / r)` multiplication
gates are necessary.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Rank
namespace Local

open Cardinal

variable {K : Type u} {C : Type v} {U : Type w}
variable {A : Type x} {B : Type y}
variable [Field K] [Add U] [Mul U]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

/-- A local rank restriction on exactly the multiplication interactions that
occur when evaluating a circuit on the problem's designated inputs. -/
def CircuitBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (interactionRank : Nat) : Prop :=
  ∀ interaction,
    interaction ∈ interactions certificate
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation constant) problem.inputs) →
    LinearMap.rank interaction ≤ interactionRank

/-- Nonuniform local-rank budget indexed by the actual retained interaction
occurrences of an evaluated circuit. -/
def IndexedBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (budget : Fin (interactions certificate
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation constant)
        problem.inputs)).length → Nat) : Prop :=
  ∀ index,
    LinearMap.rank
      ((interactions certificate
        (circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation constant)
          problem.inputs)).get index) ≤ budget index

/-- Equivalent-to-use atom-level formulation: bound the interaction created
by every multiplication atom in the evaluated circuit. -/
def MultiplicationBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (interactionRank : Nat) : Prop :=
  ∀ arguments : Fin 2 → U,
    (⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature C) U) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation constant) problem.inputs →
    LinearMap.rank
      (certificate.interaction
        (arguments (0 : Fin 2)) (arguments (1 : Fin 2))) ≤ interactionRank

/-- An atom-level multiplication bound implies the filtered-list circuit
bound used by the rank theorem. -/
theorem CircuitBound.of_multiplicationBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (interactionRank : Nat)
    (bound : MultiplicationBound certificate circuit interactionRank) :
    CircuitBound certificate circuit interactionRank := by
  intro interaction present
  change interaction ∈
    (circuitAtoms circuit
      (Algebraic.Arithmetic.interpretation constant)
      problem.inputs).filterMap (Atom.interaction? certificate) at present
  rw [List.mem_filterMap] at present
  obtain ⟨atom, atomPresent, interactionEqual⟩ := present
  cases atom with
  | mk op arguments =>
      cases op with
      | add =>
          simp [Atom.interaction?] at interactionEqual
      | mul =>
          change Fin 2 → U at arguments
          simp only [Atom.interaction?] at interactionEqual
          rw [← Option.some.inj interactionEqual]
          exact bound arguments atomPresent
      | constant scalar =>
          simp [Atom.interaction?] at interactionEqual

/-- The target feature rank is bounded by the sum of nonuniform local
interaction-rank budgets. -/
theorem target_rank_le_sum_indexedBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget : Fin (interactions certificate
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation constant)
        problem.inputs)).length → Nat)
    (localBound : IndexedBound certificate circuit budget) :
    LinearMap.rank (certificate.feature problem.target) ≤
      ∑ index, (budget index : Cardinal) := by
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation constant) problem.inputs
  let interactionFeature : Fin (interactions certificate atoms).length →
      (A →ₗ[K] B) :=
    fun index => (interactions certificate atoms).get index
  apply LinearMap.rank_le_sum_of_mem_span
    (certificate.feature problem.target) interactionFeature budget
  · simpa [generatedSubmodule, interactionFeature, atoms] using
      targetFeature_mem_circuitSubmodule certificate circuit constructs
  · exact localBound

/-- Natural-number form of the nonuniform indexed-budget inequality. -/
theorem targetRank_le_sum_indexedBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget : Fin (interactions certificate
      (circuitAtoms circuit
        (Algebraic.Arithmetic.interpretation constant)
        problem.inputs)).length → Nat)
    (localBound : IndexedBound certificate circuit budget) :
    targetRank ≤ ∑ index, budget index := by
  have cardinalBound : (targetRank : Cardinal) ≤
      ∑ index, (budget index : Cardinal) :=
    target_rank_ge.trans
      (target_rank_le_sum_indexedBudget certificate circuit constructs budget
        localBound)
  exact_mod_cast cardinalBound

/-- Under a circuit-local rank bound, the target feature rank is at most the
number of multiplication gates times the local bound. -/
theorem target_rank_le_mul_multiplicationCost
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (interactionRank : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (localBound : CircuitBound certificate circuit interactionRank) :
    LinearMap.rank (certificate.feature problem.target) ≤
      (circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) : Cardinal) *
          interactionRank := by
  classical
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation constant) problem.inputs
  let interactionFeature : Fin (interactions certificate atoms).length →
      (A →ₗ[K] B) :=
    fun index => (interactions certificate atoms).get index
  have targetMem : certificate.feature problem.target ∈
      Submodule.span K (Set.range interactionFeature) := by
    simpa [generatedSubmodule, interactionFeature, atoms] using
      targetFeature_mem_circuitSubmodule certificate circuit constructs
  have targetMemImage : certificate.feature problem.target ∈
      Submodule.span K
        (interactionFeature ''
          (Finset.univ : Finset
            (Fin (interactions certificate atoms).length))) := by
    simpa [Set.image_univ] using targetMem
  obtain ⟨coefficients, coefficientsSpec⟩ :=
    (Submodule.mem_span_image_finset_iff_exists_fun
      (R := K) (v := interactionFeature)).mp targetMemImage
  have rankBound : LinearMap.rank (certificate.feature problem.target) ≤
      ((interactions certificate atoms).length : Cardinal) *
        interactionRank := by
    rw [← coefficientsSpec]
    calc
      LinearMap.rank
          (∑ index, coefficients index • interactionFeature index) ≤
          ∑ index,
            LinearMap.rank (coefficients index • interactionFeature index) := by
        simpa using LinearMap.rank_finsetSum_le
          (Finset.univ : Finset
            ((Finset.univ : Finset
              (Fin (interactions certificate atoms).length)) : Type))
          (fun index => coefficients index • interactionFeature index)
      _ ≤ ∑ _index, (interactionRank : Cardinal) := by
        apply Finset.sum_le_sum
        intro index _
        exact (LinearMap.rank_smul_le
          (coefficients index) (interactionFeature index)).trans
            (localBound (interactionFeature index) (by
              simp [CircuitBound, interactionFeature, atoms] at localBound ⊢))
      _ = ((interactions certificate atoms).length : Cardinal) *
          interactionRank := by
        simp [nsmul_eq_mul]
  have interactionsLength : (interactions certificate atoms).length =
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
    calc
      (interactions certificate atoms).length =
          Atom.listCost atoms
            (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
        interactions_length certificate atoms
      _ = circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
        simpa [atoms] using circuitAtoms_cost circuit
          (Algebraic.Arithmetic.interpretation constant) problem.inputs
          (Algebraic.Arithmetic.multiplicationCost (K := C))
  simpa [interactionsLength] using rankBound

/-- Natural-number target rank is bounded by local rank times multiplication
cost. -/
theorem targetRank_le_mul_multiplicationCost
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank interactionRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (localBound : CircuitBound certificate circuit interactionRank) :
    targetRank ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) *
        interactionRank := by
  have cardinalBound : (targetRank : Cardinal) ≤
      (circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) : Cardinal) *
          interactionRank :=
    target_rank_ge.trans
      (target_rank_le_mul_multiplicationCost certificate interactionRank
        circuit constructs localBound)
  exact_mod_cast cardinalBound

/-- Circuit-local interaction rank yields a multiplication lower bound. -/
theorem circuit_lowerBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank interactionRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (positive : 0 < interactionRank)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (localBound : CircuitBound certificate circuit interactionRank) :
    targetRank ⌈/⌉ interactionRank ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  (ceilDiv_le_iff_le_mul positive).2
    (by simpa [Nat.mul_comm] using
      (targetRank_le_mul_multiplicationCost certificate targetRank
        interactionRank target_rank_ge circuit constructs localBound))

end Local
end Rank
end Interaction
end Arithmetic
end Fusion
end Algebraic

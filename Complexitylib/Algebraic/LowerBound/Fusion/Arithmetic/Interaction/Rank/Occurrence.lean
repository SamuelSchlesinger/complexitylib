/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Rank.Local
public import Mathlib.Data.Fintype.Lattice

/-!
# Multiplication-occurrence rank budgets

Present the nonuniform interaction-rank theorem directly in terms of the
evaluated multiplication gates of an arithmetic circuit.  This avoids asking
clients to index a second, certificate-dependent filtered list while retaining
one budget entry for every gate occurrence, including repeated semantic
products.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Rank
namespace Occurrence

open Cardinal

variable {K : Type u} {C : Type v} {U : Type w}
variable {A : Type x} {B : Type y}
variable [Field K] [Add U] [Mul U]
variable [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B]

/-- A positive quantity bounded by a finite sum forces one summand to reach
its ceiling average.  Positivity also rules out an empty index type. -/
theorem exists_budget_ge_ceilDiv
    (targetRank : Nat)
    (targetPositive : 0 < targetRank)
    (budget : Fin count → Nat)
    (target_le_sum : targetRank ≤ ∑ index, budget index) :
    ∃ index, targetRank ⌈/⌉ count ≤ budget index := by
  have countPositive : 0 < count := by
    by_contra notPositive
    have countZero : count = 0 := Nat.eq_zero_of_not_pos notPositive
    subst count
    simp at target_le_sum
    omega
  let _ : Nonempty (Fin count) := Fin.pos_iff_nonempty.mp countPositive
  obtain ⟨index, maximal⟩ := Finite.exists_max budget
  refine ⟨index, (ceilDiv_le_iff_le_mul countPositive).2 ?_⟩
  exact target_le_sum.trans (by
    calc
      (∑ candidate, budget candidate) ≤
          ∑ _candidate : Fin count, budget index := by
        apply Finset.sum_le_sum
        intro candidate _
        exact maximal candidate
      _ = count * budget index := by simp)

/-- The interaction map created by a particular evaluated multiplication-gate
occurrence. -/
def interactionFamily
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1) :
    Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
      (A →ₗ[K] B) :=
  fun index =>
    let arguments :=
      (circuitMultiplicationArguments constant problem.inputs circuit).get index
    certificate.interaction
      (arguments (0 : Fin 2)) (arguments (1 : Fin 2))

/-- Nonuniform rank budget indexed directly by evaluated multiplication-gate
occurrences. -/
def IndexedBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (budget :
      Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
        Nat) : Prop :=
  ∀ index,
    LinearMap.rank (interactionFamily certificate circuit index) ≤ budget index

/-- A semantic budget function can be checked on membership in the
multiplication-occurrence list.  The final sum still counts duplicate
occurrences separately. -/
def ArgumentBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (budget : (Fin 2 → U) → Nat) : Prop :=
  ∀ arguments,
    arguments ∈
      circuitMultiplicationArguments constant problem.inputs circuit →
    LinearMap.rank
      (certificate.interaction
        (arguments (0 : Fin 2)) (arguments (1 : Fin 2))) ≤ budget arguments

/-- The target feature is spanned by the occurrence-indexed interaction
family. -/
theorem targetFeature_mem_span
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant)) :
    certificate.feature problem.target ∈
      Submodule.span K (Set.range (interactionFamily certificate circuit)) := by
  let atoms := circuitAtoms circuit
    (Algebraic.Arithmetic.interpretation constant) problem.inputs
  apply (show generatedSubmodule certificate atoms ≤
      Submodule.span K (Set.range (interactionFamily certificate circuit))
    from ?_)
  · simpa [atoms] using
      targetFeature_mem_circuitSubmodule certificate circuit constructs
  · rw [generatedSubmodule]
    apply Submodule.span_le.2
    intro interaction present
    obtain ⟨interactionIndex, interactionEqual⟩ := present
    have interactionPresent : interaction ∈
        interactions certificate atoms := by
      rw [← interactionEqual]
      exact List.get_mem _ interactionIndex
    rw [interactions_eq_map_multiplicationArguments certificate atoms,
      List.mem_map] at interactionPresent
    obtain ⟨arguments, argumentsPresent, argumentsEqual⟩ :=
      interactionPresent
    rw [← argumentsEqual]
    apply Submodule.subset_span
    obtain ⟨argumentIndex, argumentEqual⟩ :=
      List.mem_iff_get.mp argumentsPresent
    refine ⟨argumentIndex, ?_⟩
    change certificate.interaction
      ((multiplicationArguments atoms).get argumentIndex (0 : Fin 2))
      ((multiplicationArguments atoms).get argumentIndex (1 : Fin 2)) =
        certificate.interaction
          (arguments (0 : Fin 2)) (arguments (1 : Fin 2))
    rw [argumentEqual]

/-- An argument-indexed semantic budget induces an occurrence-indexed
budget by evaluating it at each gate's actual arguments. -/
theorem IndexedBound.of_argumentBound
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (budget : (Fin 2 → U) → Nat)
    (bound : ArgumentBound certificate circuit budget) :
    IndexedBound certificate circuit
      (fun index => budget
        ((circuitMultiplicationArguments constant problem.inputs circuit).get
          index)) := by
  intro index
  exact bound _ (List.get_mem _ index)

/-- Target rank is at most the sum of occurrence-indexed local rank budgets. -/
theorem target_rank_le_sum_indexedBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget :
      Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
        Nat)
    (localBound : IndexedBound certificate circuit budget) :
    LinearMap.rank (certificate.feature problem.target) ≤
      ∑ index, (budget index : Cardinal) :=
  LinearMap.rank_le_sum_of_mem_span
    (certificate.feature problem.target)
    (interactionFamily certificate circuit) budget
    (targetFeature_mem_span certificate circuit constructs) localBound

/-- Natural-number form of the occurrence-indexed rank inequality. -/
theorem targetRank_le_sum_indexedBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget :
      Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
        Nat)
    (localBound : IndexedBound certificate circuit budget) :
    targetRank ≤ ∑ index, budget index := by
  have cardinalBound : (targetRank : Cardinal) ≤
      ∑ index, (budget index : Cardinal) :=
    target_rank_ge.trans
      (target_rank_le_sum_indexedBudget certificate circuit constructs budget
        localBound)
  exact_mod_cast cardinalBound

/-- Some actual multiplication occurrence carries at least the ceiling
average of any positive certified target-rank lower bound. -/
theorem exists_occurrence_budget_ge_ceilDiv
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank : Nat)
    (targetPositive : 0 < targetRank)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget :
      Fin (circuitMultiplicationArguments constant problem.inputs circuit).length →
        Nat)
    (localBound : IndexedBound certificate circuit budget) :
    ∃ index,
      targetRank ⌈/⌉
          (circuitMultiplicationArguments constant problem.inputs circuit).length ≤
        budget index :=
  exists_budget_ge_ceilDiv targetRank targetPositive budget
    (targetRank_le_sum_indexedBudget certificate targetRank target_rank_ge
      circuit constructs budget localBound)

/-- A semantic argument budget bounds target rank by its list sum over actual
multiplication occurrences. -/
theorem targetRank_le_sum_argumentBudget
    {constant : C → U}
    {problem : Problem U}
    (certificate : Interaction.Certificate (K := K)
      (Q := A →ₗ[K] B) constant problem)
    (targetRank : Nat)
    (target_rank_ge : (targetRank : Cardinal) ≤
      LinearMap.rank (certificate.feature problem.target))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant))
    (budget : (Fin 2 → U) → Nat)
    (localBound : ArgumentBound certificate circuit budget) :
    targetRank ≤
      ((circuitMultiplicationArguments constant problem.inputs circuit).map
        budget).sum := by
  simpa [← Fin.sum_ofFn] using
    targetRank_le_sum_indexedBudget certificate targetRank target_rank_ge
      circuit constructs
      (fun index => budget
        ((circuitMultiplicationArguments constant problem.inputs circuit).get
          index))
      (IndexedBound.of_argumentBound certificate circuit budget localBound)

end Occurrence
end Rank
end Interaction
end Arithmetic
end Fusion
end Algebraic

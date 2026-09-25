/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Linear
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Combined

/-!
# Canonical quotient-feature Fusion

Quotient the semantic vector space by the linear span of every free input and
named constant.  The quotient map is then a canonical linear feature that
annihilates all zero-cost data.  Addition cannot create a new quotient
direction, while each multiplication can create at most one.

Consequently, the dimension of the requested outputs modulo free data is a
multiplication lower bound.  No hand-designed feature coordinates are needed.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Linear
namespace Quotient

noncomputable section

variable {K : Type u} {C : Type v} {U : Type w}

/-- Linear span of all semantic values available without a multiplication or
addition gate: free problem inputs and named scalar constants. -/
def freeSubmodule
    (K : Type u)
    [Semiring K]
    [AddCommMonoid U]
    [Module K U]
    (constant : C → U)
    (problem : Problem U) : Submodule K U :=
  Submodule.span K
    (Set.range problem.inputs ∪ Set.range constant)

/-- Every free input belongs to the free-data submodule. -/
theorem input_mem_freeSubmodule
    [Semiring K]
    [AddCommMonoid U]
    [Module K U]
    (constant : C → U)
    (problem : Problem U)
    (input : Fin problem.inputCount) :
    problem.inputs input ∈ freeSubmodule K constant problem := by
  apply Submodule.subset_span
  exact Set.mem_union_left _ ⟨input, rfl⟩

/-- Every named constant belongs to the free-data submodule. -/
theorem constant_mem_freeSubmodule
    [Semiring K]
    [AddCommMonoid U]
    [Module K U]
    (constant : C → U)
    (problem : Problem U)
    (scalar : C) :
    constant scalar ∈ freeSubmodule K constant problem := by
  apply Submodule.subset_span
  exact Set.mem_union_right _ ⟨scalar, rfl⟩

/-- Canonical interaction certificate obtained from quotienting by all free
semantic data. -/
def certificate
    [Field K]
    [AddCommGroup U]
    [Module K U]
    [Mul U]
    (constant : C → U)
    (problem : Problem U) :
    Certificate (K := K)
      (Q := U ⧸ freeSubmodule K constant problem) constant problem :=
  Linear.certificate constant problem
    (freeSubmodule K constant problem).mkQ
    (by
      intro input
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact input_mem_freeSubmodule constant problem input)
    (by
      intro scalar
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact constant_mem_freeSubmodule constant problem scalar)

/-- Dimension of the span of requested outputs modulo free inputs and named
constants. -/
def outputRank
    [Field K]
    [AddCommGroup U]
    [Module K U]
    (constant : C → U)
    (problem : Problem U)
    (targets : Fin m → U) : Nat :=
  Module.finrank K
    (Submodule.span K
      (Set.range ((freeSubmodule K constant problem).mkQ ∘ targets)))

/-- Canonical quotient-output rank lower-bounds multiplication cost. -/
theorem outputRank_le_multiplicationCost
    [Field K]
    [AddCommGroup U]
    [Module K U]
    [Mul U]
    (constant : C → U)
    (problem : Problem U)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m)
    (constructs : Multiple.Constructs (constant := constant)
      problem targets circuit) :
    outputRank (K := K) constant problem targets ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  exact Multiple.featureSpan_finrank_le_multiplicationCost
    (certificate constant problem) targets circuit constructs

/-- Linear independence modulo free data forces one multiplication per
requested output. -/
theorem circuit_multiplication_lowerBound_of_quotientIndependent
    [Field K]
    [AddCommGroup U]
    [Module K U]
    [Mul U]
    (constant : C → U)
    (problem : Problem U)
    (targets : Fin m → U)
    (independent : LinearIndependent K
      ((freeSubmodule K constant problem).mkQ ∘ targets))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m)
    (constructs : Multiple.Constructs (constant := constant)
      problem targets circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  exact Multiple.circuit_multiplication_lowerBound_of_linearIndependent
    (certificate constant problem) targets independent circuit constructs

/-- Canonical quotient-output rank lower-bounds total nonconstant gate cost. -/
theorem outputRank_le_gateCost
    [Field K]
    [AddCommGroup U]
    [Module K U]
    [Mul U]
    (constant : C → U)
    (problem : Problem U)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m)
    (constructs : Multiple.Constructs (constant := constant)
      problem targets circuit) :
    outputRank (K := K) constant problem targets ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := C)) :=
  (outputRank_le_multiplicationCost (K := K) constant problem targets circuit
    constructs).trans (Combined.circuit_multiplicationCost_le_gateCost circuit)

/-- Canonical quotient-output rank lower-bounds raw circuit size. -/
theorem outputRank_le_size
    [Field K]
    [AddCommGroup U]
    [Module K U]
    [Mul U]
    (constant : C → U)
    (problem : Problem U)
    (targets : Fin m → U)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount g m)
    (constructs : Multiple.Constructs (constant := constant)
      problem targets circuit) :
    outputRank (K := K) constant problem targets ≤ circuit.size :=
  (outputRank_le_gateCost (K := K) constant problem targets circuit
    constructs).trans
    (Combined.circuit_gateCost_le_size circuit)

end
end Quotient
end Linear
end Interaction
end Arithmetic
end Fusion
end Algebraic

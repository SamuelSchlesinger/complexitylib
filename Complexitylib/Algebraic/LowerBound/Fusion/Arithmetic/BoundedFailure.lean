/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic
public import Complexitylib.Algebraic.LowerBound.Fusion.Counting

/-!
# Bounded-failure arithmetic fusion

For multiplicative-complexity lower bounds, additions and constants are free.
Consequently an arithmetic fusion model only needs three local facts:

* addition preserves every witness;
* each named constant preserves every witness;
* a multiplication fails on at most a bounded number of witnesses.

`FailureRules` packages exactly this interface and compiles it to the generic
finite-witness counting framework.  Concrete applications can use degree
thresholds, derivative directions, rank increments, monomial cuts, or other
observations without rebuilding the cover-counting proof.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic

/-- Local arithmetic rules sufficient for a bounded-failure fusion argument. -/
structure FailureRules
    {K : Type u}
    {R : Type v}
    [Add R]
    [Mul R]
    {constant : K → R}
    {problem : Problem R}
    (model : Model
      (Algebraic.Arithmetic.multiplicationCost (K := K))
      (Algebraic.Arithmetic.interpretation constant) problem)
    [Fintype model.Witness] where
  /-- Maximum number of witnesses destroyed by one multiplication. -/
  capacity : Nat
  /-- Free additions must preserve every witness. -/
  add_preserved : ∀ (arguments : Fin 2 → R) (witness : model.Witness),
    (⟨.add, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K) R).PreservedBy model witness
  /-- Free constants must preserve every witness. -/
  constant_preserved : ∀ (scalar : K)
      (arguments : Fin (Algebraic.Arithmetic.arity (.constant scalar)) → R)
      (witness : model.Witness),
    (⟨.constant scalar, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K) R).PreservedBy model witness
  /-- The local combinatorial estimate charged to one multiplication. -/
  mul_failure_card_le : ∀ arguments : Fin 2 → R,
    ((⟨.mul, arguments⟩ :
      Atom (Algebraic.Arithmetic.signature K) R).failures model).card ≤ capacity

/-- Arithmetic local rules compile to a generic weighted failure bound. -/
noncomputable def FailureRules.failureBound
    {K : Type u}
    {R : Type v}
    [Add R]
    [Mul R]
    {constant : K → R}
    {problem : Problem R}
    {model : Model
      (Algebraic.Arithmetic.multiplicationCost (K := K))
      (Algebraic.Arithmetic.interpretation constant) problem}
    [Fintype model.Witness]
    (rules : FailureRules model) : FailureBound model where
  capacity := rules.capacity
  failure_card_le := by
    classical
    intro atom
    cases atom with
    | mk op arguments =>
        cases op with
        | add =>
            change Fin 2 → R at arguments
            have noFailures :
                ((⟨.add, arguments⟩ :
                  Atom (Algebraic.Arithmetic.signature K) R).failures model) = ∅ := by
              ext witness
              simp [rules.add_preserved arguments witness]
            rw [noFailures]
            simp [Atom.cost]
        | mul =>
            change Fin 2 → R at arguments
            simpa [Atom.cost] using rules.mul_failure_card_le arguments
        | constant scalar =>
            have noFailures :
                ((⟨.constant scalar, arguments⟩ :
                  Atom (Algebraic.Arithmetic.signature K) R).failures model) = ∅ := by
              ext witness
              simp [rules.constant_preserved scalar arguments witness]
            rw [noFailures]
            simp [Atom.cost]

/-- A positive arithmetic failure capacity lower-bounds every fusion cover. -/
theorem FailureRules.cover_lowerBound
    {K : Type u}
    {R : Type v}
    [Add R]
    [Mul R]
    {constant : K → R}
    {problem : Problem R}
    {model : Model
      (Algebraic.Arithmetic.multiplicationCost (K := K))
      (Algebraic.Arithmetic.interpretation constant) problem}
    [Fintype model.Witness]
    (rules : FailureRules model)
    (positive : 0 < rules.capacity)
    (cover : Cover model) :
    Fintype.card model.Witness ⌈/⌉ rules.capacity ≤ cover.cost :=
  rules.failureBound.ceilDiv_witnessCard_le_coverCost positive cover

/-- The bounded-failure arithmetic argument transferred to a circuit. -/
theorem FailureRules.circuit_lowerBound
    {K : Type u}
    {R : Type v}
    [Add R]
    [Mul R]
    {constant : K → R}
    {problem : Problem R}
    {model : Model
      (Algebraic.Arithmetic.multiplicationCost (K := K))
      (Algebraic.Arithmetic.interpretation constant) problem}
    [Fintype model.Witness]
    (rules : FailureRules model)
    (positive : 0 < rules.capacity)
    (circuit : Circuit (Algebraic.Arithmetic.signature K)
      problem.inputCount 1)
    (constructs : problem.Constructs circuit
      (Algebraic.Arithmetic.interpretation constant)) :
    Fintype.card model.Witness ⌈/⌉ rules.capacity ≤
      circuit.cost (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
  rules.failureBound.ceilDiv_witnessCard_le_circuitCost
    positive circuit constructs

end Arithmetic
end Fusion
end Algebraic

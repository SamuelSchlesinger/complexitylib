/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity
public import Complexitylib.Algebraic.LowerBound.GateElimination.DeMorganXor

/-!
# Transporting the De Morgan parity lower bound

The literal De Morgan lower bound extends to every realized macro basis, both
for chosen implementation costs and for intrinsic minimum AND/OR costs.
-/

@[expose] public section

namespace Algebraic

/-- Every circuit over a basis realized by De Morgan circuits pays at least
`3 * (n - 1)` for parity, when each source gate is charged by the binary-gate
cost of its implementation. -/
theorem parity_lowerBound_of_deMorgan_realization
    {ρ : Signature}
    {interpretation : Interpretation ρ Bool}
    (realization : Realization ρ DeMorgan.signature interpretation
      DeMorgan.interpretation)
    (circuit : Circuit ρ n 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.parityTarget n)) :
    3 * (n - 1) ≤
      circuit.cost (realization.pullCost DeMorgan.binaryCost) := by
  exact realization.transport_lowerBound DeMorgan.binaryCost
    (GateElimination.Xor.parityTarget n)
    (fun targetCircuit targetComputes =>
      DeMorgan.xor_lowerBound targetCircuit targetComputes)
    circuit computes

/-- The intrinsic form of the transported parity bound. Each source operation
is charged by its minimum possible De Morgan AND/OR implementation cost, not
by an arbitrary initially selected gadget. -/
theorem parity_lowerBound_of_deMorgan_minimumCost
    {ρ : Signature}
    {interpretation : Interpretation ρ Bool}
    (realization : Realization ρ DeMorgan.signature interpretation
      DeMorgan.interpretation)
    (circuit : Circuit ρ n 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.parityTarget n)) :
    3 * (n - 1) ≤
      circuit.cost (realization.minimumCost DeMorgan.binaryCost) := by
  exact parity_lowerBound_of_deMorgan_realization
    (realization.minimize DeMorgan.binaryCost).toRealization circuit computes

/-- If every macro operation has intrinsic De Morgan AND/OR cost at most `K`,
then the ordinary source gate count satisfies the ceiling-divided parity lower
bound. -/
theorem parity_size_lowerBound_of_deMorgan_minimumCost
    {ρ : Signature}
    {interpretation : Interpretation ρ Bool}
    (realization : Realization ρ DeMorgan.signature interpretation
      DeMorgan.interpretation)
    (positive : 0 < K)
    (bounded : ∀ op,
      realization.minimumCost DeMorgan.binaryCost op ≤ K)
    (circuit : Circuit ρ n 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.parityTarget n)) :
    (3 * (n - 1)) ⌈/⌉ K ≤ circuit.size := by
  rw [ceilDiv_le_iff_le_mul positive]
  exact (parity_lowerBound_of_deMorgan_minimumCost realization circuit
    computes).trans (circuit.cost_le_mul_size _ bounded)

/-- Conventional unit-cost corollary: if every source operation has a chosen
De Morgan implementation of at most `K` gates, then parity requires at least
the ceiling of `3 * (n - 1) / K` source gates. -/
theorem parity_size_lowerBound_of_deMorgan_realization
    {ρ : Signature}
    {interpretation : Interpretation ρ Bool}
    (realization : Realization ρ DeMorgan.signature interpretation
      DeMorgan.interpretation)
    (positive : 0 < K)
    (bounded : ∀ op, (realization.operation op).size ≤ K)
    (circuit : Circuit ρ n 1)
    (computes : circuit.ComputesWith interpretation
      (GateElimination.Xor.parityTarget n)) :
    (3 * (n - 1)) ⌈/⌉ K ≤ circuit.size := by
  apply realization.transport_sizeLowerBound_ceilDiv
    (GateElimination.Xor.parityTarget n) positive _ bounded circuit computes
  intro targetCircuit targetComputes
  have cost_le_size := targetCircuit.cost_le_mul_size (K := 1)
    DeMorgan.binaryCost (by
      intro op
      cases op <;> decide)
  exact (DeMorgan.xor_lowerBound targetCircuit targetComputes).trans <|
    by simpa using cost_le_size

end Algebraic

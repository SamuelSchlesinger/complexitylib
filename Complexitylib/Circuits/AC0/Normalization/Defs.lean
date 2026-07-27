/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.NormalForm.Defs

/-!
# Normalizing unbounded AND/OR circuits to negation-normal formulas

Each gate first replaces its arbitrarily long input table by the finite set of
distinct signed source wires. This is semantically exact because AND and OR are
idempotent. It also closes an important quantitative loophole: the circuit
model counts gates rather than wire incidences, so duplicate inputs must not
inflate the normalized formula.
-/

@[expose] public section

namespace Complexity

/-- The distinct signed source wires read by a gate, after composing every
edge-negation flag with an optional outer negation. -/
def Gate.signedSupport {W : ℕ}
    (gate : Gate Basis.unboundedAndOr W) (outerNegated : Bool) :
    Finset (Fin W × Bool) :=
  Finset.univ.image fun input =>
    (gate.inputs input, outerNegated.xor (gate.negated input))

namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

/-- Unfold one circuit wire into a negation-normal unbounded formula.

The `negated` parameter requests either the wire value or its complement.
De Morgan duality pushes that request through every gate, so negation reaches
only input literals. Distinct signed gate inputs are used exactly once. -/
noncomputable def wireAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (negated : Bool) (wire : Fin (N + G)) : AC0Formula N :=
  if hinput : wire.val < N then
    .lit
      { var := ⟨wire.val, hinput⟩
        polarity := !negated }
  else
    have hgate : wire.val - N < G := by omega
    let gateIndex : Fin G := ⟨wire.val - N, hgate⟩
    let gate := circuit.gates gateIndex
    let support := gate.signedSupport negated
    let children := support.attach.toList.map
        fun source : {signed // signed ∈ support} =>
      have hprior : source.val.1.val < wire.val := by
        have hmember : source.val ∈ gate.signedSupport negated := by
          simpa only [support] using source.property
        obtain ⟨input, _, hsource⟩ := Finset.mem_image.mp hmember
        have hacyclic := circuit.acyclic gateIndex input
        have hvalue :=
          congrArg (fun signed : Fin (N + G) × Bool => signed.1.val)
            hsource
        simp only at hvalue
        calc
          source.val.1.val = (gate.inputs input).val := hvalue.symm
          _ < N + gateIndex.val := by
            simpa only [gate] using hacyclic
          _ = wire.val := by
            simp only [gateIndex]
            omega
      circuit.wireAC0Formula source.val.2 source.val.1
    AC0Formula.ofOp (gate.op.dualIf negated)
      (.ofList children)
termination_by wire.val
decreasing_by
  exact hprior

/-- Normalize one selected output gate to a negation-normal unbounded formula. -/
noncomputable def outputAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (output : Fin M) : AC0Formula N :=
  let gate := circuit.outputs output
  let support := gate.signedSupport false
  let children := support.attach.toList.map
    fun source : {signed // signed ∈ support} =>
      circuit.wireAC0Formula source.val.2 source.val.1
  AC0Formula.ofOp gate.op (.ofList children)

end Circuit
end Complexity

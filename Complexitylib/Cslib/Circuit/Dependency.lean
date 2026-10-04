/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Wire
public import Mathlib.Data.Fintype.Basic

/-!
# Circuit dependencies

The consumers of a wire are the gates that read it. Equality of two evaluations
propagates through the program outside a boundary when the gates crossing that
boundary have equal values.

Ported from `Cslib.Computability.Circuit.Dependency` at commit `2a4389b` of the author's CSLib
fork (branch `complexitylib-integration`); upstream CSLib does not have this module. It keeps its
`Cslib.Circuits` namespace as a candidate for upstreaming.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ} {U : Type*}

/-- A gate reads a wire as one of its arguments. -/
def Program.Reads (p : Program σ n g) (gate : Fin g) (wire : Wire n g) : Prop :=
  ∃ argument, (p.lines gate).wires argument = wire

instance Program.instDecidableReads (p : Program σ n g) (gate : Fin g) (wire : Wire n g) :
    Decidable (p.Reads gate wire) := by
  unfold Program.Reads
  infer_instance

/-- All gates that read a given wire. -/
def Program.consumers (p : Program σ n g) (wire : Wire n g) : Finset (Fin g) :=
  Finset.univ.filter (fun gate => p.Reads gate wire)

@[simp] theorem Program.mem_consumers (p : Program σ n g) (wire : Wire n g)
    (gate : Fin g) : gate ∈ p.consumers wire ↔ p.Reads gate wire := by
  simp [consumers]

/-- A gate can only read input wires and earlier gate wires. -/
theorem Program.Reads.lt {p : Program σ n g} {gate : Fin g} {wire : Wire n g}
    (h : p.Reads gate wire) : wire.index.val < n + gate.val := by
  obtain ⟨argument, rfl⟩ := h
  exact p.lines_wires_lt gate argument

/-- Equality propagates away from a boundary if every gate crossing it agrees. -/
theorem Program.trace_eq_of_boundary (p : Program σ n g) (I : Interpretation σ U)
    (x y : Fin n → U) (boundary : Set (Wire n g)) (limit : ℕ)
    (hinput : ∀ i, Wire.input i ∉ boundary → x i = y i)
    (hgate : ∀ j : Fin g, n + j.val < limit → Wire.gate j ∉ boundary →
      (∃ a, (p.lines j).wires a ∈ boundary) → p.eval I x j = p.eval I y j)
    (wire : Wire n g) (hwire : wire ∉ boundary) (hlimit : wire.index.val < limit) :
    p.trace I x wire = p.trace I y wire := by
  classical
  induction hindex : wire.index.val using Nat.strong_induction_on generalizing wire with
  | _ k ih =>
    subst hindex
    cases wire with
    | input i => simpa using hinput i hwire
    | gate j =>
      simp only [Program.trace_gateWire, Program.gateFunction_apply]
      by_cases hcross : ∃ a, (p.lines j).wires a ∈ boundary
      · exact hgate j hlimit hwire hcross
      · rw [← p.lines_eval I x j, ← p.lines_eval I y j]
        unfold Line.eval
        congr 1
        funext a
        exact ih _ (p.lines_wires_lt j a) _ (fun ha => hcross ⟨a, ha⟩)
          (Nat.lt_trans (p.lines_wires_lt j a) hlimit) rfl

end Cslib.Circuits

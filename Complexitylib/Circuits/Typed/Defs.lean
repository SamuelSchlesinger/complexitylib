/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Basis.Defs

/-! # Typed Boolean circuits

This file defines the library's typed Boolean circuits. A `Circuit B N M G` is
a circuit over the basis `B` with `N` primary inputs, `M` output gates, and `G`
internal gates; its wiring makes it acyclic by construction. The file also
defines evaluation, depth, the size measure `G + M`, and complete bases.

## Main definitions

* `Gate` — a gate over a basis, with a free negation flag on each input
* `Circuit` — an acyclic Boolean circuit (well-formedness by construction)
* `Circuit.wireValue`, `Circuit.eval` — evaluation of wires and outputs
* `Circuit.wireDepth` — depth of a wire in the circuit DAG
* `Circuit.outputDepth` — depth of a single output gate
* `Circuit.depth` — depth of a (possibly multi-output) circuit
* `Circuit.size` — the number of internal and output gates
* `CompleteBasis` — typeclass for functionally complete bases

## Main results

* `CompleteBasis.of_simulation` — completeness transfers to any basis that can
  simulate the circuits of a complete basis
-/


@[expose] public section

namespace Complexity

/--
A gate in a circuit over basis `B` with `W` wires available as inputs.
The gate's fan-in must satisfy the arity constraint of its operation, and each
input is wired to one of the `W` available wires.
-/
structure Gate (B : Basis) (W : Nat) where
  /-- The basis operation this gate computes. -/
  op : B.Op
  /-- The number of inputs this gate reads. -/
  fanIn : Nat
  /-- Proof that `fanIn` satisfies the arity constraint of `op`. -/
  arityOk : (B.arity op).satisfiedBy fanIn
  /-- The wire each of the gate's `fanIn` inputs is connected to. -/
  inputs : Fin fanIn → Fin W
  /-- Per-input negation flag. Negations are free under this library's size
      convention. -/
  negated : Fin fanIn → Bool

/-- Evaluate a gate given a wire-value assignment. -/
def Gate.eval (g : Gate B W) (wireVal : BitString W) : Bool :=
  B.eval g.op g.fanIn g.arityOk (fun i => (g.negated i).xor (wireVal (g.inputs i)))

/--
A Boolean circuit over basis `B` with `N` inputs, `M` outputs, and `G`
internal gates.

All gates reference wires from `Fin (N + G)`. The `acyclic` field ensures
that internal gate `i` only reads wires `0, …, N + i − 1`, preventing cycles.
-/
structure Circuit (B : Basis) (N M G : Nat) [NeZero N] [NeZero M] where
  /-- The internal gates; gate `i` drives wire `N + i`. -/
  gates : Fin G → Gate B (N + G)
  /-- The output gates; output bit `j` is the value of gate `outputs j`. -/
  outputs : Fin M → Gate B (N + G)
  /-- Acyclicity: internal gate `i` only reads wires `0, …, N + i − 1`. -/
  acyclic : ∀ (i : Fin G) (k : Fin (gates i).fanIn),
    ((gates i).inputs k).val < N + i.val

namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Value of wire `w` when the circuit is fed `input`.

The first `N` wires carry the primary inputs. Wire `N + i` carries the
output of internal gate `i`. -/
def wireValue (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    B.eval gate.op gate.fanIn gate.arityOk
      fun k => (gate.negated k).xor (c.wireValue input (gate.inputs k))
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- On primary input wires (index < `N`), `wireValue` is the corresponding input bit. -/
theorem wireValue_of_lt (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireValue input w = input ⟨w.val, h⟩ := by
  unfold wireValue
  simp [h]

/-- On internal gate wires (index ≥ `N`), `wireValue` is the evaluation of gate
`w − N` on the values of its input wires. -/
theorem wireValue_of_not_lt (c : Circuit B N M G) (input : BitString N)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireValue input w =
      (c.gates ⟨w.val - N, by omega⟩).eval (c.wireValue input) := by
  unfold wireValue
  simp only [h, dite_false]
  rfl

/-- Depth of wire `w` in the circuit DAG.

Primary inputs have depth 0. Wire `N + i` (internal gate `i`) has depth
`1 + max over input wires`. -/
def wireDepth (c : Circuit B N M G) (w : Fin (N + G)) : Nat :=
  if h : w.val < N then
    0
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    1 + Fin.foldl gate.fanIn (fun acc k => max acc (c.wireDepth (gate.inputs k))) 0
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Primary input wires (index < N) have depth 0. -/
@[simp] theorem wireDepth_of_lt (c : Circuit B N M G)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireDepth w = 0 := by
  unfold wireDepth; simp [h]

/-- Internal gate wires (index ≥ N) have depth 1 + max over their input wires.
Unfolds one step of `wireDepth` for the gate case. -/
theorem wireDepth_of_not_lt (c : Circuit B N M G)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireDepth w =
      1 + Fin.foldl (c.gates ⟨w.val - N, by omega⟩).fanIn
        (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, by omega⟩).inputs k))) 0 := by
  conv_lhs => unfold wireDepth
  simp only [h, dite_false]

/-- Depth contributed by a single output gate: one layer for the gate itself
plus the maximum `wireDepth` of its inputs. Always ≥ 1. -/
def outputDepth (c : Circuit B N M G) (j : Fin M) : Nat :=
  let outGate := c.outputs j
  1 + Fin.foldl outGate.fanIn (fun acc k => max acc (c.wireDepth (outGate.inputs k))) 0

/-- Depth of a circuit: the maximum `outputDepth` over all output gates. -/
def depth (c : Circuit B N M G) : Nat :=
  Fin.foldl M (fun acc j => max acc (c.outputDepth j)) 0

/-- Evaluate a circuit: map an `N`-bit input to an `M`-bit output. -/
def eval (c : Circuit B N M G) (input : BitString N) : BitString M :=
  fun j => (c.outputs j).eval (c.wireValue input)

/-- The library's circuit size: internal gates plus output gates.

Primary input vertices are not counted, and the negation flags on gate inputs
have zero cost. Some texts instead count input vertices and explicit NOT gates;
those conventions agree only up to additive/linear overhead, not on exact size
bounds. -/
-- The circuit argument is unused by design: `size` is determined by the
-- indices, and the argument exists purely to enable `c.size` dot notation.
def size (_ : Circuit B N M G) : Nat := G + M

end Circuit

/-- A basis is complete if every Boolean function can be computed by some circuit over it. -/
class CompleteBasis (B : Basis) : Prop where
  /-- Every function `BitString N → BitString M` is the evaluation of some circuit over `B`. -/
  complete : ∀ {N M} [NeZero N] [NeZero M] (f : BitString N → BitString M),
    ∃ G, ∃ c : Circuit B N M G, c.eval = f

/-- If every circuit over `B₁` can be simulated by a circuit over `B₂`
    (possibly with a different number of internal gates), then completeness
    of `B₁` implies completeness of `B₂`.

    This is the generic tool for proving new bases complete: show you can
    compile each gate of a known-complete basis into a subcircuit of the
    new basis. -/
theorem CompleteBasis.of_simulation (B₁ B₂ : Basis) [CompleteBasis B₁]
    (sim : ∀ {N M G} [NeZero N] [NeZero M] (c : Circuit B₁ N M G),
      ∃ G', ∃ c' : Circuit B₂ N M G', c'.eval = c.eval)
    : CompleteBasis B₂ where
  complete f := by
    obtain ⟨G, c, hc⟩ := CompleteBasis.complete (B := B₁) f
    obtain ⟨G', c', hc'⟩ := sim c
    exact ⟨G', c', hc'.trans hc⟩

end Complexity

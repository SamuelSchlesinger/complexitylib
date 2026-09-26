/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Circuit.Basic
public import Complexitylib.Circuits.Basis.Defs
public import Complexitylib.Circuits.Typed.Defs
public import Complexitylib.Cslib.Circuit.Gated
public import Complexitylib.Cslib.Circuit.Program

/-!
# Typed circuits as CSLib straight-line programs

CSLib's circuits (`Cslib.Circuits.Circuit`) are straight-line programs over a
signature, and `Basis.signature` (in `Complexitylib.Circuits.Basis.Defs`) makes
each Complexitylib basis such a signature: an operation symbol of `B.signature`
is a whole gate kind of `B`, so `Gate.kind` turns each gate into one.

`Circuit.toStraightLine` translates a typed circuit `Circuit B N M G` into a
CSLib circuit over `B.signature`. The program lists the `G` internal gates and
then the `M` output gates, and the CSLib outputs are the last `M` gates, so the
translation has exactly `G + M` gates, the typed circuit's `size`.

## Main definitions

- `Complexity.Gate.kind` — the gate kind of a gate, an operation symbol of
  `B.signature`
- `Complexity.Circuit.toStraightLine` — a typed circuit as a CSLib circuit
-/


@[expose] public section

namespace Complexity

open Cslib.Circuits

/-- The gate kind of a gate: its operation, fan-in, and negation flags. -/
def Gate.kind {B : Basis} {W : ℕ} (gate : Gate B W) : B.GateKind :=
  ⟨gate.op, gate.fanIn, gate.arityOk, gate.negated⟩

namespace StraightLine

variable {N : ℕ}

/-- The CSLib wire with index `w` in the layout of typed circuits, where the
first `N` wires are the inputs and wire `N + j` is gate `j`. -/
def wireOfIndex {j : ℕ} (w : ℕ) (hw : w < N + j) : Wire N j :=
  if h : w < N then .input ⟨w, h⟩ else .gate ⟨w - N, by omega⟩

end StraightLine

namespace Circuit

variable {B : Basis} {N M G : ℕ} [NeZero N] [NeZero M]

/-- Line `j` of the straight-line form of a typed circuit: internal gate `j`
for `j < G`, and output gate `j - G` otherwise. -/
def straightLineAt (c : Circuit B N M G) (j : Fin (G + M)) : Line B.signature N j :=
  if h : j.val < G then
    ⟨(c.gates ⟨j, h⟩).kind, fun k => StraightLine.wireOfIndex ((c.gates ⟨j, h⟩).inputs k).val
      (by simpa using c.acyclic ⟨j, h⟩ k)⟩
  else
    ⟨(c.outputs ⟨j - G, by omega⟩).kind, fun k =>
      StraightLine.wireOfIndex ((c.outputs ⟨j - G, by omega⟩).inputs k).val
        (by have := ((c.outputs ⟨j - G, by omega⟩).inputs k).isLt; omega)⟩

/-- The typed circuit `c` as a CSLib circuit over `B.signature`: its internal
gates followed by its output gates, with the output gates as outputs. -/
def toStraightLine (c : Circuit B N M G) : Cslib.Circuits.Circuit B.signature N M where
  size := G + M
  program := Program.ofLines (G + M) c.straightLineAt
  outputs o := .gate (Fin.natAdd G o)

end Circuit

end Complexity

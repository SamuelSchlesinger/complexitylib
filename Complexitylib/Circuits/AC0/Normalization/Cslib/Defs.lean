/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Normalization.Defs
public import Complexitylib.Cslib.Circuit.Program

/-!
# Negation-normal formulas for CSLib unbounded AND/OR circuits

Use the existing wire normalization through a program-only typed adapter. The adapter's
unused output does not enter the selected formula, so it adds no depth or formula-size cost.
-/

@[expose] public section

namespace Complexity.CslibAC0

open Cslib.Circuits

variable {n g : ℕ}

/-- A CSLib line read through the typed circuit wire numbering. -/
def lineGate (l : Line Basis.unboundedAndOr.signature n g) :
    Gate Basis.unboundedAndOr (n + g) where
  op := l.op.op
  fanIn := l.op.fanIn
  arityOk := l.op.arityOk
  inputs a := (l.wires a).index
  negated := l.op.negated

variable [NeZero n]

/-- Use the existing typed wire normalizer on a CSLib program. The auxiliary output is unused. -/
def asTyped (p : Program Basis.unboundedAndOr.signature n g) :
    Complexity.Circuit Basis.unboundedAndOr n 1 g where
  gates j := lineGate (p.lines j)
  outputs _ :=
    { op := .or
      fanIn := 0
      arityOk := trivial
      inputs := Fin.elim0
      negated := Fin.elim0 }
  acyclic j k := Program.lines_wires_lt p j k

/-- Unfold a CSLib output to a negation-normal formula, removing repeated signed wires. -/
noncomputable def outputFormula (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1) :
    AC0Formula n :=
  (asTyped c.program).wireAC0Formula false (c.outputs 0).index

end Complexity.CslibAC0

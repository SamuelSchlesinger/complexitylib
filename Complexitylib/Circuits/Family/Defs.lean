/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BitString
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Boolean circuit families — definitions

This module lifts the finite `Circuit` model to one circuit at every positive
input length. Because `Circuit` deliberately requires a nonzero input arity,
the answer on the unique empty input is stored separately as `emptyOutput`.

The first component of `circuits n` is the number of internal gates. Family
`size` counts internal and output gates, but not primary-input vertices or the
free per-edge negation flags.
-/

@[expose] public section

namespace Complexity

namespace Circuit

variable {B : Basis} {N G : ℕ} [NeZero N]

/-- A single-output circuit computes `f` when its output agrees with `f` on
    every input. -/
def Computes (c : Circuit B N 1 G) (f : BitString N → Bool) : Prop :=
  (fun x => (c.eval x) 0) = f

/-- A circuit computes the length-`N` member of a Boolean function family. -/
def ComputesOnLength (c : Circuit B N 1 G) (f : BoolFunFamily) : Prop :=
  c.Computes (f N)

end Circuit

/-- A nonuniform family of single-output circuits over `B`.

At each positive length `n`, the dependent pair contains an internal-gate
count `G` and a circuit `Circuit B n 1 G`. The unique length-zero input is
handled by `emptyOutput`, since the base circuit model deliberately requires
at least one input wire. -/
structure CircuitFamily (B : Basis) where
  /-- The family's answer on the unique length-zero input, stored directly
      because `Circuit` requires a positive input arity. -/
  emptyOutput : Bool
  /-- For each positive length `n`, an internal-gate count `G` paired with a
      single-output circuit on `n` inputs and `G` internal gates. -/
  circuits : ∀ (n : ℕ) [NeZero n], Σ G, Circuit B n 1 G

namespace CircuitFamily

variable {B : Basis}

/-- Number of internal gates in the positive-length circuit. -/
def internalGateCount (F : CircuitFamily B) (n : ℕ) [NeZero n] : ℕ :=
  (F.circuits n).1

/-- The circuit selected by the family at positive input length `n`. -/
def circuit (F : CircuitFamily B) (n : ℕ) [NeZero n] :
    Circuit B n 1 (F.internalGateCount n) :=
  (F.circuits n).2

/-- The Boolean function family computed by `F`, including its explicit
    length-zero answer. -/
def function (F : CircuitFamily B) : BoolFunFamily
  | 0, _ => F.emptyOutput
  | n + 1, x => (F.circuit (n + 1)).eval x 0

/-- Evaluate a circuit family on the list representation used by languages. -/
def evalList (F : CircuitFamily B) (x : List Bool) : Bool :=
  F.function x.length x.get

/-- Total circuit size at each length. The separate empty-input answer is a
    finite exception and is assigned size zero. -/
def size (F : CircuitFamily B) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (F.circuit (n + 1)).size

/-- Circuit depth at each length, with depth zero on the empty input. -/
def depth (F : CircuitFamily B) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (F.circuit (n + 1)).depth

/-- A pointwise size bound for a circuit family. -/
def SizeBoundedBy (F : CircuitFamily B) (s : ℕ → ℕ) : Prop :=
  ∀ n, F.size n ≤ s n

/-- A pointwise depth bound for a circuit family. -/
def DepthBoundedBy (F : CircuitFamily B) (d : ℕ → ℕ) : Prop :=
  ∀ n, F.depth n ≤ d n

/-- A family has polynomial size when one natural-coefficient polynomial
    bounds its size at every input length. -/
def PolynomialSize (F : CircuitFamily B) : Prop :=
  ∃ p : Polynomial ℕ, F.SizeBoundedBy fun n => p.eval n

/-- `F` computes the Boolean function family `f` at every length. -/
def Computes (F : CircuitFamily B) (f : BoolFunFamily) : Prop :=
  F.function = f

end CircuitFamily

end Complexity

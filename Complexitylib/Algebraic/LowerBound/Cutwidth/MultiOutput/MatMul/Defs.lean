/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Program
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Matrix multiplication in coordinates: definition

The product `C = A B` of two `n × n` matrices, as a map with `2 n²` inputs and `n²` outputs.
The input coordinates are `Fin (n * n + n * n)`: the entry `A i j` of the first factor sits at
`matMulLeft n i j`, among the first `n * n` coordinates, and the entry `B j k` of the second
factor at `matMulRight n j k`, among the last `n * n`. The output `C i k` sits at
`matMulOutput n i k`. Pairs of indices are numbered row by row through `finProdFinEquiv`.

* `matMul n z` is the product read from the input `z`:
  output `C i k` is `∑ j, A i j * B j k`.
* `matMulInput A B` is the input holding the two matrices `A` and `B`.
* `matMulTermA n s`, `matMulTermB n s` and `matMulTermC out`: the wires of a circuit with `s`
  gates and output wires `out` carrying the entries `A i j`, `B j k` and `C i k`, indexed by
  pairs of indices. These are the *terminals*.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

/-- The input coordinate of the entry `A i j` of the first factor. -/
def matMulLeft (n : Nat) (i j : Fin n) : Fin (n * n + n * n) :=
  Fin.castAdd (n * n) (finProdFinEquiv (i, j))

/-- The input coordinate of the entry `B j k` of the second factor. -/
def matMulRight (n : Nat) (j k : Fin n) : Fin (n * n + n * n) :=
  Fin.natAdd (n * n) (finProdFinEquiv (j, k))

/-- The output coordinate of the entry `C i k` of the product. -/
def matMulOutput (n : Nat) (i k : Fin n) : Fin (n * n) :=
  finProdFinEquiv (i, k)

/-- **Matrix multiplication in coordinates.** The output `C i k` is `∑ j, A i j * B j k`, where
`A i j = z (matMulLeft n i j)` and `B j k = z (matMulRight n j k)`. -/
def matMul {R : Type*} [Semiring R] (n : Nat) (z : Fin (n * n + n * n) → R) :
    Fin (n * n) → R :=
  fun o => ∑ j, z (matMulLeft n (finProdFinEquiv.symm o).1 j) *
    z (matMulRight n j (finProdFinEquiv.symm o).2)

/-- The input holding the matrices `A` and `B`. -/
def matMulInput {R : Type*} {n : Nat} (A B : Matrix (Fin n) (Fin n) R) :
    Fin (n * n + n * n) → R :=
  Fin.append (fun p => A (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
    (fun p => B (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)

/-- The wire of the input `A i j`. -/
def matMulTermA (n s : Nat) (q : Fin n × Fin n) : Wire (n * n + n * n) s :=
  Wire.input (matMulLeft n q.1 q.2)

/-- The wire of the input `B j k`. -/
def matMulTermB (n s : Nat) (q : Fin n × Fin n) : Wire (n * n + n * n) s :=
  Wire.input (matMulRight n q.1 q.2)

/-- The wire carrying the output `C i k`, among the output wires `out`. -/
def matMulTermC {n s : Nat} (out : Fin (n * n) → Wire (n * n + n * n) s) (q : Fin n × Fin n) :
    Wire (n * n + n * n) s :=
  out (matMulOutput n q.1 q.2)

end Algebraic.Cutwidth.MultiOutput

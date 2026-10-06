/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs

/-!
# The terminal graph of matrix multiplication: definitions

The `3 n²` terminals of `n × n` matrix multiplication `C = A B`, the inputs `A i j` and `B j k`
and the outputs `C i k`, are the edges of the complete tripartite graph on three copies `I`,
`J`, `K` of `Fin n`: `A i j` joins `i ∈ I` to `j ∈ J`, `B j k` joins `j ∈ J` to `k ∈ K`, and
`C i k` joins `i ∈ I` to `k ∈ K`. Every vertex has degree `2 n`.

A split of the wires of a circuit places some terminals on its side `S`. We record the placed
terminals of each kind as a set of index pairs: `a` holds the pairs `(i, j)` with `A i j` placed,
`b` the pairs `(j, k)` with `B j k` placed, and `c` the pairs `(i, k)` with `C i k` placed.

* `rowSet a i` and `colSet a j`: the second coordinates paired with `i`, and the first coordinates
  paired with `j`.
* `degI a c i`, `degJ a b j`, `degK b c k`: the number of placed terminals at a vertex.
* `minority n d = min d (2 n - d)`: the smaller of the numbers of terminals at a vertex of
  degree `2 n` on the two sides, when `d` of them are placed.
* `chargeI a c`, `chargeJ a b`, `chargeK b c`: the sums of `minority` over the vertices of `I`,
  `J` and `K`. For matrix multiplication they are lower bounds for ranks of three linear maps
  read off the split: fixing `B` (`chargeI`), fixing `A` (`chargeK`), and the cross block of the
  Hessian of `∑ Λ i k C i k` (`chargeJ`).
* `heavyI a c`, `heavyJ a b`, `heavyK b c`: the *heavy* vertices, with at least `n` placed
  terminals; `heavyCount a b c` counts them.
* `mixedPairs X Y`: the pairs `(x, y)` with exactly one of `x ∈ X` and `y ∈ Y`.
* `lightHeavy a b c`: the number of terminals with exactly one heavy endpoint.
* `place t S`: the index pairs whose terminal wire `t p` lies in a set of wires `S`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Tripartite

variable {n : Nat}

/-- Row `i` of a set of index pairs: the second coordinates paired with `i`. -/
def rowSet (a : Finset (Fin n × Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i, j) ∈ a

/-- Column `j` of a set of index pairs: the first coordinates paired with `j`. -/
def colSet (a : Finset (Fin n × Fin n)) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i, j) ∈ a

/-- The placed terminals at the vertex `i ∈ I`: the entries `A i j` and `C i k`. -/
def degI (a c : Finset (Fin n × Fin n)) (i : Fin n) : Nat :=
  (rowSet a i).card + (rowSet c i).card

/-- The placed terminals at the vertex `j ∈ J`: the entries `A i j` and `B j k`. -/
def degJ (a b : Finset (Fin n × Fin n)) (j : Fin n) : Nat :=
  (colSet a j).card + (rowSet b j).card

/-- The placed terminals at the vertex `k ∈ K`: the entries `B j k` and `C i k`. -/
def degK (b c : Finset (Fin n × Fin n)) (k : Fin n) : Nat :=
  (colSet b k).card + (colSet c k).card

/-- The smaller side at a vertex of degree `2 n` with `d` placed terminals. -/
def minority (n d : Nat) : Nat :=
  min d (2 * n - d)

/-- The charge of the vertices of `I`. -/
def chargeI (a c : Finset (Fin n × Fin n)) : Nat :=
  ∑ i, minority n (degI a c i)

/-- The charge of the vertices of `J`. -/
def chargeJ (a b : Finset (Fin n × Fin n)) : Nat :=
  ∑ j, minority n (degJ a b j)

/-- The charge of the vertices of `K`. -/
def chargeK (b c : Finset (Fin n × Fin n)) : Nat :=
  ∑ k, minority n (degK b c k)

/-- The heavy vertices of `I`: at least `n` placed terminals. -/
def heavyI (a c : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => n ≤ degI a c i

/-- The heavy vertices of `J`. -/
def heavyJ (a b : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => n ≤ degJ a b j

/-- The heavy vertices of `K`. -/
def heavyK (b c : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun k => n ≤ degK b c k

/-- The number of heavy vertices. -/
def heavyCount (a b c : Finset (Fin n × Fin n)) : Nat :=
  (heavyI a c).card + (heavyJ a b).card + (heavyK b c).card

/-- The pairs `(x, y)` with exactly one of `x ∈ X` and `y ∈ Y`. -/
def mixedPairs (X Y : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => ¬(p.1 ∈ X ↔ p.2 ∈ Y)

/-- The number of terminals with exactly one heavy endpoint. -/
def lightHeavy (a b c : Finset (Fin n × Fin n)) : Nat :=
  (mixedPairs (heavyI a c) (heavyJ a b)).card + (mixedPairs (heavyJ a b) (heavyK b c)).card +
    (mixedPairs (heavyI a c) (heavyK b c)).card

/-- The index pairs whose terminal wire lies in `S`. -/
def place {N s : Nat} (t : Fin n × Fin n → Wire N s) (S : Finset (Wire N s)) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => t p ∈ S

end Algebraic.Cutwidth.MultiOutput.Tripartite

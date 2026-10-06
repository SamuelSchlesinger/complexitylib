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
* `excessI a c i`, `deficitI a c i`: the excess `deg - n` and deficit `n - deg` of a vertex of
  `I` relative to the threshold `n`.
* `colSetIn a R j` and `complColSetIn a R j`: the rows `i ∈ R` with `A i j` placed, resp.
  unplaced.
* `probeIJ a b c I₀` and `twoSubsetProbeIJ a b c I₀ I₁`: exploratory sums mixing the `I` and `J`
  charges along subsets of `I`. They are combinatorial quantities only; no rank-cut theorem
  relates them to the signals crossing a split.
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

/-- The excess `degI a c i - n` of `i ∈ I` over the threshold `n` (zero unless `i` is heavy). -/
def excessI (a c : Finset (Fin n × Fin n)) (i : Fin n) : Nat :=
  degI a c i - n

/-- The deficit `n - degI a c i` of `i ∈ I` below the threshold `n` (zero if `i` is heavy). -/
def deficitI (a c : Finset (Fin n × Fin n)) (i : Fin n) : Nat :=
  n - degI a c i

/-- The first coordinates in `R` paired with `j` in `a`: the placed terminals `A i j` with
`i ∈ R`. -/
def colSetIn (a : Finset (Fin n × Fin n)) (R : Finset (Fin n)) (j : Fin n) : Finset (Fin n) :=
  (colSet a j).filter (· ∈ R)

/-- The first coordinates in `R` not paired with `j` in `a`: the unplaced terminals `A i j` with
`i ∈ R`. -/
def complColSetIn (a : Finset (Fin n × Fin n)) (R : Finset (Fin n)) (j : Fin n) :
    Finset (Fin n) :=
  R.filter (· ∉ colSet a j)

/-- An exploratory probe mixing the `I` and `J` charges along a subset `I₀` of `I`: the
`I`-charge `minority n (degI a c i)` of the rows `i ∈ I₀`, plus, at each `j ∈ J`, the two summands
of `minority n (degJ a b j) = min x (n - y) + min (n - x) y` (`minority_add_eq`, with
`x = (colSet a j).card`, `y = (rowSet b j).card`) with the `A`-terminals restricted to the rows of
`I₀ᶜ`. It interpolates between `chargeJ` (`I₀ = ∅`) and `chargeI` (`I₀ = univ`).

This is a combinatorial quantity only: no theorem bounds the number of signals crossing a split
below by it. -/
def probeIJ (a b c : Finset (Fin n × Fin n)) (I₀ : Finset (Fin n)) : Nat :=
  ∑ i ∈ I₀, minority n (degI a c i) +
    ∑ j, (min (colSetIn a I₀ᶜ j).card (n - (rowSet b j).card) +
      min (complColSetIn a I₀ᶜ j).card (rowSet b j).card)

/-- A two-subset variant of `probeIJ`. At `i ∈ I`, `minority n (degI a c i)` is the sum of
`min r (n - s)` and `min (n - r) s` (`minority_add_eq`, with `r = (rowSet a i).card`,
`s = (rowSet c i).card`); here the first summand is counted over `I₀` and the second over `I₁`.
At each `j ∈ J`, the two summands of `minority n (degJ a b j)` are counted with the
`A`-terminals restricted to the rows of `I₀ᶜ` and of `I₁ᶜ` respectively. As for `probeIJ`, the
arguments are the rows charged on the `I` side, and
`twoSubsetProbeIJ a b c I₀ I₀ = probeIJ a b c I₀`.

This is a combinatorial quantity only: no theorem bounds the number of signals crossing a split
below by it. -/
def twoSubsetProbeIJ (a b c : Finset (Fin n × Fin n)) (I₀ I₁ : Finset (Fin n)) : Nat :=
  ∑ i ∈ I₀, min (rowSet a i).card (n - (rowSet c i).card) +
    ∑ i ∈ I₁, min (n - (rowSet a i).card) (rowSet c i).card +
    ∑ j, (min (colSetIn a I₀ᶜ j).card (n - (rowSet b j).card) +
      min (complColSetIn a I₁ᶜ j).card (rowSet b j).card)

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

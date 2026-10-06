/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexitylib.Circuits.KCNF.Internal.Isolation
import Complexitylib.Circuits.KCNF.Internal.SubcubeFree

/-!
# k-CNFs without large subcubes have few solutions

A *move* of a solution `x` of a clause set `ψ` is a nonempty set `T` of variables with
`x ⊕ e_T` again a solution; two moves are *separated* when no clause meets both. Separated moves
combine freely (Lemma 3), so in a clause set whose co-occurrence graph has maximum degree `Δ` and
whose solutions contain no subcube of dimension `D`, every solution has at most `(D - 1)(Δ + 1)`
non-isolated directions (Lemma 4). The satisfiability coding lemma
(`Complexitylib.Circuits.KCNF.Coding`) then bounds the number of solutions. After sparsification
(`Complexitylib.Circuits.KCNF.Sparsification`) every `k`-CNF is a union of at most `2 ^ (ε N)`
such pieces, which gives Theorem A: a `k`-CNF whose solutions contain no subcube of dimension `D`
has at most `2 ^ ((1 - 1/k + ε) N + C D)` solutions.

The exponent `1 - 1/k` cannot be improved, already for `D = 1`: the `k`-CNF requiring even
parity on each of `N/k` disjoint blocks of `k` variables has `2 ^ ((1 - 1/k) N)` solutions, no two
of which are neighbours (this example is not formalized here).

## Main results

* `flipOn_mem_solutions_of_closed` (Lemma 3 (a)): the part of a move that no clause connects to
  the rest of the move is a move.
* `flipOn_biUnion_mem_solutions_of_separated` (Lemma 3 (b)): every union of pairwise separated
  moves is a move.
* `card_compl_isolatedDirections_le` (Lemma 4): local far-isolation, `d = 1`.
* `card_neighbors_le_occurrences_mul`: a variable occurring in `c` clauses of width `k` has at
  most `c (k - 1)` neighbours.
* `card_solutions_le_of_neighbors` (Theorem A, bounded degree): a clause set of width `k ≥ 1`
  and co-occurrence degree `Δ` whose solutions contain no subcube of dimension `D` has at most
  `2 ^ ((1 - 1/k) N + (D - 1)(Δ + 1)/k)` solutions.
* `card_solutions_le_of_not_containsSubcube`, `CNF.card_accepting_le_of_not_containsSubcube`
  (Theorem A): for every `k ≥ 1` and `ε > 0` there is `C` such that every `k`-CNF whose solutions
  contain no subcube of dimension `D` has at most `2 ^ ((1 - 1/k + ε) N + C D)` solutions.
-/

@[expose] public section

namespace Complexity.ClauseSet

open Finset

variable {N : ℕ}

/-- **Lemma 3 (a).** If `x` and `x ⊕ e_T` are solutions, `T' ⊆ T`, and no clause mentions both a
variable of `T'` and a variable of `T \ T'`, then `x ⊕ e_{T'}` is a solution. In particular
every connected component of a move in the co-occurrence graph is a move. -/
theorem flipOn_mem_solutions_of_closed {ψ : ClauseSet N} {x : BitString N}
    {T T' : Finset (Fin N)} (hx : x ∈ ψ.solutions) (hT : x.flipOn T ∈ ψ.solutions)
    (hsub : T' ⊆ T)
    (hclosed : ∀ C ∈ ψ, (∃ l ∈ C, l.var ∈ T') → ¬ ∃ l ∈ C, l.var ∈ T \ T') :
    x.flipOn T' ∈ ψ.solutions :=
  Isolation.flipOn_mem_of_closed hx hT hsub hclosed

/-- **Lemma 3 (b).** Let `x` be a solution and `T j`, for `j ∈ s`, moves of `x` that are pairwise
separated: no clause mentions variables of two of them. Then for every `J ⊆ s`,
`x ⊕ e_{⋃_{j ∈ J} T j}` is a solution. -/
theorem flipOn_biUnion_mem_solutions_of_separated {ι : Type*} {ψ : ClauseSet N}
    {x : BitString N} {s : Finset ι} {T : ι → Finset (Fin N)} (hx : x ∈ ψ.solutions)
    (hmove : ∀ j ∈ s, x.flipOn (T j) ∈ ψ.solutions)
    (hsep : ∀ C ∈ ψ, ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' →
      (∃ l ∈ C, l.var ∈ T j) → ¬ ∃ l ∈ C, l.var ∈ T j')
    {J : Finset ι} (hJ : J ⊆ s) : x.flipOn (J.biUnion T) ∈ ψ.solutions :=
  Isolation.flipOn_biUnion_mem_of_separated hx hmove hsep hJ

/-- **Lemma 4 (local far-isolation, `d = 1`).** If every variable has at most `Δ` neighbours in
the co-occurrence graph of `ψ` and the solutions of `ψ` contain no subcube of dimension `D`,
then every solution `x` has at most `(D - 1)(Δ + 1)` directions `i` with `x ⊕ e_i` a solution. -/
theorem card_compl_isolatedDirections_le {ψ : ClauseSet N} {Δ D : ℕ}
    (hdeg : ∀ u, (ψ.neighbors u).card ≤ Δ)
    (hfree : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D) {x : BitString N}
    (hx : x ∈ ψ.solutions) :
    (univ \ isolatedDirections ψ.solutions x).card ≤ (D - 1) * (Δ + 1) :=
  Isolation.card_compl_isolatedDirections_le hdeg hfree hx

/-- In a clause set whose clauses have at most `k` literals, a variable mentioned by `c` clauses
has at most `c (k - 1)` neighbours in the co-occurrence graph. -/
theorem card_neighbors_le_occurrences_mul {ψ : ClauseSet N} {k : ℕ}
    (hk : ∀ C ∈ ψ, C.card ≤ k) (u : Fin N) :
    (ψ.neighbors u).card ≤ ψ.occurrences u * (k - 1) :=
  Isolation.card_neighbors_le hk u

/-- **Theorem A for bounded co-occurrence degree.** Let every clause of `ψ` have at most `k ≥ 1`
literals, let every variable have at most `Δ` neighbours in the co-occurrence graph, and let the
solutions of `ψ` contain no subcube of dimension `D`. Then
`|sol ψ| ≤ 2 ^ ((1 - 1/k) N + (D - 1)(Δ + 1)/k)`. -/
theorem card_solutions_le_of_neighbors {ψ : ClauseSet N} {k Δ D : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ C ∈ ψ, C.card ≤ k) (hdeg : ∀ u, (ψ.neighbors u).card ≤ Δ)
    (hfree : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D) :
    (ψ.solutions.card : ℝ) ≤
      (2 : ℝ) ^ ((1 - 1 / (k : ℝ)) * N + (((D - 1) * (Δ + 1) : ℕ) : ℝ) / k) :=
  Isolation.card_solutions_le_of_neighbors hk1 hk hdeg hfree

/-- **Theorem A.** For every `k ≥ 1` and `ε > 0` there is a constant `C ≥ 0` such that every
clause set `φ` over `N` variables whose clauses have at most `k` literals, and whose solutions
contain no subcube of dimension `D`, has at most `2 ^ ((1 - 1/k + ε) N + C D)` solutions. -/
theorem card_solutions_le_of_not_containsSubcube (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (φ : ClauseSet N) (D : ℕ), (∀ C ∈ φ, C.card ≤ k) →
      ¬ ContainsSubcube (φ.solutions : Set (BitString N)) D →
      (φ.solutions.card : ℝ) ≤ 2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) :=
  SubcubeFree.card_solutions_le k hk hε

end Complexity.ClauseSet

namespace Complexity

/-- **Theorem A for CNFs.** For every `k ≥ 1` and `ε > 0` there is a constant `C ≥ 0` such that
every CNF `φ` of width at most `k` over `N` variables whose accepted inputs contain no subcube of
dimension `D` accepts at most `2 ^ ((1 - 1/k + ε) N + C D)` inputs. -/
theorem CNF.card_accepting_le_of_not_containsSubcube (k : ℕ) (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (φ : CNF N) (D : ℕ), φ.width ≤ k →
      ¬ ContainsSubcube {x | φ.eval x = true} D →
      ((Finset.univ.filter fun x => φ.eval x = true).card : ℝ) ≤
        2 ^ ((1 - 1 / (k : ℝ) + ε) * N + C * D) := by
  obtain ⟨C, hC, hbound⟩ := ClauseSet.card_solutions_le_of_not_containsSubcube k hk hε
  refine ⟨C, hC, fun N φ D hφ hfree => ?_⟩
  rw [← CNF.solutions_toClauseSet]
  refine hbound N φ.toClauseSet D
    (fun C hC => (CNF.card_le_width_of_mem_toClauseSet hC).trans hφ) fun h => hfree ?_
  refine h.mono fun x hx => ?_
  exact (CNF.mem_solutions_toClauseSet φ x).mp hx

end Complexity

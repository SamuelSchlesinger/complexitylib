/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Neighbors and cliques in the Boolean input cube

Neighbors are single-bit flips. Distinct neighbors of a vertex are distance
two apart, so every clique has at most two vertices.
-/

@[expose] public section

namespace Algebraic.BooleanCube

variable {ι : Type*}

/-- The graph whose edges change exactly one Boolean coordinate. -/
def graph [Fintype ι] : SimpleGraph (ι → Bool) where
  Adj left right := hammingDist left right = 1
  symm := ⟨by intro left right h; simpa only [hammingDist_comm] using h⟩
  loopless := ⟨by intro vector; simp⟩

variable [Fintype ι] [DecidableEq ι]

/-- Flip one coordinate of a Boolean vertex. -/
def flip (vertex : ι → Bool) (i : ι) : ι → Bool := Function.update vertex i (!(vertex i))

/-- A single flip changes exactly one coordinate. -/
theorem hammingDist_flip (vertex : ι → Bool) (i : ι) : hammingDist vertex (flip vertex i) = 1 := by
  have support : Finset.univ.filter (fun j => vertex j ≠ flip vertex i j) = {i} := by
    ext j
    by_cases same : j = i <;> cases value : vertex i <;> simp [flip, same, value]
  simp [hammingDist, support]

/-- A flipped vertex is different from the original vertex. -/
theorem flip_ne (vertex : ι → Bool) (i : ι) : flip vertex i ≠ vertex := by
  intro equal
  have h := hammingDist_flip vertex i
  simp [equal] at h

/-- Every neighbor is obtained by flipping a unique differing coordinate. -/
theorem adjacent_iff_flip (left right : ι → Bool) :
    graph.Adj left right ↔ ∃ i, right = flip left i := by
  constructor
  · intro adjacent
    obtain ⟨i, support⟩ := Finset.card_eq_one.mp adjacent
    refine ⟨i, ?_⟩
    funext j
    have difference : left j ≠ right j ↔ j = i := by
      simpa using Finset.ext_iff.mp support j
    by_cases same : j = i
    · have different := difference.mpr same
      cases hl : left j <;> cases hr : right j <;> simp_all [flip]
    · have equal : left j = right j := not_not.mp (mt difference.mp same)
      simp [flip, same, equal]
  · rintro ⟨i, rfl⟩
    exact hammingDist_flip left i

/-- Flipping two different coordinates gives neighbors at mutual distance two. -/
theorem hammingDist_flip_flip (vertex : ι → Bool) {i j : ι} (different : i ≠ j) :
    hammingDist (flip vertex i) (flip vertex j) = 2 := by
  have support : Finset.univ.filter (fun k => flip vertex i k ≠ flip vertex j k) = {i, j} := by
    ext k
    by_cases first : k = i <;> by_cases second : k = j <;>
      cases hi : vertex i <;> cases hj : vertex j <;> simp_all [flip]
  simp [hammingDist, support, different]

/-- Distinct neighbors of a Boolean vertex are never adjacent to each other. -/
theorem not_adjacent_of_common_neighbor {base left right : ι → Bool}
    (hl : graph.Adj base left) (hr : graph.Adj base right) (different : left ≠ right) :
    ¬graph.Adj left right := by
  obtain ⟨i, rfl⟩ := (adjacent_iff_flip base left).mp hl
  obtain ⟨j, rfl⟩ := (adjacent_iff_flip base right).mp hr
  have distinct : i ≠ j := by intro equal; exact different (equal ▸ rfl)
  have distance := hammingDist_flip_flip base distinct
  change hammingDist _ _ ≠ 1
  omega

/-- Every clique in the Boolean cube has at most two vertices. -/
theorem card_le_two_of_pairwise_adjacent (vertices : Finset (ι → Bool))
    (clique : ∀ a ∈ vertices, ∀ b ∈ vertices, a ≠ b → graph.Adj a b) : vertices.card ≤ 2 := by
  by_contra large
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge large)
  exact not_adjacent_of_common_neighbor (clique a ha b hb hab) (clique a ha c hc hac) hbc
    (clique b hb c hc hbc)

end Algebraic.BooleanCube

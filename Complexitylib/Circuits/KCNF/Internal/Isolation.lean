/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexitylib.Circuits.KCNF.Internal.Coding
import Mathlib.Tactic

/-!
# Moves, local far-isolation, and the bounded-degree bound -- proofs

Internal proofs for `Complexitylib.Circuits.KCNF.SubcubeFree`.

A clause is satisfied by a point as soon as it is satisfied by a solution that agrees with the
point on the clause's variables (`sat_of_agree`). Flipping a family of separated moves of a
solution, or a part of a move that no clause connects to the rest, agrees on every clause with
the solution or with one of the moved solutions. A largest set of pairwise non-adjacent
non-isolated directions spans a subcube of solutions, so it has fewer than `D` elements when
there is no subcube of dimension `D`; every non-isolated direction lies in its closed
neighbourhood.
-/

@[expose] public section

namespace Complexity

open Finset

variable {N : ℕ}

namespace ClauseSet

namespace Isolation

/-- The clause `C` mentions a variable of `T`. -/
def Meets (C : Finset (Literal N)) (T : Finset (Fin N)) : Prop := ∃ l ∈ C, l.var ∈ T

/-- A point satisfies every clause of `ψ` that a solution agreeing with it on the clause's
variables satisfies. -/
theorem sat_of_agree {ψ : ClauseSet N} {w : BitString N}
    (h : ∀ C ∈ ψ, ∃ z ∈ ψ.solutions, ∀ l ∈ C, z l.var = w l.var) : w ∈ ψ.solutions := by
  rw [mem_solutions]
  intro C hC
  obtain ⟨z, hz, hagree⟩ := h C hC
  obtain ⟨l, hl, htrue⟩ := mem_solutions.mp hz C hC
  refine ⟨l, hl, ?_⟩
  simpa only [Literal.eval, hagree l hl] using htrue

/-- **Lemma 3 (a).** If `x ⊕ e_T` is a solution and no clause meets both `T' ⊆ T` and `T \ T'`,
then `x ⊕ e_{T'}` is a solution. In particular every connected component of a move in the
co-occurrence graph is a move. -/
theorem flipOn_mem_of_closed {ψ : ClauseSet N} {x : BitString N} {T T' : Finset (Fin N)}
    (hx : x ∈ ψ.solutions) (hT : x.flipOn T ∈ ψ.solutions) (hsub : T' ⊆ T)
    (hclosed : ∀ C ∈ ψ, Meets C T' → ¬ Meets C (T \ T')) :
    x.flipOn T' ∈ ψ.solutions := by
  refine sat_of_agree fun C hC => ?_
  by_cases hmeet : Meets C T'
  · refine ⟨x.flipOn T, hT, fun l hl =>
      BitString.flipOn_apply_eq_of_iff ⟨fun hlT => ?_, fun h => hsub h⟩⟩
    by_contra hlT'
    exact hclosed C hC hmeet ⟨l, hl, mem_sdiff.mpr ⟨hlT, hlT'⟩⟩
  · refine ⟨x, hx, fun l hl => ?_⟩
    rw [BitString.flipOn_apply_of_not_mem fun h => hmeet ⟨l, hl, h⟩]

/-- **Lemma 3 (b).** Let `x` be a solution and `T j`, `j ∈ s`, moves of `x` (each `x ⊕ e_{T j}`
is a solution) that are pairwise separated: no clause meets two of them. Then for every
`J ⊆ s`, `x ⊕ e_{⋃_{j ∈ J} T j}` is a solution. -/
theorem flipOn_biUnion_mem_of_separated {ι : Type*} {ψ : ClauseSet N}
    {x : BitString N} {s : Finset ι} {T : ι → Finset (Fin N)} (hx : x ∈ ψ.solutions)
    (hmove : ∀ j ∈ s, x.flipOn (T j) ∈ ψ.solutions)
    (hsep : ∀ C ∈ ψ, ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Meets C (T j) → ¬ Meets C (T j'))
    {J : Finset ι} (hJ : J ⊆ s) : x.flipOn (J.biUnion T) ∈ ψ.solutions := by
  refine sat_of_agree fun C hC => ?_
  by_cases hmeet : ∃ j ∈ J, Meets C (T j)
  · obtain ⟨j, hj, hjmeet⟩ := hmeet
    refine ⟨x.flipOn (T j), hmove j (hJ hj), fun l hl => BitString.flipOn_apply_eq_of_iff ?_⟩
    constructor
    · exact fun h => mem_biUnion.mpr ⟨j, hj, h⟩
    · intro h
      obtain ⟨j', hj', hlj'⟩ := mem_biUnion.mp h
      by_contra hlj
      have hne : j ≠ j' := fun hjj => hlj (hjj ▸ hlj')
      exact hsep C hC j (hJ hj) j' (hJ hj') hne hjmeet ⟨l, hl, hlj'⟩
  · push Not at hmeet
    refine ⟨x, hx, fun l hl => ?_⟩
    rw [BitString.flipOn_apply_of_not_mem]
    intro h
    obtain ⟨j, hj, hlj⟩ := mem_biUnion.mp h
    exact hmeet j hj ⟨l, hl, hlj⟩

/-- Pairwise non-adjacent singleton moves span a subcube of solutions. -/
theorem flipOn_mem_of_independent {ψ : ClauseSet N} {x : BitString N} {M : Finset (Fin N)}
    (hx : x ∈ ψ.solutions) (hmove : ∀ i ∈ M, x.flipOn {i} ∈ ψ.solutions)
    (hind : ∀ u ∈ M, ∀ w ∈ M, u ≠ w → w ∉ ψ.neighbors u) {T : Finset (Fin N)} (hT : T ⊆ M) :
    x.flipOn T ∈ ψ.solutions := by
  have h := flipOn_biUnion_mem_of_separated (T := fun i => {i}) hx hmove
    (fun C hC j hj j' hj' hne hmeet hmeet' => by
      obtain ⟨l, hl, hlj⟩ := hmeet
      obtain ⟨l', hl', hlj'⟩ := hmeet'
      rw [mem_singleton] at hlj hlj'
      apply hind j hj j' hj' hne
      simp only [neighbors, mem_filter, mem_univ, true_and]
      exact ⟨Ne.symm hne, C, hC, ⟨l, hl, hlj⟩, l', hl', hlj'⟩) hT
  simpa using h

theorem mem_neighbors_comm {ψ : ClauseSet N} {u w : Fin N} :
    w ∈ ψ.neighbors u ↔ u ∈ ψ.neighbors w := by
  simp only [neighbors, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hne, C, hC, hu, hw⟩
    exact ⟨Ne.symm hne, C, hC, hw, hu⟩
  · rintro ⟨hne, C, hC, hw, hu⟩
    exact ⟨Ne.symm hne, C, hC, hu, hw⟩

/-- **Lemma 4 (local far-isolation, `d = 1`).** If every variable has at most `Δ` neighbours in
the co-occurrence graph of `ψ` and the solutions contain no subcube of dimension `D`, then every
solution has at most `(D - 1)(Δ + 1)` non-isolated directions. -/
theorem card_compl_isolatedDirections_le {ψ : ClauseSet N} {Δ D : ℕ}
    (hdeg : ∀ u, (ψ.neighbors u).card ≤ Δ)
    (hfree : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D) {x : BitString N}
    (hx : x ∈ ψ.solutions) :
    (univ \ isolatedDirections ψ.solutions x).card ≤ (D - 1) * (Δ + 1) := by
  set NI := univ \ isolatedDirections ψ.solutions x with hNI
  have hmemNI : ∀ i, i ∈ NI ↔ x.flipOn {i} ∈ ψ.solutions := by
    intro i
    simp [hNI, isolatedDirections]
  let Ind : Finset (Finset (Fin N)) := NI.powerset.filter fun M =>
    ∀ u ∈ M, ∀ w ∈ M, u ≠ w → w ∉ ψ.neighbors u
  have hInd : (∅ : Finset (Fin N)) ∈ Ind := by simp [Ind]
  obtain ⟨M, hM, hmax⟩ := Ind.exists_max_image card ⟨∅, hInd⟩
  simp only [Ind, mem_filter, mem_powerset] at hM
  obtain ⟨hMNI, hMind⟩ := hM
  have hmove : ∀ i ∈ M, x.flipOn {i} ∈ ψ.solutions := fun i hi => (hmemNI i).mp (hMNI hi)
  -- the independent set is small
  have hMcard : M.card ≤ D - 1 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨J, hJM, hJcard⟩ := exists_subset_card_eq (s := M) (n := D) (by omega)
    exact hfree ⟨x, J, hJcard, fun T hT =>
      flipOn_mem_of_independent hx hmove hMind (hT.trans hJM)⟩
  -- every non-isolated direction is in its closed neighbourhood
  have hcover : NI ⊆ M ∪ M.biUnion ψ.neighbors := by
    intro i hi
    by_cases hiM : i ∈ M
    · exact mem_union_left _ hiM
    · refine mem_union_right _ (mem_biUnion.mpr ?_)
      by_contra hnone
      push Not at hnone
      have hins : insert i M ∈ Ind := by
        simp only [Ind, mem_filter, mem_powerset]
        refine ⟨insert_subset hi hMNI, fun u hu w hw hne => ?_⟩
        rw [mem_insert] at hu hw
        by_cases hui : u = i
        · subst hui
          rcases hw with hwi | hwM
          · exact absurd hwi.symm hne
          · exact fun h => hnone w hwM (mem_neighbors_comm.mp h)
        · have huM : u ∈ M := hu.resolve_left hui
          by_cases hwi : w = i
          · subst hwi
            exact hnone u huM
          · exact hMind u huM w (hw.resolve_left hwi) hne
      have := hmax _ hins
      rw [card_insert_of_notMem hiM] at this
      omega
  calc NI.card ≤ (M ∪ M.biUnion ψ.neighbors).card := card_le_card hcover
    _ ≤ M.card + (M.biUnion ψ.neighbors).card := card_union_le _ _
    _ ≤ M.card + ∑ m ∈ M, (ψ.neighbors m).card := by gcongr; exact card_biUnion_le
    _ ≤ M.card + ∑ _m ∈ M, Δ := by gcongr with m; exact hdeg m
    _ = M.card * (Δ + 1) := by rw [sum_const, smul_eq_mul]; ring
    _ ≤ (D - 1) * (Δ + 1) := Nat.mul_le_mul_right _ hMcard

/-- In a clause set of width at most `k`, a variable mentioned by at most `c` clauses has at most
`c (k - 1)` neighbours. -/
theorem card_neighbors_le {ψ : ClauseSet N} {k : ℕ} (hk : ∀ C ∈ ψ, C.card ≤ k) (u : Fin N) :
    (ψ.neighbors u).card ≤ ψ.occurrences u * (k - 1) := by
  let Cu := ψ.filter fun C => ∃ l ∈ C, l.var = u
  have hsub : ψ.neighbors u ⊆ Cu.biUnion fun C => (C.image Literal.var).erase u := by
    intro w hw
    simp only [neighbors, mem_filter, mem_univ, true_and] at hw
    obtain ⟨hne, C, hC, hu, l, hl, hlw⟩ := hw
    refine mem_biUnion.mpr ⟨C, mem_filter.mpr ⟨hC, hu⟩, mem_erase.mpr ⟨hne, ?_⟩⟩
    exact mem_image.mpr ⟨l, hl, hlw⟩
  calc (ψ.neighbors u).card
      ≤ (Cu.biUnion fun C => (C.image Literal.var).erase u).card := card_le_card hsub
    _ ≤ ∑ C ∈ Cu, ((C.image Literal.var).erase u).card := card_biUnion_le
    _ ≤ ∑ _C ∈ Cu, (k - 1) := by
        refine sum_le_sum fun C hC => ?_
        obtain ⟨hCψ, l, hl, hlu⟩ := mem_filter.mp hC
        have hmem : u ∈ C.image Literal.var := mem_image.mpr ⟨l, hl, hlu⟩
        rw [card_erase_of_mem hmem]
        exact Nat.sub_le_sub_right (card_image_le.trans (hk C hCψ)) 1
    _ = ψ.occurrences u * (k - 1) := by rw [sum_const, smul_eq_mul]; rfl

/-- **The bounded-degree form of Theorem A.** Let every clause of `ψ` have at most `k ≥ 1`
literals, let every variable have at most `Δ` neighbours in the co-occurrence graph, and let the
solutions contain no subcube of dimension `D`. Then
`|sol ψ| ≤ 2 ^ ((1 - 1/k) N + (D - 1)(Δ + 1)/k)`. -/
theorem card_solutions_le_of_neighbors {ψ : ClauseSet N} {k Δ D : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ C ∈ ψ, C.card ≤ k) (hdeg : ∀ u, (ψ.neighbors u).card ≤ Δ)
    (hfree : ¬ ContainsSubcube (ψ.solutions : Set (BitString N)) D) :
    (ψ.solutions.card : ℝ) ≤
      (2 : ℝ) ^ ((1 - 1 / (k : ℝ)) * N + (((D - 1) * (Δ + 1) : ℕ) : ℝ) / k) := by
  set m : ℕ := (D - 1) * (Δ + 1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hcoding := Coding.sum_two_rpow_isolated_div_le hk1 hk
  -- each solution has at least `N - m` isolated directions
  have hiso : ∀ x ∈ ψ.solutions,
      ((N : ℝ) - m) / k ≤ ((isolatedDirections ψ.solutions x).card : ℝ) / k := by
    intro x hx
    refine div_le_div_of_nonneg_right ?_ hkpos.le
    have hle := card_compl_isolatedDirections_le hdeg hfree hx
    have hsplit : (univ \ isolatedDirections ψ.solutions x).card +
        (isolatedDirections ψ.solutions x).card = N := by
      rw [card_sdiff_add_card_eq_card (subset_univ _), card_univ, Fintype.card_fin]
    have : (N : ℝ) = ((univ \ isolatedDirections ψ.solutions x).card : ℝ) +
        (isolatedDirections ψ.solutions x).card := by exact_mod_cast hsplit.symm
    have hle' : ((univ \ isolatedDirections ψ.solutions x).card : ℝ) ≤ m := by
      exact_mod_cast hle
    linarith
  have hlower : (ψ.solutions.card : ℝ) * (2 : ℝ) ^ (((N : ℝ) - m) / k) ≤ 2 ^ N := by
    calc (ψ.solutions.card : ℝ) * (2 : ℝ) ^ (((N : ℝ) - m) / k)
        = ∑ _x ∈ ψ.solutions, (2 : ℝ) ^ (((N : ℝ) - m) / k) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ ψ.solutions,
            (2 : ℝ) ^ (((isolatedDirections ψ.solutions x).card : ℝ) / k) :=
          sum_le_sum fun x hx => Real.rpow_le_rpow_of_exponent_le (by norm_num) (hiso x hx)
      _ ≤ 2 ^ N := hcoding
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (((N : ℝ) - m) / k) := by positivity
  rw [← le_div_iff₀ hpos, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)] at hlower
  refine hlower.trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

end Isolation

end ClauseSet

end Complexity

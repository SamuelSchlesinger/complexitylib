/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Internal.Sparsification.Tree
import Mathlib.Tactic

/-!
# Sparsification -- explicit thresholds and the leaf count

For a width `k ≥ 1` and a parameter `α ≥ 1`, let `X = 2 k α` and take the thresholds
`θ 0 = 1`, `θ j = α X ^ (2 j - 1)` (`threshold`). Then along every branch ending in a sparse node,
at most `N X ^ (2 c - 1)` clauses of size `c` are introduced (`Path.card_introducedOfCard_le_pow`),
by induction on `c` from the recursive bound of the path analysis: the products
`θ (c - h) · X ^ (2 h - 1)` all equal `α X ^ (2 c - 2)`, and `2 α c ≤ X`. Hence every branch has
length at most `Λ = N k X ^ (2 k)` and at most `(k - 1) N / α` petal steps.

A leaf is determined by the positions of its petal steps among the first `Λ` steps, so there are
at most `∑_{j ≤ (k - 1) N / α} (Λ choose j)` leaves (`exists_leaves`). The leaves are sparse, so
every variable occurs in at most `2 ∑_{c < k} θ c` of their clauses
(`occurrences_le_of_sparse`).
-/

@[expose] public section

namespace Complexity.ClauseSet.Sparsify

open Finset

variable {N : ℕ}

/-- The base `X = 2 k α` of the thresholds. -/
def base (k α : ℕ) : ℕ := 2 * k * α

/-- The thresholds: `θ 0 = 1` and `θ j = α X ^ (2 j - 1)` for `j ≥ 1`. -/
def threshold (k α j : ℕ) : ℕ := if j = 0 then 1 else α * base k α ^ (2 * j - 1)

variable {k α : ℕ}

theorem one_le_base (hk : 1 ≤ k) (hα : 1 ≤ α) : 1 ≤ base k α := by
  unfold base
  have : 1 ≤ k * α := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  nlinarith

theorem one_le_threshold (hk : 1 ≤ k) (hα : 1 ≤ α) (j : ℕ) : 1 ≤ threshold k α j := by
  unfold threshold
  split_ifs
  · exact le_rfl
  · exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by have := one_le_base hk hα; omega)))

theorem threshold_of_one_le {j : ℕ} (hj : 1 ≤ j) :
    threshold k α j = α * base k α ^ (2 * j - 1) := by
  unfold threshold
  rw [ite_eq_right (by omega)]

theorem threshold_pred_le (hk : 1 ≤ k) (hα : 1 ≤ α) {c : ℕ} (hc : 1 ≤ c) :
    threshold k α (c - 1) ≤ α * base k α ^ (2 * c - 2) := by
  rcases Nat.eq_or_lt_of_le hc with rfl | hc2
  · simp [threshold, hα]
  · rw [threshold_of_one_le (by omega)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_base hk hα) (by omega))

namespace Path

variable (hk : 1 ≤ k) (hα : 1 ≤ α)
include hk hα

/-- **Introduced clauses of each size.** Along a branch from a clause set of width `k` ending in
a sparse node, at most `N X ^ (2 c - 1)` clauses of size `c` are introduced, for `1 ≤ c ≤ k`. -/
theorem card_introducedOfCard_le_pow (P : Path (threshold k α) N)
    (hleaf : Sparse (threshold k α) (P.node P.len)) :
    ∀ c, 1 ≤ c → c ≤ k → (P.introducedOfCard c).card ≤ N * base k α ^ (2 * c - 1) := by
  have hθ := one_le_threshold hk hα
  set X := base k α
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc hck
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hrec := P.card_introducedOfCard_le hθ hleaf hc
    have hterm : ∀ h ∈ Ico 1 (c' + 1),
        2 * threshold k α (c' + 1 - h) * (P.introducedOfCard h).card ≤
          2 * α * N * X ^ (2 * c') := by
      intro h hh
      obtain ⟨hh1, hhc⟩ := mem_Ico.mp hh
      rw [threshold_of_one_le (by omega)]
      have hIh := ih h hhc hh1 (by omega)
      calc 2 * (α * X ^ (2 * (c' + 1 - h) - 1)) * (P.introducedOfCard h).card
          ≤ 2 * (α * X ^ (2 * (c' + 1 - h) - 1)) * (N * X ^ (2 * h - 1)) :=
            Nat.mul_le_mul_left _ hIh
        _ = 2 * α * N * X ^ ((2 * (c' + 1 - h) - 1) + (2 * h - 1)) := by rw [pow_add]; ring
        _ = 2 * α * N * X ^ (2 * c') := by congr 2; omega
    calc (P.introducedOfCard (c' + 1)).card
        ≤ 2 * N * threshold k α (c' + 1 - 1) +
            ∑ h ∈ Ico 1 (c' + 1), 2 * threshold k α (c' + 1 - h) *
              (P.introducedOfCard h).card := hrec
      _ ≤ 2 * N * (α * X ^ (2 * (c' + 1) - 2)) + ∑ _h ∈ Ico 1 (c' + 1), 2 * α * N * X ^ (2 * c') :=
          add_le_add (Nat.mul_le_mul_left _ (threshold_pred_le hk hα hc)) (sum_le_sum hterm)
      _ = (c' + 1) * (2 * α * N * X ^ (2 * c')) := by
          rw [sum_const, Nat.card_Ico, smul_eq_mul, Nat.add_sub_cancel,
            show 2 * (c' + 1) - 2 = 2 * c' by omega]
          ring
      _ ≤ k * (2 * α * N * X ^ (2 * c')) := Nat.mul_le_mul_right _ hck
      _ = N * X ^ (2 * (c' + 1) - 1) := by
          rw [show 2 * (c' + 1) - 1 = 2 * c' + 1 by omega, pow_succ]
          simp only [X, base]
          ring

/-- **Branches are short.** A branch from a clause set of width `k` ending in a sparse node has
at most `N k X ^ (2 k)` steps. -/
theorem len_le (P : Path (threshold k α) N) (hk0 : ∀ C ∈ P.node 0, C.card ≤ k)
    (hleaf : Sparse (threshold k α) (P.node P.len)) :
    P.len ≤ N * (k * base k α ^ (2 * k)) := by
  have hθ := one_le_threshold hk hα
  calc P.len ≤ P.introduced.card := P.len_le_card_introduced hθ
    _ = ∑ c ∈ Ico 1 k, (P.introducedOfCard c).card := P.card_introduced_eq_sum hθ hk0
    _ ≤ ∑ _c ∈ Ico 1 k, N * base k α ^ (2 * k) := by
        refine sum_le_sum fun c hc => ?_
        obtain ⟨hc1, hck⟩ := mem_Ico.mp hc
        refine (card_introducedOfCard_le_pow hk hα P hleaf c hc1 hck.le).trans ?_
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_base hk hα) (by omega))
    _ ≤ N * (k * base k α ^ (2 * k)) := by
        rw [sum_const, Nat.card_Ico, smul_eq_mul]
        calc (k - 1) * (N * base k α ^ (2 * k)) ≤ k * (N * base k α ^ (2 * k)) :=
              Nat.mul_le_mul_right _ (Nat.sub_le k 1)
          _ = N * (k * base k α ^ (2 * k)) := by ring

/-- **Few petal steps.** A branch from a clause set of width `k` ending in a sparse node has at
most `(k - 1) N / α` petal steps. -/
theorem mul_card_petal_le (P : Path (threshold k α) N) (hk0 : ∀ C ∈ P.node 0, C.card ≤ k)
    (hleaf : Sparse (threshold k α) (P.node P.len)) :
    α * ((range P.len).filter fun i => P.dir i = true).card ≤ (k - 1) * N := by
  have hθ := one_le_threshold hk hα
  have hj : ∀ j ∈ Ico 1 k, α * (P.petalSteps j).card ≤ N := by
    intro j hj
    obtain ⟨hj1, hjk⟩ := mem_Ico.mp hj
    have h1 := P.mul_card_petalSteps_le hθ j
    have h2 := card_introducedOfCard_le_pow hk hα P hleaf j hj1 hjk.le
    rw [threshold_of_one_le hj1] at h1
    have hpos : 0 < base k α ^ (2 * j - 1) := pow_pos (one_le_base hk hα) _
    have : α * (P.petalSteps j).card * base k α ^ (2 * j - 1) ≤
        N * base k α ^ (2 * j - 1) := by
      calc α * (P.petalSteps j).card * base k α ^ (2 * j - 1)
          = α * base k α ^ (2 * j - 1) * (P.petalSteps j).card := by ring
        _ ≤ N * base k α ^ (2 * j - 1) := h1.trans h2
    exact Nat.le_of_mul_le_mul_right this hpos
  calc α * ((range P.len).filter fun i => P.dir i = true).card
      ≤ α * ∑ j ∈ Ico 1 k, (P.petalSteps j).card :=
        Nat.mul_le_mul_left _ (P.card_petal_le_sum hθ hk0)
    _ = ∑ j ∈ Ico 1 k, α * (P.petalSteps j).card := mul_sum _ _ _
    _ ≤ ∑ _j ∈ Ico 1 k, N := sum_le_sum hj
    _ = (k - 1) * N := by rw [sum_const, Nat.card_Ico, smul_eq_mul]

end Path

/-- **The leaves.** For width `k ≥ 1` and `α ≥ 1`, every clause set `φ` of width `k` has a family
of at most `∑_{j ≤ (k - 1) N / α} (Λ choose j)` sparse clause sets, `Λ = N k X ^ (2 k)`, each
refining `φ` and having only solutions of `φ`, whose solutions cover those of `φ`. -/
theorem exists_leaves (hk : 1 ≤ k) (hα : 1 ≤ α) (φ : ClauseSet N)
    (hφ : ∀ C ∈ φ, C.card ≤ k) :
    ∃ Ψ : Finset (ClauseSet N),
      Ψ.card ≤ ∑ j ∈ range ((k - 1) * N / α + 1), (N * (k * base k α ^ (2 * k))).choose j ∧
      (∀ ψ ∈ Ψ, Sparse (threshold k α) ψ ∧ (∀ C ∈ ψ, ∃ D ∈ φ, C ⊆ D) ∧
        ∀ x, ψ.Sat x → φ.Sat x) ∧
      ∀ x, φ.Sat x → ∃ ψ ∈ Ψ, ψ.Sat x := by
  classical
  have hθ := one_le_threshold hk hα
  set θ := threshold k α
  set Λ := N * (k * base k α ^ (2 * k))
  set ρ := (k - 1) * N / α
  set ψ₀ := reduce φ
  have hψ₀ : ∀ C ∈ ψ₀, C.card ≤ k := fun C hC => hφ C (reduce_subset φ hC)
  let S : Finset (Finset ℕ) := (range Λ).powerset.filter (·.card ≤ ρ)
  let leaf : Finset ℕ → ClauseSet N := fun s => walkSeq θ Λ ψ₀ fun i => decide (i ∈ s)
  refine ⟨(S.image leaf).filter (Sparse θ), ?_, ?_, ?_⟩
  · -- counting position sets
    calc ((S.image leaf).filter (Sparse θ)).card ≤ (S.image leaf).card := card_filter_le _ _
      _ ≤ S.card := card_image_le
      _ ≤ ((range (ρ + 1)).biUnion fun j => (range Λ).powersetCard j).card := by
          refine card_le_card fun s hs => ?_
          obtain ⟨hsΛ, hsρ⟩ := mem_filter.mp hs
          exact mem_biUnion.mpr ⟨s.card, mem_range.mpr (by omega),
            mem_powersetCard.mpr ⟨mem_powerset.mp hsΛ, rfl⟩⟩
      _ ≤ ∑ j ∈ range (ρ + 1), ((range Λ).powersetCard j).card := card_biUnion_le
      _ = ∑ j ∈ range (ρ + 1), Λ.choose j := by
          refine sum_congr rfl fun j _ => ?_
          rw [card_powersetCard, card_range]
  · intro ψ hψ
    obtain ⟨hψimg, hsparse⟩ := mem_filter.mp hψ
    obtain ⟨s, -, rfl⟩ := mem_image.mp hψimg
    refine ⟨hsparse, fun C hC => ?_, fun x hx => ?_⟩
    · obtain ⟨D, hD, hCD⟩ := refines_walkSeq hθ hC
      exact ⟨D, reduce_subset φ hD, hCD⟩
    · exact sat_reduce_iff.mp (sat_of_sat_walkSeq hx)
  · intro x hx
    obtain ⟨w, hw, hwx⟩ := exists_isLeafWord_sat hθ ψ₀ (sat_reduce_iff.mpr hx)
    obtain ⟨P, hP0, hPlen, hPleaf, hPdir⟩ := exists_path_of_isLeafWord (reduced_reduce φ) hw
    have hP0k : ∀ C ∈ P.node 0, C.card ≤ k := hP0 ▸ hψ₀
    have hlen : w.length ≤ Λ := hPlen ▸ Path.len_le hk hα P hP0k hPleaf
    have hpetal := Path.mul_card_petal_le hk hα P hP0k hPleaf
    rw [hPdir] at hpetal
    set s := (range w.length).filter fun i => w.getD i false = true
    have hs : s ∈ S := by
      refine mem_filter.mpr ⟨mem_powerset.mpr fun i hi => ?_, ?_⟩
      · exact mem_range.mpr (lt_of_lt_of_le (mem_range.mp (mem_filter.mp hi).1) hlen)
      · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hpetal)
    have hleaf : leaf s = walk θ ψ₀ w := by
      refine walkSeq_eq_walk hw (fun i hi => ?_) hlen
      simp only [s, mem_filter, mem_range, hi, true_and]
      cases w.getD i false <;> simp
    refine ⟨leaf s, mem_filter.mpr ⟨mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩, hleaf ▸ hwx⟩
    rw [hleaf]
    exact hw.sparse_walk

/-- **Bounded occurrences.** In a sparse clause set of width `k`, every variable occurs in at most
`2 ∑_{c < k} θ c` clauses. -/
theorem occurrences_le_of_sparse {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet N}
    (hsparse : Sparse θ ψ) (hk : ∀ C ∈ ψ, C.card ≤ k) (v : Fin N) :
    ψ.occurrences v ≤ 2 * ∑ c ∈ range k, θ c := by
  have hsub : ψ.filter (fun C => ∃ l ∈ C, l.var = v) ⊆
      (univ : Finset Bool).biUnion fun p =>
        (Ico 1 (k + 1)).biUnion fun c => flower ψ c {⟨v, p⟩} := by
    intro C hC
    obtain ⟨hCψ, l, hl, hlv⟩ := mem_filter.mp hC
    have hCpos : 1 ≤ C.card := card_pos.mpr ⟨l, hl⟩
    have hleq : l = ⟨v, l.polarity⟩ := by cases l; simp_all
    refine mem_biUnion.mpr ⟨l.polarity, mem_univ _, mem_biUnion.mpr ⟨C.card,
      mem_Ico.mpr ⟨hCpos, by have := hk C hCψ; omega⟩, mem_flower.mpr ⟨hCψ, rfl, ?_⟩⟩⟩
    rw [singleton_subset_iff, ← hleq]
    exact hl
  calc ψ.occurrences v ≤ ((univ : Finset Bool).biUnion fun p =>
        (Ico 1 (k + 1)).biUnion fun c => flower ψ c {⟨v, p⟩}).card := card_le_card hsub
    _ ≤ ∑ p : Bool, ((Ico 1 (k + 1)).biUnion fun c => flower ψ c {⟨v, p⟩}).card :=
        card_biUnion_le
    _ ≤ ∑ _p : Bool, ∑ c ∈ Ico 1 (k + 1), θ (c - 1) := by
        refine sum_le_sum fun p _ => card_biUnion_le.trans (sum_le_sum fun c hc => ?_)
        exact card_flower_singleton_le_of_sparse hθ hsparse (mem_Ico.mp hc).1 _
    _ = 2 * ∑ c ∈ range k, θ c := by
        rw [sum_const, card_univ, Fintype.card_bool, smul_eq_mul, sum_Ico_eq_sum_range]
        simp

end Complexity.ClauseSet.Sparsify

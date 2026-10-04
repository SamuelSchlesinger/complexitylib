/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.DeletionGame
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Paired
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The explicit border-rank lower bound: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.Explicit`.

* **Tightness.** `weightedLMTensor k` is supported on `ℓ = j + (a - k)`, so the weights
  `a - k`, `j`, `-ℓ` make it tight. Slice `a` has the nonzero entry
  `2^{2^{…}}` at `j = k - a`, `ℓ = 0` if `a ≤ k`, and at `j = 0`, `ℓ = a - k` otherwise.
* **Greedy distinct subset sums.** The invariant is `NoSignedRelation x`: no nontrivial
  combination `∑ ε_t x_t` with `ε_t ∈ {-1, 0, 1}` vanishes, which is equivalent to all subset
  sums being distinct. The *signed sums* `∑ ε_t x_t` of `i` chosen elements number at most
  `3^i`, so a set `A` with more than `3^i` elements has an element `a` outside them; a relation
  with coefficient `±1` on `a` would put `a` among the signed sums, so prepending `a` keeps the
  invariant. After `n + 1` steps, sorting the chosen set gives a strictly increasing tuple; its
  subset sums are subset sums of the chosen set, which are distinct.
* **Clusters in blocks.** Applying the greedy step to the offsets `a - k` of the slices of a
  set `B` gives a strictly increasing cluster in `B` with distinct subset sums of offsets. In a
  block of length `L` the offsets lie in an interval of `L` consecutive integers, so the
  diameter is at most `L - 1`, and the signs of the offsets are those of the block.
* **The paired-cluster hypothesis.** For good blocks `B⁺` and `B⁻`, the greedy clusters satisfy
  the conditions of `PairedKoszulBound`, and their medians `a = c⁺ p ∈ B⁺`, `b = c⁻ p ∈ B⁻`
  witness `DeletionGame.PairedClusterBound` with `D = (2p + 1) / (p + 1)` and
  `R ≥ 3^{2p} + 1`.
* **Arithmetic.** `1 + 2D/3 = 7/3 - 2 / (3 (p + 1))`, and `D ≥ 3/2` iff `p ≥ 1`. For the
  asymptotic form choose `L ≥ 2 R / δ`, so that `R m / L ≤ δ m / 2`, and then `k` so large that
  the constant `D E + 8 L + 2` is at most `δ m / 2`.
* **The unconditional bounds.** The paired-cluster certificate
  `Tensor3.div_mul_phi_sub_le_borderRank_restrictSlices` is `PairedKoszulBound k p L E` with
  `E = 8 (p + 1) L`, for all `k`, `p`, `L`; then `D E = 8 (2p + 1) L`.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal.Explicit

open Finset Filter

/-! ### Tightness -/

theorem lmTensor_apply (k : ℕ) (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ)
    (a j l : Fin (2 * k + 1)) :
    lmTensor k γ a j l = if (l : ℤ) = j + ((a : ℤ) - k) then γ a j else 0 :=
  rfl

theorem lmWeight_ne_zero (k : ℕ) (a j : Fin (2 * k + 1)) : lmWeight k a j ≠ 0 := by
  unfold lmWeight
  exact_mod_cast (pow_pos two_pos _).ne'

theorem tight_lmTensor (k : ℕ) (γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ) :
    (lmTensor k γ).Tight := by
  refine ⟨fun a => (a : ℤ) - k, fun j => j, fun l => -(l : ℤ), fun a b h => ?_,
    fun a j l h => ?_⟩
  · exact Fin.ext (by simpa using h)
  · rw [lmTensor_apply] at h
    split_ifs at h with h'
    · dsimp only
      omega
    · exact absurd rfl h

theorem lmTensor_ne_zero (k : ℕ) {γ : Fin (2 * k + 1) → Fin (2 * k + 1) → ℂ}
    (hγ : ∀ a j, γ a j ≠ 0) (a : Fin (2 * k + 1)) : lmTensor k γ a ≠ 0 := by
  intro h
  have := congrFun (congrFun h ⟨k - a, by omega⟩) ⟨a - k, by omega⟩
  rw [lmTensor_apply, ite_eq_left (by push_cast; omega)] at this
  exact hγ a _ this

theorem tight_weightedLMTensor (k : ℕ) : (weightedLMTensor k).Tight :=
  tight_lmTensor k _

theorem weightedLMTensor_ne_zero (k : ℕ) (a : Fin (2 * k + 1)) : weightedLMTensor k a ≠ 0 :=
  lmTensor_ne_zero k (lmWeight_ne_zero k) a

/-! ### Greedy distinct subset sums -/

/-- No nontrivial combination of the `x t` with coefficients in `{-1, 0, 1}` vanishes. -/
def NoSignedRelation {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∀ ε : Fin n → ℤ, (∀ t, ε t ∈ ({-1, 0, 1} : Finset ℤ)) → ∑ t, ε t * x t = 0 → ∀ t, ε t = 0

/-- The signed sums `∑ ε_t x_t` with coefficients `ε_t ∈ {-1, 0, 1}`. -/
def signedSums {n : ℕ} (x : Fin n → ℤ) : Finset ℤ :=
  (Fintype.piFinset fun _ : Fin n => ({-1, 0, 1} : Finset ℤ)).image fun ε => ∑ t, ε t * x t

theorem card_signedSums_le {n : ℕ} (x : Fin n → ℤ) : (signedSums x).card ≤ 3 ^ n := by
  refine card_image_le.trans ?_
  rw [Fintype.card_piFinset]
  simp

theorem neg_mem_signedCoeffs {e : ℤ} (he : e ∈ ({-1, 0, 1} : Finset ℤ)) :
    -e ∈ ({-1, 0, 1} : Finset ℤ) := by
  simp only [mem_insert, mem_singleton] at he ⊢
  omega

theorem noSignedRelation_cons {n : ℕ} {x : Fin n → ℤ} (hx : NoSignedRelation x) {a : ℤ}
    (ha : a ∉ signedSums x) : NoSignedRelation (Fin.cons a x : Fin (n + 1) → ℤ) := by
  intro ε hε hsum
  rw [Fin.sum_univ_succ] at hsum
  simp only [Fin.cons_zero, Fin.cons_succ] at hsum
  have h0 : ε 0 = 0 := by
    have h := hε 0
    simp only [mem_insert, mem_singleton] at h
    rcases h with h | h | h
    · refine absurd (mem_image.2 ⟨fun t : Fin n => ε t.succ, ?_, ?_⟩) ha
      · simpa [Fintype.mem_piFinset] using fun t : Fin n => hε t.succ
      · rw [h] at hsum
        linarith
    · exact h
    · refine absurd (mem_image.2 ⟨fun t : Fin n => -ε t.succ, ?_, ?_⟩) ha
      · simp only [Fintype.mem_piFinset]
        exact fun t => neg_mem_signedCoeffs (hε t.succ)
      · rw [h] at hsum
        simp only [neg_mul, sum_neg_distrib]
        linarith
  have hrest := hx (fun t => ε t.succ) (fun t => hε t.succ) (by rw [h0] at hsum; simpa using hsum)
  intro t
  induction t using Fin.cases with
  | zero => exact h0
  | succ t => exact hrest t

theorem exists_noSignedRelation (A : Finset ℤ) {m : ℕ} (hA : 3 ^ m < A.card) :
    ∀ i ≤ m + 1, ∃ x : Fin i → ℤ, (∀ t, x t ∈ A) ∧ NoSignedRelation x
  | 0, _ => ⟨Fin.elim0, fun t => t.elim0, fun _ _ _ t => t.elim0⟩
  | i + 1, hi => by
    obtain ⟨x, hxA, hx⟩ := exists_noSignedRelation A hA i (by omega)
    have hlt : (signedSums x).card < A.card :=
      (card_signedSums_le x).trans_lt
        ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans_lt hA)
    obtain ⟨a, haA, ha⟩ := exists_mem_notMem_of_card_lt_card hlt
    refine ⟨Fin.cons a x, fun t => ?_, noSignedRelation_cons hx ha⟩
    induction t using Fin.cases with
    | zero => exact haA
    | succ t => exact hxA t

theorem sum_injective_of_noSignedRelation {n : ℕ} {x : Fin n → ℤ} (hx : NoSignedRelation x) :
    Function.Injective fun I : Finset (Fin n) => ∑ t ∈ I, x t := by
  intro I J hIJ
  have h := hx (fun t => (if t ∈ I then 1 else 0) - (if t ∈ J then 1 else 0))
    (fun t => by split_ifs <;> simp)
    (by
      simp only [sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib, sum_ite_mem, univ_inter]
      exact sub_eq_zero.2 hIJ)
  ext t
  have := h t
  split_ifs at this with h1 h2 h2 <;> simp_all

theorem exists_strictMono_injective_sum (A : Finset ℤ) {n : ℕ} (hA : 3 ^ n < A.card) :
    ∃ x : Fin (n + 1) → ℤ, StrictMono x ∧ (∀ t, x t ∈ A) ∧
      Function.Injective fun I : Finset (Fin (n + 1)) => ∑ t ∈ I, x t := by
  obtain ⟨x, hxA, hx⟩ := exists_noSignedRelation A hA (n + 1) le_rfl
  have hsum := sum_injective_of_noSignedRelation hx
  have hinj : Function.Injective x := fun s t h => by
    have := @hsum {s} {t} (by simp [h])
    simpa using this
  have hX : (univ.image x).card = n + 1 := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  set y := (univ.image x).orderEmbOfFin hX
  have hy : ∀ t, ∃ u, x u = y t := fun t => by
    obtain ⟨u, -, hu⟩ := mem_image.1 ((univ.image x).orderEmbOfFin_mem hX t)
    exact ⟨u, hu⟩
  choose σ hσ using hy
  have hσinj : Function.Injective σ := fun s t h => y.injective (by rw [← hσ, ← hσ, h])
  refine ⟨y, y.strictMono, fun t => ?_, fun I J hIJ => ?_⟩
  · rw [← hσ]
    exact hxA _
  · have hmap : ∀ I : Finset (Fin (n + 1)),
        ∑ t ∈ I, y t = ∑ u ∈ I.map ⟨σ, hσinj⟩, x u := fun I => by
      rw [sum_map]
      simp [hσ]
    simp only at hIJ
    rw [hmap, hmap] at hIJ
    exact map_injective ⟨σ, hσinj⟩ (hsum hIJ)

/-! ### Clusters in blocks -/

variable {k p : ℕ}

theorem exists_cluster (B : Finset (Fin (2 * k + 1))) (hB : 3 ^ (2 * p) + 1 ≤ B.card) :
    ∃ c : Fin (2 * p + 1) → Fin (2 * k + 1), StrictMono c ∧ (∀ t, c t ∈ B) ∧
      Function.Injective fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t := by
  have hoff : Function.Injective fun a : Fin (2 * k + 1) => (a : ℤ) - k :=
    fun a b h => Fin.ext (by simpa using h)
  obtain ⟨x, hx, hxA, hxs⟩ := exists_strictMono_injective_sum
    (B.image fun a : Fin (2 * k + 1) => (a : ℤ) - k) (n := 2 * p)
    (by rw [card_image_of_injective _ hoff]; omega)
  have : ∀ t, ∃ a ∈ B, (a : ℤ) - k = x t := fun t => by simpa using hxA t
  choose c hcB hcx using this
  have hco : clusterOffsets k c = x := funext hcx
  refine ⟨c, fun s t hst => ?_, hcB, by rw [hco]; exact hxs⟩
  have := hx hst
  rw [← hcx, ← hcx] at this
  rw [Fin.lt_def]
  omega

theorem mem_posBlock {L i : ℕ} {a : Fin (2 * k + 1)} :
    a ∈ DeletionGame.posBlock k L i ↔
      (i * L + 1 : ℤ) ≤ DeletionGame.offset k a ∧ DeletionGame.offset k a ≤ (i + 1) * L := by
  simp [DeletionGame.posBlock, DeletionGame.sideBlock]

theorem mem_negBlock {L i : ℕ} {a : Fin (2 * k + 1)} :
    a ∈ DeletionGame.negBlock k L i ↔
      (i * L + 1 : ℤ) ≤ -DeletionGame.offset k a ∧ -DeletionGame.offset k a ≤ (i + 1) * L := by
  simp [DeletionGame.negBlock, DeletionGame.sideBlock]

theorem exists_cluster_posBlock (S : Finset (Fin (2 * k + 1))) {L i : ℕ}
    (hS : 3 ^ (2 * p) + 1 ≤ (S ∩ DeletionGame.posBlock k L i).card) :
    ∃ c : Fin (2 * p + 1) → Fin (2 * k + 1), StrictMono c ∧
      (∀ t, c t ∈ S ∩ DeletionGame.posBlock k L i) ∧
      (Function.Injective fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t) ∧
      clusterOffsets k c (Fin.last (2 * p)) - clusterOffsets k c 0 ≤ (L : ℤ) - 1 ∧
      ∀ t, 1 ≤ clusterOffsets k c t ∧ clusterOffsets k c t ≤ k := by
  obtain ⟨c, hc, hcS, hcs⟩ := exists_cluster _ hS
  have hB : ∀ t, (i * L + 1 : ℤ) ≤ clusterOffsets k c t ∧ clusterOffsets k c t ≤ (i + 1) * L :=
    fun t => mem_posBlock.1 (mem_inter.1 (hcS t)).2
  have hiL : (0 : ℤ) ≤ i * L := by positivity
  refine ⟨c, hc, hcS, hcs, ?_, fun t => ⟨by linarith [(hB t).1], ?_⟩⟩
  · have h1 := (hB (Fin.last (2 * p))).2
    have h0 := (hB 0).1
    linarith
  · have := (c t).isLt
    unfold clusterOffsets
    omega

theorem exists_cluster_negBlock (S : Finset (Fin (2 * k + 1))) {L i : ℕ}
    (hS : 3 ^ (2 * p) + 1 ≤ (S ∩ DeletionGame.negBlock k L i).card) :
    ∃ c : Fin (2 * p + 1) → Fin (2 * k + 1), StrictMono c ∧
      (∀ t, c t ∈ S ∩ DeletionGame.negBlock k L i) ∧
      (Function.Injective fun I : Finset (Fin (2 * p + 1)) => ∑ t ∈ I, clusterOffsets k c t) ∧
      clusterOffsets k c (Fin.last (2 * p)) - clusterOffsets k c 0 ≤ (L : ℤ) - 1 ∧
      ∀ t, -(k : ℤ) ≤ clusterOffsets k c t ∧ clusterOffsets k c t ≤ -1 := by
  obtain ⟨c, hc, hcS, hcs⟩ := exists_cluster _ hS
  have hB : ∀ t, (i * L + 1 : ℤ) ≤ -clusterOffsets k c t ∧ -clusterOffsets k c t ≤ (i + 1) * L :=
    fun t => mem_negBlock.1 (mem_inter.1 (hcS t)).2
  have hiL : (0 : ℤ) ≤ i * L := by positivity
  refine ⟨c, hc, hcS, hcs, ?_, fun t => ⟨?_, by linarith [(hB t).1]⟩⟩
  · have h1 := (hB (Fin.last (2 * p))).1
    have h0 := (hB 0).2
    linarith
  · unfold clusterOffsets
    omega

/-! ### The paired-cluster hypothesis -/

section General

variable {β γ : Type*}

theorem pairedClusterBound_on {T : Tensor3 (Fin (2 * k + 1)) β γ} {L R : ℕ} {E : ℝ}
    (h : PairedKoszulBoundOn T p L E) (hR : 3 ^ (2 * p) + 1 ≤ R) :
    DeletionGame.PairedClusterBound k L R ((2 * p + 1 : ℝ) / (p + 1)) E
      fun S => (T.restrictSlices S).borderRank := by
  intro S i j hi hj
  obtain ⟨cp, hcp, hcpS, hcps, hcpd, hcpo⟩ := exists_cluster_posBlock S (hR.trans hi)
  obtain ⟨cn, hcn, hcnS, hcns, hcnd, hcno⟩ := exists_cluster_negBlock S (hR.trans hj)
  exact ⟨cp ⟨p, by omega⟩, (mem_inter.1 (hcpS _)).2, cn ⟨p, by omega⟩,
    (mem_inter.1 (hcnS _)).2,
    h S cp cn hcp hcn (fun t => (mem_inter.1 (hcpS t)).1) (fun t => (mem_inter.1 (hcnS t)).1)
      hcps.injOn hcns.injOn (by linarith) (by linarith) hcpo hcno⟩

end General

theorem pairedClusterBound {L R : ℕ} {E : ℝ} (h : PairedKoszulBound k p L E)
    (hR : 3 ^ (2 * p) + 1 ≤ R) :
    DeletionGame.PairedClusterBound k L R ((2 * p + 1 : ℝ) / (p + 1)) E
      fun S => ((weightedLMTensor k).restrictSlices S).borderRank :=
  pairedClusterBound_on h hR

/-! ### Arithmetic -/

theorem three_div_two_le {p : ℕ} (hp : 1 ≤ p) : (3 / 2 : ℝ) ≤ (2 * p + 1) / (p + 1) := by
  rw [le_div_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

theorem one_add_two_mul_div_three (p : ℕ) :
    1 + 2 * ((2 * p + 1 : ℝ) / (p + 1)) / 3 = 7 / 3 - 2 / (3 * (p + 1)) := by
  field_simp
  ring

/-- For `L ≥ 2 R / δ`, a lower bound `c m - C - R m / L` with a constant `C` gives `(c - δ) m`
for all large `k`, where `m = 2k + 1`. -/
theorem eventually_sub_mul_le_of_le {f : ℕ → ℝ} {c C δ : ℝ} {R L : ℕ} (hδ : 0 < δ)
    (hL0 : 0 < L) (hLR : 2 * (R : ℝ) / δ ≤ L)
    (h : ∀ᶠ k : ℕ in atTop, c * (2 * k + 1 : ℝ) - C - R * (2 * k + 1) / L ≤ f k) :
    ∀ᶠ k : ℕ in atTop, (c - δ) * (2 * k + 1 : ℝ) ≤ f k := by
  obtain ⟨K, hK⟩ := exists_nat_ge (2 * C / δ)
  filter_upwards [h, eventually_ge_atTop K] with k hk hkK
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
  have hk1 : (K : ℝ) ≤ 2 * k + 1 := by
    have : (K : ℝ) ≤ k := by exact_mod_cast hkK
    linarith
  have h1 : (R : ℝ) * (2 * k + 1) / L ≤ δ / 2 * (2 * k + 1) := by
    rw [div_le_iff₀ hLpos]
    have := (div_le_iff₀ hδ).1 hLR
    have hk0 : (0 : ℝ) ≤ 2 * k + 1 := by positivity
    nlinarith
  have h2 : C ≤ δ / 2 * (2 * k + 1) := by
    have := (div_le_iff₀ hδ).1 (hK.trans hk1)
    linarith
  linarith

/-- A block length `L ≥ 3^{2p} + 1` with `2 (3^{2p} + 1) / δ ≤ L`. -/
theorem exists_blockLength (p : ℕ) (δ : ℝ) :
    ∃ L : ℕ, 3 ^ (2 * p) + 1 ≤ L ∧ 2 * (3 ^ (2 * p) + 1 : ℝ) / δ ≤ L := by
  refine ⟨max (3 ^ (2 * p) + 1) ⌈2 * (3 ^ (2 * p) + 1 : ℝ) / δ⌉₊, le_max_left _ _, ?_⟩
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)

section General

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem le_borderRank_of_pairedKoszulBoundOn {T : Tensor3 (Fin (2 * k + 1)) β γ}
    (hT : T.Tight) (hT0 : ∀ i, T i ≠ 0) {L : ℕ} {E : ℝ} (h : PairedKoszulBoundOn T p L E)
    (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) - (2 * p + 1) / (p + 1) * E -
        (8 * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      T.borderRank := by
  have := hT.le_borderRank_of_pairedClusterBound hT0 (pairedClusterBound_on h le_rfl)
    (Nat.le_add_left 1 _) hL hLk (three_div_two_le hp)
  rw [one_add_two_mul_div_three] at this
  push_cast at this
  exact this

/-- The finite bound with `E = 8 (p + 1) L`, where `D E + 8 L = 16 (p + 1) L`. -/
theorem le_borderRank_of_pairedKoszulBoundOn_eight {T : Tensor3 (Fin (2 * k + 1)) β γ}
    (hT : T.Tight) (hT0 : ∀ i, T i ≠ 0) {L : ℕ} (h : PairedKoszulBoundOn T p L (8 * (p + 1) * L))
    (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) -
        (16 * (p + 1) * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      T.borderRank := by
  have h' := le_borderRank_of_pairedKoszulBoundOn hT hT0 h hp hL hLk
  have hDE : (2 * p + 1 : ℝ) / (p + 1) * (8 * (p + 1) * L) = 8 * (2 * p + 1) * L := by
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  linarith

end General

/-- **The asymptotic bound for a family.** If tight tensors `T k` with nonzero slices satisfy
`PairedKoszulBoundOn (T k) p L (8 (p + 1) L)` for all large `k`, for one block length `L` with
`3^{2p} + 1 ≤ L` and `2 (3^{2p} + 1) / δ ≤ L`, then
`borderRank (T k) ≥ (7/3 - 2 / (3 (p + 1)) - δ) (2k + 1)` for all large `k`. -/
theorem eventually_le_borderRank_of_pairedKoszulBoundOn
    {T : (k : ℕ) → Tensor3 (Fin (2 * k + 1)) (Fin (2 * k + 1)) (Fin (2 * k + 1))}
    (hT : ∀ k, (T k).Tight) (hT0 : ∀ k i, T k i ≠ 0) (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    {L : ℕ} (hL : 3 ^ (2 * p) + 1 ≤ L) (hLδ : 2 * (3 ^ (2 * p) + 1 : ℝ) / δ ≤ L)
    (h : ∀ᶠ k : ℕ in atTop, PairedKoszulBoundOn (T k) p L (8 * (p + 1) * L)) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (T k).borderRank := by
  refine eventually_sub_mul_le_of_le (R := 3 ^ (2 * p) + 1) (C := 16 * (p + 1) * L + 2) hδ
    ((Nat.succ_pos _).trans_le hL) (by exact_mod_cast hLδ) ?_
  filter_upwards [h, eventually_ge_atTop L] with k hk hLk
  have := le_borderRank_of_pairedKoszulBoundOn_eight (hT k) (hT0 k) hk hp hL hLk
  push_cast
  linarith

/-! ### The unconditional bounds -/

theorem le_borderRank_of_pairedKoszulBound {L : ℕ} {E : ℝ} (h : PairedKoszulBound k p L E)
    (hp : 1 ≤ p)
    (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) - (2 * p + 1) / (p + 1) * E -
        (8 * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      (weightedLMTensor k).borderRank :=
  le_borderRank_of_pairedKoszulBoundOn (tight_weightedLMTensor k) (weightedLMTensor_ne_zero k) h
    hp hL hLk

theorem pairedKoszulBound (k p L : ℕ) : PairedKoszulBound k p L (8 * (p + 1) * L) :=
  fun S cp cn hcp hcn hSP hSN hoP hoN hLP hLN hP hN =>
    div_mul_phi_sub_le_borderRank_restrictSlices S cp cn hcp hcn hSP hSN hoP hoN hLP hLN hP hN

theorem le_borderRank {L : ℕ} (hp : 1 ≤ p) (hL : 3 ^ (2 * p) + 1 ≤ L) (hLk : L ≤ k) :
    (7 / 3 - 2 / (3 * (p + 1))) * (2 * k + 1 : ℝ) -
        (16 * (p + 1) * L + (3 ^ (2 * p) + 1) * (2 * k + 1) / L + 2) ≤
      (weightedLMTensor k).borderRank :=
  le_borderRank_of_pairedKoszulBoundOn_eight (tight_weightedLMTensor k)
    (weightedLMTensor_ne_zero k) (pairedKoszulBound k p L) hp hL hLk

theorem eventually_le_borderRank (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - 2 / (3 * (p + 1)) - δ) * (2 * k + 1 : ℝ) ≤
      (weightedLMTensor k).borderRank := by
  obtain ⟨L, hL, hLδ⟩ := exists_blockLength p δ
  exact eventually_le_borderRank_of_pairedKoszulBoundOn (T := weightedLMTensor)
    tight_weightedLMTensor weightedLMTensor_ne_zero hp hδ hL hLδ
    (Eventually.of_forall fun k => pairedKoszulBound k p L)

theorem eventually_nineteen_div_nine {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (19 / 9 - δ) * (2 * k + 1 : ℝ) ≤ (weightedLMTensor k).borderRank := by
  filter_upwards [eventually_le_borderRank (p := 2) (by norm_num) hδ] with k hk
  convert hk using 2
  norm_num

theorem eventually_twentyOne_div_ten :
    ∀ᶠ k : ℕ in atTop, (21 / 10 : ℝ) * (2 * k + 1) ≤ (weightedLMTensor k).borderRank := by
  filter_upwards [eventually_nineteen_div_nine (δ := 1 / 90) (by norm_num)] with k hk
  convert hk using 2
  norm_num

/-- For `ε > 0`, some `p ≥ 1` has `2 / (3 (p + 1)) < ε`. -/
theorem exists_two_div_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, 1 ≤ p ∧ 2 / (3 * ((p : ℝ) + 1)) < ε := by
  obtain ⟨p, hp⟩ := exists_nat_gt (1 / ε)
  refine ⟨p + 1, le_add_self, ?_⟩
  have := (div_lt_iff₀ hε).1 hp
  rw [div_lt_iff₀ (by positivity)]
  push_cast
  nlinarith

theorem eventually_seven_div_three {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (7 / 3 - ε) * (2 * k + 1 : ℝ) ≤ (weightedLMTensor k).borderRank := by
  obtain ⟨p, hp, hlt⟩ := exists_two_div_lt hε
  filter_upwards [eventually_le_borderRank hp (sub_pos.2 hlt)] with k hk
  convert hk using 2
  ring

end Algebraic.Tensor3.Internal.Explicit

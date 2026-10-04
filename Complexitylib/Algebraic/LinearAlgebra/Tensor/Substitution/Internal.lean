/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Instances.Matrix

/-!
# Border substitution for tight tensors: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.Tensor.Substitution`.

* **Only the kernel matters.** Over a field, `ker P ⊆ ker P'` gives `P' = G * P` (factor
  `P'` through `ℂ^α ⧸ ker P ≅ range P` and extend from `range P`), so
  `X ↦ map X Y Z T` at `P'` is the image under `G ⊗ 1 ⊗ 1` of its value at `P`.
* **One step.** Approximate `T` by `T_n = ∑_{s < r + 1} u_{n,s} ⊗ v_{n,s} ⊗ w_{n,s}`. A unit
  vector `û_n` on the line of `u_{n,0}` (any unit vector if `u_{n,0} = 0`) makes `orthProj û_n`
  kill the first summand, so `(orthProj û_n ⊗ 1 ⊗ 1) T_n` has rank at most `r`. A subsequence
  of `û_n` converges on the compact unit sphere of the sup norm, to some `u ≠ 0`, and
  `(X, S) ↦ (X ⊗ 1 ⊗ 1) S` and `orthProj` (at `u ≠ 0`) are continuous.
* **Torus limit.** With weights `σ i = τA i - τA i₀` for the `i₀` minimizing `τA` on the
  support of `u` (and `τC` shifted to compensate), `λ(t) = diag(t ^ σ i)` fixes `T` together
  with the matching diagonal maps on `B` and `C`. Conjugating gives a border-rank bound for
  the projection with kernel `ℂ λ(t) u`. Along `t = 2⁻ⁿ`, `λ(t) u → u i₀ • e_{i₀}`, since
  `σ i > 0` for every other `i` in the support (`τA` is injective), and the set of `v` whose
  projection satisfies the bound is closed at `v ≠ 0`. The projection along `e_{i₀}` has the
  same kernel as the diagonal `0/1` matrix that zeroes slice `i₀`.
* **Deletion.** For `T` restricted to `S`, the zeroed slice `i₀` is in `S`, or else the bound
  already holds for the restriction to `S` and any further deletion keeps it. Iterating gives
  the deletion order; once the bound reaches `0`, the restricted tensor is zero, which forces
  at most `r` nonzero slices.
-/

@[expose] public section

namespace Algebraic.Tensor3.Internal

open Finset Matrix Filter Topology

variable {α β γ α' β' γ' α'' : Type*}

section OrthProj

variable [Fintype α] [DecidableEq α]

theorem orthProj_mulVec (u v : α → ℂ) :
    orthProj u *ᵥ v = v - ((star u ⬝ᵥ u)⁻¹ * (star u ⬝ᵥ v)) • u := by
  rw [orthProj, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

omit [DecidableEq α] in
theorem star_dotProduct_self_ne_zero {u : α → ℂ} (hu : u ≠ 0) : star u ⬝ᵥ u ≠ 0 := by
  open ComplexOrder in exact fun h => hu (dotProduct_star_self_eq_zero.mp h)

theorem orthProj_mulVec_self (u : α → ℂ) : orthProj u *ᵥ u = 0 := by
  by_cases hu : u = 0
  · subst hu
    simp
  · rw [orthProj_mulVec, inv_mul_cancel₀ (star_dotProduct_self_ne_zero hu), one_smul, sub_self]

theorem orthProj_mulVec_eq_zero_iff {u v : α → ℂ} :
    orthProj u *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • u := by
  constructor
  · intro h
    exact ⟨_, sub_eq_zero.mp ((orthProj_mulVec u v).symm.trans h)⟩
  · rintro ⟨c, rfl⟩
    rw [mulVec_smul, orthProj_mulVec_self, smul_zero]

theorem continuousAt_orthProj {u : α → ℂ} (hu : u ≠ 0) :
    ContinuousAt (orthProj : (α → ℂ) → Matrix α α ℂ) u := by
  have hd : Continuous fun u : α → ℂ => star u ⬝ᵥ u :=
    continuous_star.dotProduct continuous_id
  have hv : Continuous fun u : α → ℂ => vecMulVec u (star u) := by
    unfold vecMulVec
    fun_prop
  unfold orthProj
  exact continuousAt_const.sub ((hd.continuousAt.inv₀ (star_dotProduct_self_ne_zero hu)).smul
    hv.continuousAt)

/-- Some unit vector `u` (for the sup norm) has `orthProj u` vanishing at `x`. -/
theorem exists_mem_sphere_orthProj_mulVec_eq_zero [Nonempty α] (x : α → ℂ) :
    ∃ u ∈ Metric.sphere (0 : α → ℂ) 1, orthProj u *ᵥ x = 0 := by
  obtain ⟨y, hy, hxy⟩ : ∃ y : α → ℂ, y ≠ 0 ∧ ∃ c : ℂ, x = c • y := by
    by_cases hx : x = 0
    · refine ⟨fun _ => 1, fun h => ?_, 0, by simp [hx]⟩
      simpa using congrFun h (Classical.arbitrary α)
    · exact ⟨x, hx, 1, (one_smul ℂ x).symm⟩
  refine ⟨((‖y‖ : ℂ)⁻¹) • y, by simpa using norm_smul_inv_norm (𝕜 := ℂ) hy, ?_⟩
  obtain ⟨c, rfl⟩ := hxy
  rw [orthProj_mulVec_eq_zero_iff]
  have hy' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
  exact ⟨c * ‖y‖, by rw [smul_smul, mul_assoc, mul_inv_cancel₀ hy', mul_one]⟩

end OrthProj

section Kernel

/-- Over a field, `ker P ⊆ ker P'` lets `P'` factor as `G * P`. -/
theorem exists_mul_eq_of_ker [Fintype α] [Fintype α'] {P : Matrix α' α ℂ}
    {P' : Matrix α'' α ℂ} (h : ∀ v, P *ᵥ v = 0 → P' *ᵥ v = 0) :
    ∃ G : Matrix α'' α' ℂ, G * P = P' := by
  classical
  set f := Matrix.toLin' P
  set f' := Matrix.toLin' P'
  have hker : LinearMap.ker f ≤ LinearMap.ker f' := fun v hv => h v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((LinearMap.ker f).liftQ f' hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  have := congrArg (fun φ => φ ⟨f v, LinearMap.mem_range_self f v⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [LinearMap.comp_apply, this, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable [Fintype α] [Fintype β] [Fintype γ]

theorem borderRankLE_map_of_ker [Fintype α'] [Fintype β'] [Fintype γ']
    {P : Matrix α' α ℂ} {P' : Matrix α'' α ℂ} (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)
    {T : Tensor3 α β γ} {ρ : ℕ} (h : (map P Y Z T).BorderRankLE ρ)
    (hker : ∀ v, P *ᵥ v = 0 → P' *ᵥ v = 0) : (map P' Y Z T).BorderRankLE ρ := by
  classical
  obtain ⟨G, rfl⟩ := exists_mul_eq_of_ker hker
  have := h.map G (1 : Matrix β' β' ℂ) (1 : Matrix γ' γ' ℂ)
  rwa [map_map, Matrix.one_mul, Matrix.one_mul] at this

variable [DecidableEq β] [DecidableEq γ]

theorem continuous_map_left :
    Continuous fun p : Matrix α' α ℂ × Tensor3 α β γ =>
      map p.1 (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) p.2 := by
  unfold map
  fun_prop

theorem continuous_map_left_const (T : Tensor3 α β γ) :
    Continuous fun X : Matrix α' α ℂ => map X (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T := by
  unfold map
  fun_prop

end Kernel

section Restrict

variable [DecidableEq α]

theorem restrictSlices_restrictSlices (T : Tensor3 α β γ) (S S' : Finset α) :
    (T.restrictSlices S).restrictSlices S' = T.restrictSlices (S' ∩ S) := by
  funext i j k
  simp only [restrictSlices, Finset.mem_inter]
  split_ifs <;> simp_all

theorem restrictSlices_univ [Fintype α] (T : Tensor3 α β γ) : T.restrictSlices univ = T := by
  funext i j k
  simp [restrictSlices]

theorem restrictSlices_empty (T : Tensor3 α β γ) : T.restrictSlices ∅ = 0 := by
  funext i j k
  simp [restrictSlices]

theorem zero_restrictSlices (S : Finset α) : (0 : Tensor3 α β γ).restrictSlices S = 0 := by
  funext i j k
  simp [restrictSlices]

theorem restrictSlices_eq_map [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] (T : Tensor3 α β γ) (S : Finset α) :
    T.restrictSlices S =
      map (diagonal fun i => if i ∈ S then 1 else 0) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T := by
  rw [← diagonal_one, ← diagonal_one, map_diagonal]
  funext i j k
  simp [restrictSlices]

theorem tight_restrictSlices {T : Tensor3 α β γ} (hT : T.Tight) (S : Finset α) :
    (T.restrictSlices S).Tight := by
  obtain ⟨τA, τB, τC, hinj, h⟩ := hT
  refine ⟨τA, τB, τC, hinj, fun i j k hijk => h i j k ?_⟩
  simp only [Tensor3.restrictSlices] at hijk
  split_ifs at hijk
  · exact hijk
  · exact absurd rfl hijk

theorem borderRankLE_restrictSlices_of_subset [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {T : Tensor3 α β γ} {S S' : Finset α} {ρ : ℕ}
    (h : (T.restrictSlices S).BorderRankLE ρ) (hS : S' ⊆ S) :
    (T.restrictSlices S').BorderRankLE ρ := by
  have := h.map (diagonal fun i => if i ∈ S' then 1 else 0) (1 : Matrix β β ℂ)
    (1 : Matrix γ γ ℂ)
  rwa [← restrictSlices_eq_map, restrictSlices_restrictSlices,
    Finset.inter_eq_left.mpr hS] at this

theorem borderRankLE_restrictSlices [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    [DecidableEq γ] {T : Tensor3 α β γ} {ρ : ℕ} (h : T.BorderRankLE ρ) (S : Finset α) :
    (T.restrictSlices S).BorderRankLE ρ := by
  rw [restrictSlices_eq_map]
  exact h.map _ _ _

end Restrict

theorem borderRankLE_zero_tensor (r : ℕ) : (0 : Tensor3 α β γ).BorderRankLE r :=
  (borderRankLE_zero_iff.mpr rfl).mono (Nat.zero_le r)

section Substitution

variable [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

/-- A tensor of rank at most `r + 1` has rank at most `r` after projecting the first factor
along a suitable unit vector. -/
theorem exists_mem_sphere_rankLE_map_orthProj [Nonempty α] {S : Tensor3 α β γ} {r : ℕ}
    (h : S.RankLE (r + 1)) :
    ∃ u ∈ Metric.sphere (0 : α → ℂ) 1,
      (map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) S).RankLE r := by
  obtain ⟨u, v, w, rfl⟩ := h
  obtain ⟨û, hû, h0⟩ := exists_mem_sphere_orthProj_mulVec_eq_zero (u 0)
  refine ⟨û, hû, fun s => orthProj û *ᵥ u (Fin.succAbove 0 s), fun s => v (Fin.succAbove 0 s),
    fun s => w (Fin.succAbove 0 s), ?_⟩
  have hz : outer (0 : α → ℂ) (v 0) (w 0) = 0 := by
    funext i j k
    simp [outer]
  rw [Tensor3.map_sum, Fin.sum_univ_succAbove _ 0]
  simp only [Tensor3.map_outer, one_mulVec, h0, hz, zero_add]

theorem exists_borderRankLE_map_orthProj [Nonempty α] {T : Tensor3 α β γ} {r : ℕ}
    (h : T.BorderRankLE (r + 1)) :
    ∃ u : α → ℂ, u ≠ 0 ∧
      (map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE r := by
  obtain ⟨Tn, hTn, hlim⟩ := mem_closure_iff_seq_limit.mp h
  choose û hû hrank using fun n => exists_mem_sphere_rankLE_map_orthProj (hTn n)
  obtain ⟨u₀, hu₀, φ, hφ, hconv⟩ := (isCompact_sphere (0 : α → ℂ) 1).tendsto_subseq hû
  have hne : u₀ ≠ 0 := by
    rintro rfl
    simp at hu₀
  refine ⟨u₀, hne, mem_closure_of_tendsto (b := atTop)
    (f := fun n => map (orthProj (û (φ n))) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) (Tn (φ n)))
    ?_ (Eventually.of_forall fun n => hrank (φ n))⟩
  have hP : Tendsto (fun n => orthProj (û (φ n))) atTop (𝓝 (orthProj u₀)) :=
    (continuousAt_orthProj hne).tendsto.comp hconv
  have hT : Tendsto (fun n => Tn (φ n)) atTop (𝓝 T) := hlim.comp hφ.tendsto_atTop
  have hc : Tendsto (fun p : Matrix α α ℂ × Tensor3 α β γ =>
      map p.1 (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) p.2) (𝓝 (orthProj u₀, T))
      (𝓝 (map (orthProj u₀) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T)) :=
    continuous_map_left.tendsto' _ _ rfl
  exact (hc.comp (hP.prodMk_nhds hT)).congr fun n => rfl

/-- The diagonal matrix `diag(t ^ τ i)`: the one-parameter subgroup with weights `τ`. -/
noncomputable def torus {ι : Type*} [DecidableEq ι] (τ : ι → ℤ) (t : ℂ) : Matrix ι ι ℂ :=
  diagonal fun i => t ^ τ i

omit [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] in
theorem torus_mul_torus_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℤ) {t : ℂ}
    (ht : t ≠ 0) : torus τ t * torus τ t⁻¹ = 1 := by
  rw [torus, torus, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [inv_zpow', ← zpow_add₀ ht, add_neg_cancel, zpow_zero]

theorem map_torus {T : Tensor3 α β γ} {τA : α → ℤ} {τB : β → ℤ} {τC : γ → ℤ}
    (hT : ∀ i j k, T i j k ≠ 0 → τA i + τB j + τC k = 0) {t : ℂ} (ht : t ≠ 0) :
    map (torus τA t) (torus τB t) (torus τC t) T = T := by
  rw [torus, torus, torus, map_diagonal]
  funext i j k
  by_cases h : T i j k = 0
  · simp [h]
  · rw [← zpow_add₀ ht, ← zpow_add₀ ht, hT i j k h, zpow_zero, one_mul]

/-- The torus fixing `T` moves the projection direction `u` to `torus τA t *ᵥ u` without
changing the border-rank bound. -/
theorem borderRankLE_map_orthProj_torus {T : Tensor3 α β γ} {τA : α → ℤ} {τB : β → ℤ}
    {τC : γ → ℤ} (hT : ∀ i j k, T i j k ≠ 0 → τA i + τB j + τC k = 0) {t : ℂ} (ht : t ≠ 0)
    {u : α → ℂ} {ρ : ℕ}
    (h : (map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE ρ) :
    (map (orthProj (torus τA t *ᵥ u)) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE
      ρ := by
  have h' := h.map (1 : Matrix α α ℂ) (torus τB t) (torus τC t)
  rw [← map_torus hT (inv_ne_zero ht), map_map, map_map] at h'
  simp only [Matrix.one_mul, Matrix.mul_one] at h'
  rw [torus_mul_torus_inv τB ht, torus_mul_torus_inv τC ht] at h'
  refine borderRankLE_map_of_ker _ _ h' fun v hv => ?_
  rw [← mulVec_mulVec, orthProj_mulVec_eq_zero_iff] at hv
  obtain ⟨c, hc⟩ := hv
  have hv : v = c • (torus τA t *ᵥ u) := by
    rw [← mulVec_smul, ← hc, mulVec_mulVec, torus_mul_torus_inv τA ht, one_mulVec]
  rw [hv, mulVec_smul, orthProj_mulVec_self, smul_zero]

theorem exists_borderRankLE_restrictSlices_erase_of_tight {T : Tensor3 α β γ} (hT : T.Tight)
    {u : α → ℂ} (hu : u ≠ 0) {ρ : ℕ}
    (h : (map (orthProj u) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE ρ) :
    ∃ i, u i ≠ 0 ∧ (T.restrictSlices (univ.erase i)).BorderRankLE ρ := by
  obtain ⟨τA, τB, τC, hinj, hsupp⟩ := hT
  obtain ⟨i₀, hi₀, hmin⟩ := (univ.filter fun i => u i ≠ 0).exists_min_image τA
    (by obtain ⟨i, hi⟩ := Function.ne_iff.mp hu; exact ⟨i, by simpa using hi⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hmin
  set σ : α → ℤ := fun i => τA i - τA i₀ with hσ
  have hsupp' : ∀ i j k, T i j k ≠ 0 → σ i + τB j + (fun k => τC k + τA i₀) k = 0 :=
    fun i j k hijk => by
      have := hsupp i j k hijk
      simp only [hσ]
      omega
  set t : ℕ → ℂ := fun n => (2⁻¹ : ℂ) ^ n with ht
  have ht0 : ∀ n, t n ≠ 0 := fun n => pow_ne_zero _ (by norm_num)
  have htlim : Tendsto t atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  set v : α → ℂ := Pi.single i₀ (u i₀) with hv
  have hv0 : v ≠ 0 := fun h0 => hi₀ (by simpa [hv] using congrFun h0 i₀)
  have hvlim : Tendsto (fun n => torus σ (t n) *ᵥ u) atTop (𝓝 v) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    simp only [torus, mulVec_diagonal]
    by_cases hui : u i = 0
    · have hii : i ≠ i₀ := fun h => hi₀ (h ▸ hui)
      simp [hui, hv, hii]
    · by_cases hii : i = i₀
      · subst hii
        simp [hσ, hv]
      · have hlt : τA i₀ < τA i := lt_of_le_of_ne (hmin i hui) (hinj.ne (Ne.symm hii))
        have hσi : σ i = τA i - τA i₀ := rfl
        obtain ⟨m, hm⟩ : ∃ m : ℕ, σ i = ((m + 1 : ℕ) : ℤ) := ⟨(σ i).toNat - 1, by omega⟩
        rw [show v i = 0 by simp [hv, hii], hm]
        simp_rw [zpow_natCast]
        simpa using (htlim.pow (m + 1)).mul_const (u i)
  have hmem : ∀ n, (map (orthProj (torus σ (t n) *ᵥ u)) (1 : Matrix β β ℂ)
      (1 : Matrix γ γ ℂ) T).BorderRankLE ρ := fun n =>
    borderRankLE_map_orthProj_torus hsupp' (ht0 n) h
  have hlim : (map (orthProj v) (1 : Matrix β β ℂ) (1 : Matrix γ γ ℂ) T).BorderRankLE ρ := by
    have hP := (continuousAt_orthProj hv0).tendsto.comp hvlim
    have hc := ((continuous_map_left_const (α' := α) T).tendsto (orthProj v)).comp hP
    exact (isClosed_setOf_borderRankLE ρ).mem_of_tendsto (hc.congr fun n => rfl)
      (Eventually.of_forall hmem)
  refine ⟨i₀, hi₀, ?_⟩
  rw [restrictSlices_eq_map]
  refine borderRankLE_map_of_ker _ _ hlim fun w hw => ?_
  obtain ⟨c, rfl⟩ := orthProj_mulVec_eq_zero_iff.mp hw
  rw [mulVec_smul]
  funext i
  by_cases hii : i = i₀
  · subst hii
    simp [mulVec_diagonal]
  · simp [hv]

end Substitution

section Deletion

variable [Fintype α] [DecidableEq α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem exists_mem_borderRankLE_restrictSlices_erase {T : Tensor3 α β γ} (hT : T.Tight)
    {S : Finset α} (hS : S.Nonempty) {r : ℕ}
    (h : (T.restrictSlices S).BorderRankLE (r + 1)) :
    ∃ i ∈ S, (T.restrictSlices (S.erase i)).BorderRankLE r := by
  have : Nonempty α := ⟨hS.choose⟩
  obtain ⟨u, hu, hA⟩ := exists_borderRankLE_map_orthProj h
  obtain ⟨i, -, hC⟩ :=
    exists_borderRankLE_restrictSlices_erase_of_tight (tight_restrictSlices hT S) hu hA
  rw [restrictSlices_restrictSlices] at hC
  by_cases hi : i ∈ S
  · refine ⟨i, hi, borderRankLE_restrictSlices_of_subset hC fun x hx => ?_⟩
    simp only [Finset.mem_erase] at hx
    simp [hx.1, hx.2]
  · obtain ⟨j, hj⟩ := hS
    refine ⟨j, hj, borderRankLE_restrictSlices_of_subset hC fun x hx => ?_⟩
    simp only [Finset.mem_erase] at hx
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hi (h ▸ hx.2), hx.2⟩

theorem exists_list_borderRankLE_restrictSlices_sdiff {T : Tensor3 α β γ} (hT : T.Tight)
    (S₀ : Finset α) {r : ℕ} (h : (T.restrictSlices S₀).BorderRankLE r) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = S₀ ∧
      ∀ q, (T.restrictSlices (S₀ \ (l.take q).toFinset)).BorderRankLE (r - q) := by
  induction hn : S₀.card generalizing S₀ r with
  | zero =>
    obtain rfl := Finset.card_eq_zero.mp hn
    refine ⟨[], List.nodup_nil, rfl, fun q => ?_⟩
    simpa [restrictSlices_empty] using borderRankLE_zero_tensor (α := α) (β := β) (γ := γ) _
  | succ n ih =>
    have hne : S₀.Nonempty := Finset.card_pos.mp (by omega)
    cases r with
    | zero =>
      have h0 := borderRankLE_zero_iff.mp h
      refine ⟨S₀.toList, S₀.nodup_toList, S₀.toList_toFinset, fun q => ?_⟩
      have : T.restrictSlices (S₀ \ (S₀.toList.take q).toFinset) = 0 := by
        rw [← Finset.inter_eq_left.mpr (Finset.sdiff_subset (s := S₀)
          (t := (S₀.toList.take q).toFinset)), ← restrictSlices_restrictSlices, h0,
          zero_restrictSlices]
      rw [this]
      exact borderRankLE_zero_tensor _
    | succ r =>
      obtain ⟨i, hi, hr⟩ := exists_mem_borderRankLE_restrictSlices_erase hT hne h
      obtain ⟨l, hl, hlS, hq⟩ := ih (S₀.erase i) hr (by rw [Finset.card_erase_of_mem hi]; omega)
      have hil : i ∉ l := fun h => by
        have := congrArg (i ∈ ·) hlS
        simp [List.mem_toFinset, h] at this
      refine ⟨i :: l, List.nodup_cons.mpr ⟨hil, hl⟩, ?_, fun q => ?_⟩
      · rw [List.toFinset_cons, hlS, Finset.insert_erase hi]
      · cases q with
        | zero => simpa using h
        | succ q =>
          have := hq q
          rw [List.take_succ_cons, List.toFinset_cons, Finset.sdiff_insert,
            ← Finset.erase_sdiff_comm]
          simpa using this

theorem card_le_of_borderRankLE_restrictSlices {T : Tensor3 α β γ} (hT : T.Tight)
    {S : Finset α} (hS : ∀ i ∈ S, T i ≠ 0) {r : ℕ}
    (h : (T.restrictSlices S).BorderRankLE r) : S.card ≤ r := by
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  obtain ⟨l, hl, hlS, hq⟩ := exists_list_borderRankLE_restrictSlices_sdiff hT S h
  have h0 := borderRankLE_zero_iff.mp (by simpa using hq r)
  have hcard : ((l.take r).toFinset).card < S.card := by
    calc ((l.take r).toFinset).card ≤ (l.take r).length := List.toFinset_card_le _
      _ ≤ r := by simp
      _ < S.card := hlt
  obtain ⟨i, hi⟩ : (S \ (l.take r).toFinset).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff (l.take r).toFinset S
    omega
  apply hS i (Finset.mem_sdiff.mp hi).1
  funext j k
  have := congrFun (congrFun (congrFun h0 i) j) k
  simpa [Tensor3.restrictSlices, hi] using this

theorem exists_list_add_borderRank_le {T : Tensor3 α β γ} (hT : T.Tight) {S₀ : Finset α}
    (hS : ∀ i ∈ S₀, T i ≠ 0) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = S₀ ∧ ∀ q ≤ S₀.card,
      q + (T.restrictSlices (S₀ \ (l.take q).toFinset)).borderRank ≤
        (T.restrictSlices S₀).borderRank := by
  have hr := borderRankLE_borderRank (T.restrictSlices S₀)
  have hcard := card_le_of_borderRankLE_restrictSlices hT hS hr
  obtain ⟨l, hl, hlS, hq⟩ := exists_list_borderRankLE_restrictSlices_sdiff hT S₀ hr
  refine ⟨l, hl, hlS, fun q hq' => ?_⟩
  have := borderRank_le_iff.mpr (hq q)
  omega

theorem not_borderRankLE_restrictSlices_of_forall_list {T : Tensor3 α β γ} (hT : T.Tight)
    {S₀ : Finset α} (hS : ∀ i ∈ S₀, T i ≠ 0) {r : ℕ} (LB : Finset α → ℕ)
    (hLB : ∀ S ⊆ S₀, ∀ ρ, (T.restrictSlices S).BorderRankLE ρ → LB S ≤ ρ)
    (h : ∀ l : List α, l.Nodup → l.toFinset = S₀ →
      ∃ q ≤ S₀.card, r < q + LB (S₀ \ (l.take q).toFinset)) :
    ¬ (T.restrictSlices S₀).BorderRankLE r := by
  intro hr
  have hcard := card_le_of_borderRankLE_restrictSlices hT hS hr
  obtain ⟨l, hl, hlS, hq⟩ := exists_list_borderRankLE_restrictSlices_sdiff hT S₀ hr
  obtain ⟨q, hq₀, hlt⟩ := h l hl hlS
  have := hLB _ Finset.sdiff_subset _ (hq q)
  omega

end Deletion

end Algebraic.Tensor3.Internal

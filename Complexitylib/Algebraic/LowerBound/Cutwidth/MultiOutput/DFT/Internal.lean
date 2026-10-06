/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.DFT.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular.Internal
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Proofs for Vandermonde and Fourier transform matrices

Let `M = (x c ^ r)` be the transposed Vandermonde matrix of distinct nodes `x c`, with rows `r`
and columns `c` in `0, …, N - 1`; the Fourier matrix `dft ω N` is the case `x c = ω ^ c` for a
primitive `N`-th root of unity `ω`.

* *Prefix rows are independent* (`card_filter_lt_le_blockRank`): on a set `C` of columns, the
  rows `r < |C|` are linearly independent, since a combination `∑ g r x ^ r` of them vanishing
  at the `|C|` distinct nodes `x c` is a polynomial of degree below `|C|` with `|C|` roots. So
  every block `M[Y, C]` has rank at least the number of rows `r ∈ Y` with `r < |C|`.
* *Half cuts* (`le_blockRank_add_blockRank`): for a set `X` of `h ≤ N/2` columns and any set
  `Y` of rows, `rank M[Yᶜ, X] + rank M[Y, Xᶜ] ≥ h`. The first block has rank at least the
  number of rows `r < h` outside `Y`, and the second, as `|Xᶜ| = N - h ≥ h`, at least the
  number of rows `r < h` in `Y`.
* *The layout bound* (`half_le_of_rank_cuts`): if some row of `M` has no zero entry and every
  split with `h` inputs on one side satisfies the half-cut bound, a fan-in-two program carrying
  `M` and obeying the rank-cut inequality has `h ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`.
  The component of the output wire of the nonzero row is closed, so the rank-cut inequality
  puts every input into it. Along the ranking of `MultiOutput.exists_rank`, the number of
  inputs in a prefix grows by at most one per wire, so the prefix ending at some input holds
  exactly `h` inputs; it is crossed by at least `h` signals and charged to the component holding
  all inputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Matrix Filter Module Polynomial

/-! ## Vandermonde matrices -/

section Vandermonde

variable {F : Type*} [Field F] {N : ℕ}

/-- **Prefix rows of a Vandermonde matrix are independent.** For distinct nodes `x c`, every
block of `(x c ^ r)` with rows `Y` and columns `C` has rank at least the number of rows
`r ∈ Y` with `r < |C|`. -/
theorem card_filter_lt_le_blockRank {x : Fin N → F} (hx : Function.Injective x)
    (Y C : Finset (Fin N)) :
    (Y.filter fun r : Fin N => (r : ℕ) < C.card).card ≤ blockRank (vandermonde x)ᵀ Y C := by
  classical
  set Z := Y.filter fun r : Fin N => (r : ℕ) < C.card with hZ
  set B := (vandermonde x)ᵀ.submatrix (fun i : ↥Y => (i : Fin N)) (fun j : ↥C => (j : Fin N))
    with hB
  let ι : ↥Z → ↥Y := fun z => ⟨z.1, (Finset.mem_filter.1 z.2).1⟩
  have hlt : ∀ z : ↥Z, (z.1 : ℕ) < C.card := fun z => (Finset.mem_filter.1 z.2).2
  have hli : LinearIndependent F (fun z : ↥Z => B.row (ι z)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    set P : F[X] := ∑ z : ↥Z, Polynomial.C (g z) * X ^ (z.1 : ℕ) with hP
    have hcoeff : ∀ k : ℕ, P.coeff k = ∑ z : ↥Z, if k = (z.1 : ℕ) then g z else 0 := by
      intro k
      rw [hP, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
    have hdeg : P.degree < (C.image x).card := by
      rw [Finset.card_image_of_injective _ hx, Polynomial.degree_lt_iff_coeff_zero]
      intro k hk
      rw [hcoeff]
      refine Finset.sum_eq_zero fun z _ => ?_
      have := hlt z
      exact ite_eq_right (by omega)
    have heval : ∀ y ∈ C.image x, P.eval y = 0 := by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
      have := congrFun hg ⟨c, hc⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hB, ι,
        Matrix.row, Matrix.submatrix_apply, Matrix.transpose_apply, vandermonde_apply] at this
      rw [hP, Polynomial.eval_finsetSum]
      simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X] using this
    have hP0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero _ hdeg heval
    intro z
    have := hcoeff z.1
    rw [hP0, Polynomial.coeff_zero, Finset.sum_eq_single z (fun z' _ hz' => ite_eq_right fun h =>
      hz' (Subtype.ext (Fin.ext h.symm))) (by simp), ite_eq_left rfl] at this
    exact this.symm
  rw [blockRank, Matrix.rank_eq_finrank_span_row]
  calc Z.card = Fintype.card ↥Z := (Fintype.card_coe Z).symm
    _ = finrank F (Submodule.span F (Set.range fun z : ↥Z => B.row (ι z))) :=
        (finrank_span_eq_card hli).symm
    _ ≤ finrank F (Submodule.span F (Set.range B.row)) :=
        Submodule.finrank_mono (Submodule.span_mono (by
          rintro _ ⟨z, rfl⟩
          exact ⟨ι z, rfl⟩))

/-- The first `h ≤ N` indices number `h`. -/
theorem card_filter_val_lt_eq {h : ℕ} (hh : h ≤ N) :
    (Finset.univ.filter fun r : Fin N => (r : ℕ) < h).card = h := by
  have : (Finset.univ.filter fun r : Fin N => (r : ℕ) < h) =
      (Finset.range h).attachFin fun j hj => by
        rw [Finset.mem_range] at hj
        omega := by
    ext j
    simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- **Half cuts of a Vandermonde matrix.** For distinct nodes, a set `X` of `h` columns with
`2 h ≤ N`, and any set `Y` of rows, `h ≤ rank M[Yᶜ, X] + rank M[Y, Xᶜ]`. -/
theorem le_blockRank_add_blockRank {x : Fin N → F} (hx : Function.Injective x) {h : ℕ}
    (hh : 2 * h ≤ N) (Y X : Finset (Fin N)) (hX : X.card = h) :
    h ≤ blockRank (vandermonde x)ᵀ Yᶜ X + blockRank (vandermonde x)ᵀ Y Xᶜ := by
  have h₁ := card_filter_lt_le_blockRank hx Yᶜ X
  have h₂ := card_filter_lt_le_blockRank hx Y Xᶜ
  have hXc : Xᶜ.card = N - h := by rw [Finset.card_compl, Fintype.card_fin, hX]
  rw [hX] at h₁
  rw [hXc] at h₂
  set R := Finset.univ.filter fun r : Fin N => (r : ℕ) < h with hR
  have hRcard : R.card = h := card_filter_val_lt_eq (by omega)
  have hsplit : (R.filter fun r => r ∈ Y).card + (R.filter fun r => r ∉ Y).card = h :=
    hRcard ▸ Finset.card_filter_add_card_filter_not _
  have e₁ : (R.filter fun r => r ∉ Y) = Yᶜ.filter fun r : Fin N => (r : ℕ) < h := by
    ext r
    simp [R, and_comm]
  have e₂ : (R.filter fun r => r ∈ Y).card ≤ (Y.filter fun r : Fin N => (r : ℕ) < N - h).card := by
    refine Finset.card_le_card fun r hr => ?_
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact ⟨hr.2, by omega⟩
  rw [e₁] at hsplit
  omega

/-- A block with a nonzero entry has rank at least one. -/
theorem one_le_blockRank_of_ne_zero {m n : ℕ} {M : Matrix (Fin m) (Fin n) F}
    {Y : Finset (Fin m)} {X : Finset (Fin n)} {i : Fin m} {j : Fin n} (hi : i ∈ Y) (hj : j ∈ X)
    (hij : M i j ≠ 0) : 1 ≤ blockRank M Y X := by
  have hdet : ((M.submatrix (fun i : ↥Y => (i : Fin m)) (fun j : ↥X => (j : Fin n))).submatrix
      (fun _ : Fin 1 => (⟨i, hi⟩ : ↥Y)) (fun _ : Fin 1 => (⟨j, hj⟩ : ↥X))).det ≠ 0 := by
    rw [Matrix.det_unique]
    simpa using hij
  have hrank := Matrix.rank_of_det_ne_zero hdet
  rw [Fintype.card_fin] at hrank
  rw [← hrank]
  exact Matrix.rank_submatrix_le _ _ _

/-! ## The Fourier matrix -/

/-- The Fourier matrix is the transposed Vandermonde matrix of the powers of `ω`. -/
theorem dft_eq_transpose_vandermonde (ω : F) (N : ℕ) :
    dft ω N = (vandermonde fun c : Fin N => ω ^ (c : ℕ))ᵀ := by
  ext r c
  simp only [dft, Matrix.of_apply, Matrix.transpose_apply, vandermonde_apply, ← pow_mul,
    mul_comm]

/-- The powers `ω ^ c`, `c < N`, of a primitive `N`-th root of unity are distinct. -/
theorem injective_pow_of_isPrimitiveRoot {ω : F} (hω : IsPrimitiveRoot ω N) :
    Function.Injective fun c : Fin N => ω ^ (c : ℕ) :=
  fun a b hab => Fin.ext (hω.pow_inj a.2 b.2 hab)

/-- **Half cuts of the Fourier matrix.** For a primitive `N`-th root of unity `ω`, a set `X` of
`⌊N/2⌋` columns, and any set `Y` of rows, `⌊N/2⌋ ≤ rank F[Yᶜ, X] + rank F[Y, Xᶜ]`. -/
theorem le_blockRank_add_blockRank_dft {ω : F} (hω : IsPrimitiveRoot ω N)
    (Y X : Finset (Fin N)) (hX : X.card = N / 2) :
    N / 2 ≤ blockRank (dft ω N) Yᶜ X + blockRank (dft ω N) Y Xᶜ := by
  rw [dft_eq_transpose_vandermonde]
  exact le_blockRank_add_blockRank (injective_pow_of_isPrimitiveRoot hω) (by omega) Y X hX

/-- The first row of the Fourier matrix has no zero entry. -/
theorem dft_zero_ne_zero (ω : F) (hN : 0 < N) (j : Fin N) : dft ω N ⟨0, hN⟩ j ≠ 0 := by
  simp [dft]

end Vandermonde

/-! ## The layout bound -/

section Layout

variable {σ : Signature} {F : Type*} [Field F]

/-- **The layout bound for half cuts.** Let a fan-in-two program carry a matrix `M`, in the
sense that every split `S` satisfies the rank-cut inequality. If some row of `M` has no zero
entry, and every set `X` of `h ≤ N` columns satisfies `h ≤ rank M[Yᶜ, X] + rank M[Y, Xᶜ]` for
every set `Y` of rows, then `h ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`. -/
theorem half_le_of_rank_cuts {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {N s m : ℕ} (p : Program σ N s)
    (hp : p.FanInAtMost 2) (out : Fin m → Wire N s) {M : Matrix (Fin m) (Fin N) F} {h : ℕ}
    (hrow : 0 < h → ∃ i₀ : Fin m, ∀ j, M i₀ j ≠ 0)
    (hrank : ∀ (Y : Finset (Fin m)) (X : Finset (Fin N)), X.card = h →
      h ≤ blockRank M Yᶜ X + blockRank M Y Xᶜ)
    (hh : h ≤ N)
    (cuts : ∀ S : Finset (Wire N s),
      blockRank M (outputsIn out S)ᶜ (inputsIn S) +
        blockRank M (outputsIn out S) (inputsIn S)ᶜ ≤
          (forward p S).card + (backward p S).card) :
    (h : ℝ) ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C := by
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 ((N : ℝ) + 3 * s) := by
    rcases Nat.eq_zero_or_pos (N + 3 * s) with h | h
    · have : ((N : ℝ) + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - N) 0 := mul_nonneg hAη (le_max_right _ _)
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · rw [h0, Nat.cast_zero]
    linarith
  -- All inputs lie in the component of the output wire of a row without zero entries.
  obtain ⟨i₀, hi₀⟩ := hrow hpos
  set W := component p (out i₀) with hW
  have hclosed := component_closed p (out i₀)
  have hzero := cuts W
  rw [forward_eq_empty_of_closed hclosed, backward_eq_empty_of_closed hclosed] at hzero
  have hY : i₀ ∈ outputsIn out W := by
    simp [outputsIn, hW, mem_component_self]
  have hin : ∀ j, Wire.input j ∈ W := by
    intro j
    by_contra hj
    have hjX : j ∈ (inputsIn W)ᶜ := Finset.mem_compl.2 fun h' => hj (mem_inputsIn.1 h')
    have := one_le_blockRank_of_ne_zero hY hjX (hi₀ j)
    simp only [Finset.card_empty, add_zero] at hzero
    omega
  -- The ranking, and the prefix holding `h` inputs.
  obtain ⟨rank, hrank', hlt, hbound⟩ := exists_rank hAη order p hp
  let τ : ℕ → ℕ := fun t => (inputsIn (prefixBelow rank t)).card
  have hτ0 : τ 0 = 0 := by
    simp [τ, inputsIn, prefixBelow]
  have hτT : h ≤ τ (N + s) := by
    have hall : prefixBelow rank (N + s) = Finset.univ := by
      ext w
      simp [prefixBelow, hlt w]
    have huniv : inputsIn (Finset.univ : Finset (Wire N s)) = Finset.univ := by
      ext j
      simp [mem_inputsIn]
    show h ≤ (inputsIn (prefixBelow rank (N + s))).card
    rw [hall, huniv, Finset.card_univ, Fintype.card_fin]
    exact hh
  obtain ⟨t, hτt, hτt1⟩ := exists_cross τ hτ0 hpos (N + s) hτT
  have hstep := card_inputsIn_prefixBelow_succ_le rank hrank' t
  have hτeq : (inputsIn (prefixBelow rank (t + 1))).card = h := by
    simp only [τ] at hτt hτt1
    omega
  -- An input is ranked `t`.
  obtain ⟨j₀, hj₀⟩ : ∃ j, rank (Wire.input j) = t := by
    by_contra hnone
    push Not at hnone
    have hi : inputsIn (prefixBelow rank (t + 1)) = inputsIn (prefixBelow rank t) := by
      ext j
      simp only [mem_inputsIn, prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hnone j
      omega
    rw [hi] at hτeq
    simp only [τ] at hτt
    omega
  have hprefix : prefixBelow rank (t + 1) = prefixUpTo rank (Wire.input j₀) := by
    ext v
    simp only [prefixBelow, prefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  -- The lower bound at the prefix.
  set S := prefixBelow rank (t + 1) with hS
  have hlower : h ≤ (forward p S).card + (backward p S).card :=
    (hrank _ _ hτeq).trans (cuts S)
  -- The upper bound at the prefix, charged to the component holding all inputs.
  have hupper := hbound (Wire.input j₀)
  have hinputs : (inputsIn (component p (Wire.input j₀))).card = N := by
    have hcomp : component p (Wire.input j₀) = W := component_eq_of_mem (hin j₀)
    have : inputsIn W = Finset.univ := by
      ext j
      simp only [mem_inputsIn, Finset.mem_univ, iff_true]
      exact hin j
    rw [hcomp, this, Finset.card_univ, Fintype.card_fin]
  rw [← hprefix, hinputs] at hupper
  have hgates : ((gatesIn (component p (Wire.input j₀))).card : ℝ) ≤ s := by
    exact_mod_cast (by simpa using Finset.card_le_univ (gatesIn (component p (Wire.input j₀))))
  have hmax : (A + η) * max (((gatesIn (component p (Wire.input j₀))).card : ℝ) - N) 0 ≤
      (A + η) * max ((s : ℝ) - N) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hAη
  have hlowerR : (h : ℝ) ≤ (((forward p S).card + (backward p S).card : ℕ) : ℝ) := by
    exact_mod_cast hlower
  linarith

/-- **The layout bound for the Fourier matrix.** A fan-in-two program carrying `dft ω N`, for
a primitive `N`-th root of unity `ω`, and obeying the rank-cut inequality has
`⌊N/2⌋ ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`. -/
theorem half_le_of_dft {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    {N s : ℕ} (p : Program σ N s) (hp : p.FanInAtMost 2) (out : Fin N → Wire N s) {ω : F}
    (hω : IsPrimitiveRoot ω N)
    (cuts : ∀ S : Finset (Wire N s),
      blockRank (dft ω N) (outputsIn out S)ᶜ (inputsIn S) +
        blockRank (dft ω N) (outputsIn out S) (inputsIn S)ᶜ ≤
          (forward p S).card + (backward p S).card) :
    ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C :=
  half_le_of_rank_cuts hAη order p hp out
    (fun hpos => ⟨⟨0, by omega⟩, dft_zero_ne_zero ω (by omega)⟩)
    (fun Y X hX => le_blockRank_add_blockRank_dft hω Y X hX) (Nat.div_le_self N 2) cuts

end Layout

/-! ## Asymptotics -/

/-- **The numeric transfer for half cuts.** For `A > 0` and `ε > 0` there are a slack `η` and a
constant `C` with `OrderingBound A η C` such that, for all large `N`, every `s` with
`⌊N/2⌋ ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C` exceeds `(1 + 1/(2A) - ε) N`. -/
theorem exists_eventually_lt_of_half_le {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∃ η C : ℝ, 0 ≤ A + η ∧ Multigraph.OrderingBound A η C ∧ ∀ᶠ N : ℕ in atTop, ∀ s : ℕ,
      ((N / 2 : ℕ) : ℝ) ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C →
        (1 + 1 / (2 * A) - ε) * N < s := by
  set ε' := min ε (1 / (2 * A)) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 1 / (2 * A) := min_le_right _ _
  set η := A ^ 2 * ε' with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  refine ⟨η, C, hAη, hC, ?_⟩
  set B : ℝ := 4 + 3 / (2 * A) with hB
  have hBpos : 0 < B := by positivity
  filter_upwards [eventually_mul_logb_add_lt 3 (3 * Real.logb 2 B + C + 1)
    (show 0 < A * ε' / 2 by positivity), eventually_ge_atTop 1] with N hlog hN1
  intro s core
  by_contra hs
  rw [not_lt] at hs
  have hs' : (s : ℝ) ≤ (1 + 1 / (2 * A) - ε') * N :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hhalf : ((N : ℝ) - 1) / 2 ≤ ((N / 2 : ℕ) : ℝ) := by
    have h₁ : N ≤ 2 * (N / 2) + 1 := by omega
    have h₂ : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h₁
    linarith
  have hrest : 0 ≤ (1 / (2 * A) - ε') * N := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((s : ℝ) - N) 0 ≤ (1 / (2 * A) - ε') * N :=
    max_le (by linarith) hrest
  have hcoef : (A + η) * (1 / (2 * A) - ε') ≤ 1 / 2 - A * ε' / 2 := by
    have h₁ : (A + η) * (1 / (2 * A) - ε') = 1 / 2 - A * ε' + η / (2 * A) - η * ε' := by
      field_simp
      ring
    have h₂ : η / (2 * A) = A * ε' / 2 := by
      rw [hη]
      field_simp
    have h₃ : 0 ≤ η * ε' := by positivity
    linarith
  have hprod : (A + η) * max ((s : ℝ) - N) 0 ≤ (1 / 2 - A * ε' / 2) * N := by
    calc (A + η) * max ((s : ℝ) - N) 0 ≤ (A + η) * ((1 / (2 * A) - ε') * N) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (1 / (2 * A) - ε') * N := by ring
      _ ≤ (1 / 2 - A * ε' / 2) * N := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hVle : (N : ℝ) + 3 * s ≤ B * N := by
    have h₁ : (1 + 1 / (2 * A) - ε') * (N : ℝ) ≤ (1 + 1 / (2 * A)) * N :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (N : ℝ) = N + 3 * ((1 + 1 / (2 * A)) * N) := by
      rw [hB]
      ring
    linarith
  have hVpos : (0 : ℝ) < N + 3 * s := by positivity
  have hlogV : Real.logb 2 ((N : ℝ) + 3 * s) ≤ Real.logb 2 B + Real.logb 2 N := by
    calc Real.logb 2 ((N : ℝ) + 3 * s) ≤ Real.logb 2 (B * N) :=
          (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVle
      _ = Real.logb 2 B + Real.logb 2 N := Real.logb_mul hBpos.ne' (by positivity)
  have hsplit : (1 / 2 - A * ε' / 2) * (N : ℝ) = N / 2 - A * ε' / 2 * N := by ring
  linarith

universe u v

/-- **The asymptotic bound for the Fourier matrix** under the rank-cut inequality, uniformly
over fields, signatures and roots of unity. -/
theorem eventually_lt_size_of_dft_rank_cuts {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] (ω : F), IsPrimitiveRoot ω N →
      ∀ (σ : Signature.{v}) (c : Circuit σ N N), c.FanInAtMost 2 →
        (∀ S : Finset (Wire N c.size),
          blockRank (dft ω N) (outputsIn c.outputs S)ᶜ (inputsIn S) +
            blockRank (dft ω N) (outputsIn c.outputs S) (inputsIn S)ᶜ ≤
              (forward c.program S).card + (backward c.program S).card) →
          (1 + 1 / (2 * A) - ε) * N < c.size := by
  obtain ⟨η, C, hAη, hC, hev⟩ := exists_eventually_lt_of_half_le hA order hε
  filter_upwards [hev] with N hN
  intro F _ ω hω σ c hfan cuts
  exact hN c.size (half_le_of_dft hAη hC c.program hfan c.outputs hω cuts)

end Algebraic.Cutwidth.MultiOutput.Internal

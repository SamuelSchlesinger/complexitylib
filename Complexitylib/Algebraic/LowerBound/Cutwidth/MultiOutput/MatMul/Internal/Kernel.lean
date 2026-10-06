/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Rank.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular.Internal
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Kernels of matrix blocks

Write `ker(M; P, Q)` for `supportedKernel (M *ᵥ ·) P Q`, the vectors supported on the columns
`P` whose image under `M` vanishes on the rows `Q`: the kernel of the block `M[Q, P]`.

* **Totally regular matrices** (`card_supportedKernel_mul_pow_le`). The block has rank at least
  `min (|P|, |Q|)`, so `|ker(M; P, Q)| · |F| ^ min (|P|, |Q|) ≤ |F| ^ |P|`.
* **Uniform matrices** (`sum_card_supportedKernel_mul_pow_le`). Summed over all square matrices
  `M`, the kernels satisfy `(∑ |ker(M; P, Q)|) · |F| ^ min (|P|, |Q|) ≤ 2 |F| ^ (n²) |F| ^ |P|`:
  a nonzero vector `d` lies in the kernel for at most an `|F| ^ -|Q|` fraction of the matrices,
  since each row of `Q` must be orthogonal to `d` (`card_filter_dotProduct_mul_le`).
* **Averaging** (`exists_prod_le_pow`). If quantities `K t x ≥ 1` average at most `2 q ^ (e t)`
  over `x`, some `x` makes `∏ t, K t x ≤ q ^ (∑ t, e t + 2 |T|)`: the excess exponent
  `log_q (K t x) + 1 - e t` is at most `K t x / q ^ (e t)`, so it averages at most `2`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.Internal

open Algebraic.Cutwidth.MultiOutput.Internal

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- Transposes of totally regular matrices are totally regular. -/
theorem totallyRegular_transpose {m n : Nat} {M : Matrix (Fin m) (Fin n) F}
    (hM : TotallyRegular M) : TotallyRegular Mᵀ := by
  intro k r c hr hc
  have : Mᵀ.submatrix r c = (M.submatrix c r)ᵀ := by
    ext
    rfl
  rw [this, Matrix.det_transpose]
  exact hM k c r hc hr

/-- Kernels contain the zero vector. -/
theorem zero_mem_supportedKernel {n m : Nat} (M : Matrix (Fin m) (Fin n) F) (P : Finset (Fin n))
    (Q : Finset (Fin m)) : (0 : Fin n → F) ∈ supportedKernel (fun d => M *ᵥ d) P Q := by
  simp [supportedKernel]

theorem card_supportedKernel_pos {n m : Nat} (M : Matrix (Fin m) (Fin n) F)
    (P : Finset (Fin n)) (Q : Finset (Fin m)) :
    0 < (supportedKernel (fun d => M *ᵥ d) P Q).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_supportedKernel M P Q⟩

/-- `ker(M; P, Q)` has at most `|F| ^ (|P| - rank M[Q, P])` elements. -/
theorem card_supportedKernel_le_pow_sub_blockRank {n m : Nat} (M : Matrix (Fin m) (Fin n) F)
    (P : Finset (Fin n)) (Q : Finset (Fin m)) :
    (supportedKernel (fun d => M *ᵥ d) P Q).card ≤
      Fintype.card F ^ (P.card - blockRank M Q P) := by
  classical
  set B := M.submatrix (fun i : ↥Q => (i : Fin m)) (fun j : ↥P => (j : Fin n)) with hB
  let φ : (Fin n → F) → (↥P → F) := fun d j => d j
  have maps : Set.MapsTo φ ↑(supportedKernel (fun d => M *ᵥ d) P Q)
      ↑(Finset.univ.filter fun v => v ∈ LinearMap.ker B.mulVecLin) := by
    intro d hd
    simp only [supportedKernel, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hd
    obtain ⟨hsupp, hzero⟩ := hd
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    funext i
    have h := hzero i.1 i.2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, hB, Matrix.submatrix_apply, φ]
    rw [sum_subtype_eq_sum (X := P) (fun j => M i.1 j * d j)
      (fun j hj => by rw [hsupp j hj, mul_zero])]
    simpa [Matrix.mulVec, dotProduct] using h
  have inj : Set.InjOn φ ↑(supportedKernel (fun d => M *ᵥ d) P Q) := by
    intro d hd d' hd' h
    simp only [supportedKernel, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hd hd'
    funext j
    by_cases hj : j ∈ P
    · exact congrFun h ⟨j, hj⟩
    · rw [hd.1 j hj, hd'.1 j hj]
  calc (supportedKernel (fun d => M *ᵥ d) P Q).card
      ≤ (Finset.univ.filter fun v => v ∈ LinearMap.ker B.mulVecLin).card :=
        Finset.card_le_card_of_injOn φ maps inj
    _ = Fintype.card F ^ (P.card - blockRank M Q P) := by
        rw [card_filter_mem_ker, Fintype.card_coe]
        rfl

/-- **Kernels of totally regular blocks.** `|ker(M; P, Q)| · |F| ^ min (|P|, |Q|) ≤ |F| ^ |P|`. -/
theorem card_supportedKernel_mul_pow_le {n m : Nat} {M : Matrix (Fin m) (Fin n) F}
    (hM : TotallyRegular M) (P : Finset (Fin n)) (Q : Finset (Fin m)) :
    (supportedKernel (fun d => M *ᵥ d) P Q).card * Fintype.card F ^ min P.card Q.card ≤
      Fintype.card F ^ P.card := by
  have hcard := card_supportedKernel_le_pow_sub_blockRank M P Q
  have hrank : min P.card Q.card ≤ blockRank M Q P := by
    rw [min_comm]
    exact min_card_le_blockRank hM Q P
  have hle : blockRank M Q P ≤ P.card :=
    (Matrix.rank_le_card_width _).trans (Fintype.card_coe P).le
  calc (supportedKernel (fun d => M *ᵥ d) P Q).card * Fintype.card F ^ min P.card Q.card
      ≤ Fintype.card F ^ (P.card - blockRank M Q P) * Fintype.card F ^ blockRank M Q P :=
        Nat.mul_le_mul hcard (Nat.pow_le_pow_right Fintype.card_pos hrank)
    _ = Fintype.card F ^ P.card := by
        rw [← pow_add]
        congr 1
        omega

/-- **Left kernels of totally regular blocks.** `|ker(Mᵀ; P, Q)| · |F| ^ min (|P|, |Q|) ≤ |F| ^ |P|`
for the vectors `d` supported on `P` with `d ᵥ* M` vanishing on `Q`. -/
theorem card_supportedKernel_vecMul_mul_pow_le {n m : Nat} {M : Matrix (Fin n) (Fin m) F}
    (hM : TotallyRegular M) (P : Finset (Fin n)) (Q : Finset (Fin m)) :
    (supportedKernel (fun d => d ᵥ* M) P Q).card * Fintype.card F ^ min P.card Q.card ≤
      Fintype.card F ^ P.card := by
  have h : supportedKernel (fun d => d ᵥ* M) P Q = supportedKernel (fun d => Mᵀ *ᵥ d) P Q := by
    simp only [Matrix.mulVec_transpose]
  rw [h]
  exact card_supportedKernel_mul_pow_le (totallyRegular_transpose hM) P Q

theorem card_supportedKernel_vecMul_pos {n m : Nat} (M : Matrix (Fin n) (Fin m) F)
    (P : Finset (Fin n)) (Q : Finset (Fin m)) :
    0 < (supportedKernel (fun d => d ᵥ* M) P Q).card :=
  Finset.card_pos.mpr ⟨0, by simp [supportedKernel]⟩

/-! ## Uniform matrices -/

section Uniform

variable {n : Nat}

omit [Field F] [DecidableEq F] in
theorem card_matrix : Fintype.card (Matrix (Fin n) (Fin n) F) = Fintype.card (Fin n → F) ^ n := by
  have h : Fintype.card (Matrix (Fin n) (Fin n) F) = Fintype.card (Fin n → Fin n → F) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h, Fintype.card_fun, Fintype.card_fin]

/-- **Vectors orthogonal to a nonzero vector** number at most `|F| ^ (n - 1)`. -/
theorem card_filter_dotProduct_mul_le {d : Fin n → F} (hd : d ≠ 0) :
    (Finset.univ.filter fun r : Fin n → F => r ⬝ᵥ d = 0).card * Fintype.card F ≤
      Fintype.card (Fin n → F) := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hd
  rw [Pi.zero_apply] at hp
  set K := Finset.univ.filter fun r : Fin n → F => r ⬝ᵥ d = 0
  have hdot : ∀ (r : Fin n → F) (t : F), (r + t • Pi.single p 1) ⬝ᵥ d = r ⬝ᵥ d + t * d p := by
    intro r t
    rw [add_dotProduct, smul_dotProduct, single_one_dotProduct, smul_eq_mul]
  rw [← Finset.card_univ (α := F), ← Finset.card_product, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun x => x.1 + x.2 • Pi.single p 1)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  rintro ⟨r, t⟩ hrt ⟨r', t'⟩ hrt' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, K, Finset.mem_filter,
    Finset.mem_univ, true_and] at hrt hrt'
  simp only at h
  have ht : t = t' := by
    have := congrArg (· ⬝ᵥ d) h
    simp only [hdot, hrt.1, hrt'.1, zero_add] at this
    exact mul_right_cancel₀ hp this
  subst ht
  simp only [Prod.mk.injEq, and_true]
  exact add_right_cancel h

/-- **Row families orthogonal to a nonzero vector on `Q`.** Families of `n` rows whose rows in
`Q` are orthogonal to `d ≠ 0` number at most `|F| ^ (n² - |Q|)`. -/
theorem card_filter_rows_mul_le {d : Fin n → F} (hd : d ≠ 0) (Q : Finset (Fin n)) :
    (Finset.univ.filter fun M : Fin n → Fin n → F => ∀ i ∈ Q, M i ⬝ᵥ d = 0).card *
        Fintype.card F ^ Q.card ≤ Fintype.card (Fin n → F) ^ n := by
  set K := Finset.univ.filter fun r : Fin n → F => r ⬝ᵥ d = 0
  have hset : (Finset.univ.filter fun M : Fin n → Fin n → F => ∀ i ∈ Q, M i ⬝ᵥ d = 0) =
      Fintype.piFinset fun i => if i ∈ Q then K else Finset.univ := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    refine forall_congr' fun i => ?_
    by_cases hi : i ∈ Q
    · simp [hi, K]
    · simp [hi]
  have hpow : Fintype.card F ^ Q.card = ∏ i, if i ∈ Q then Fintype.card F else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [hset, Fintype.card_piFinset, hpow, ← Finset.prod_mul_distrib]
  calc ∏ i, ((if i ∈ Q then K else Finset.univ).card * if i ∈ Q then Fintype.card F else 1)
      ≤ ∏ _i : Fin n, Fintype.card (Fin n → F) := Finset.prod_le_prod fun i _ => by
        split_ifs
        · exact card_filter_dotProduct_mul_le hd
        · simp
    _ = Fintype.card (Fin n → F) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Matrices killing a nonzero vector on `Q`** number at most `|F| ^ (n² - |Q|)`. -/
theorem card_filter_mulVec_mul_le {d : Fin n → F} (hd : d ≠ 0) (Q : Finset (Fin n)) :
    (Finset.univ.filter fun M : Matrix (Fin n) (Fin n) F => ∀ i ∈ Q, (M *ᵥ d) i = 0).card *
        Fintype.card F ^ Q.card ≤ Fintype.card (Matrix (Fin n) (Fin n) F) := by
  rw [card_matrix]
  exact card_filter_rows_mul_le hd Q

/-- **Kernels of uniform blocks, exact form.** Summed over all square matrices,
`(∑ |ker(M; P, Q)|) · |F| ^ |Q| ≤ |F| ^ (n²) (|F| ^ |Q| + |F| ^ |P|)`: the zero vector lies in
every kernel, and each of the at most `|F| ^ |P|` nonzero supported vectors in at most
`|F| ^ (n² - |Q|)` of them. -/
theorem sum_card_supportedKernel_mul_pow_card_le (P Q : Finset (Fin n)) :
    (∑ M : Matrix (Fin n) (Fin n) F, (supportedKernel (fun d => M *ᵥ d) P Q).card) *
        Fintype.card F ^ Q.card ≤
      Fintype.card (Matrix (Fin n) (Fin n) F) *
        (Fintype.card F ^ Q.card + Fintype.card F ^ P.card) := by
  set r : Matrix (Fin n) (Fin n) F → (Fin n → F) → Prop := fun M d => ∀ i ∈ Q, (M *ᵥ d) i = 0
  have hker : ∀ M, supportedKernel (fun d => M *ᵥ d) P Q =
      Finset.bipartiteAbove r (slice P 0) M := by
    intro M
    ext d
    simp [supportedKernel, Finset.bipartiteAbove, mem_slice, r]
  simp_rw [hker]
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, Finset.sum_mul]
  set c := Fintype.card (Matrix (Fin n) (Fin n) F)
  have hterm : ∀ d ∈ slice P 0, (Finset.bipartiteBelow r Finset.univ d).card *
      Fintype.card F ^ Q.card ≤ (if d = 0 then c * Fintype.card F ^ Q.card else 0) + c := by
    intro d _
    by_cases hd0 : d = 0
    · rw [ite_eq_left hd0]
      refine le_trans ?_ (Nat.le_add_right _ _)
      exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (by simp [c]))
    · rw [ite_eq_right hd0, zero_add]
      exact card_filter_mulVec_mul_le hd0 Q
  calc ∑ d ∈ slice P 0, (Finset.bipartiteBelow r Finset.univ d).card * Fintype.card F ^ Q.card
      ≤ ∑ d ∈ slice P 0, ((if d = 0 then c * Fintype.card F ^ Q.card else 0) + c) :=
        Finset.sum_le_sum hterm
    _ = (if (0 : Fin n → F) ∈ slice P 0 then c * Fintype.card F ^ Q.card else 0) +
          (slice P 0).card * c := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_const, smul_eq_mul]
    _ ≤ c * (Fintype.card F ^ Q.card + Fintype.card F ^ P.card) := by
        rw [card_slice, mul_add]
        split_ifs
        · rw [mul_comm (Fintype.card F ^ P.card)]
        · rw [zero_add, mul_comm (Fintype.card F ^ P.card)]
          exact Nat.le_add_left _ _

/-- **Kernels of uniform blocks.** Summed over all square matrices,
`(∑ |ker(M; P, Q)|) · |F| ^ min (|P|, |Q|) ≤ 2 |F| ^ (n²) |F| ^ |P|`. -/
theorem sum_card_supportedKernel_mul_pow_le (P Q : Finset (Fin n)) :
    (∑ M : Matrix (Fin n) (Fin n) F, (supportedKernel (fun d => M *ᵥ d) P Q).card) *
        Fintype.card F ^ min P.card Q.card ≤
      2 * Fintype.card (Matrix (Fin n) (Fin n) F) * Fintype.card F ^ P.card := by
  have h := sum_card_supportedKernel_mul_pow_card_le (F := F) P Q
  set X := ∑ M : Matrix (Fin n) (Fin n) F, (supportedKernel (fun d => M *ᵥ d) P Q).card
  set c := Fintype.card (Matrix (Fin n) (Fin n) F)
  have hq : 0 < Fintype.card F := Fintype.card_pos
  rcases le_total Q.card P.card with hQP | hPQ
  · rw [min_eq_right hQP]
    have hpow : Fintype.card F ^ Q.card ≤ Fintype.card F ^ P.card := Nat.pow_le_pow_right hq hQP
    calc X * Fintype.card F ^ Q.card ≤ c * (Fintype.card F ^ Q.card + Fintype.card F ^ P.card) :=
          h
      _ ≤ c * (Fintype.card F ^ P.card + Fintype.card F ^ P.card) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right hpow _)
      _ = 2 * c * Fintype.card F ^ P.card := by ring
  · rw [min_eq_left hPQ]
    have hpow : Fintype.card F ^ P.card ≤ Fintype.card F ^ Q.card := Nat.pow_le_pow_right hq hPQ
    have hX : X ≤ 2 * c := by
      refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hq Q.card)
      calc X * Fintype.card F ^ Q.card
          ≤ c * (Fintype.card F ^ Q.card + Fintype.card F ^ P.card) := h
        _ ≤ c * (Fintype.card F ^ Q.card + Fintype.card F ^ Q.card) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add_left hpow _)
        _ = 2 * c * Fintype.card F ^ Q.card := by ring
    exact Nat.mul_le_mul_right _ hX

/-- **Left kernels of uniform blocks.** The same bound for `ker(Mᵀ; P, Q)`, the vectors `d`
supported on `P` with `d ᵥ* M` vanishing on `Q`. -/
theorem sum_card_supportedKernel_vecMul_mul_pow_le (P Q : Finset (Fin n)) :
    (∑ M : Matrix (Fin n) (Fin n) F, (supportedKernel (fun d => d ᵥ* M) P Q).card) *
        Fintype.card F ^ min P.card Q.card ≤
      2 * Fintype.card (Matrix (Fin n) (Fin n) F) * Fintype.card F ^ P.card := by
  have h : ∑ M : Matrix (Fin n) (Fin n) F, (supportedKernel (fun d => d ᵥ* M) P Q).card =
      ∑ M : Matrix (Fin n) (Fin n) F, (supportedKernel (fun d => M *ᵥ d) P Q).card := by
    refine Fintype.sum_equiv (Matrix.transposeAddEquiv (Fin n) (Fin n) F).toEquiv _ _
      fun M => ?_
    simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Matrix.transposeAddEquiv_apply,
      Matrix.mulVec_transpose]
  rw [h]
  exact sum_card_supportedKernel_mul_pow_le P Q

end Uniform

/-! ## Averaging -/

/-- **Averaging.** If positive quantities `K t x` average at most `2 q ^ (e t)` over `x` for every
`t`, some `x` makes `∏ t, K t x ≤ q ^ (∑ t, e t + 2 |T|)`. -/
theorem exists_prod_le_pow {X T : Type*} [Fintype X] [Nonempty X] [Fintype T] {q : Nat}
    (hq : 1 < q) (K : T → X → Nat) (hK : ∀ t x, 0 < K t x) (e : T → Nat)
    (hsum : ∀ t, ∑ x, K t x ≤ 2 * Fintype.card X * q ^ e t) :
    ∃ x, ∏ t, K t x ≤ q ^ (∑ t, e t + 2 * Fintype.card T) := by
  set d : T → X → Nat := fun t x => Nat.log q (K t x) with hd
  -- The excess exponent is paid for by the quantity.
  have hexc : ∀ t x, q ^ e t * (d t x + 1 - e t) ≤ K t x := by
    intro t x
    by_cases h : d t x + 1 ≤ e t
    · rw [Nat.sub_eq_zero_of_le h, mul_zero]
      exact Nat.zero_le _
    · have h1 : d t x + 1 - e t ≤ q ^ (d t x - e t) := by
        have := Nat.lt_pow_self (n := d t x - e t) hq
        omega
      calc q ^ e t * (d t x + 1 - e t) ≤ q ^ e t * q ^ (d t x - e t) := Nat.mul_le_mul_left _ h1
        _ = q ^ d t x := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ K t x := Nat.pow_log_le_self q (hK t x).ne'
  have havg : ∀ t, ∑ x, (d t x + 1 - e t) ≤ 2 * Fintype.card X := by
    intro t
    have hpos : 0 < q ^ e t := pow_pos (by omega) _
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [Finset.mul_sum]
    calc ∑ x, q ^ e t * (d t x + 1 - e t) ≤ ∑ x, K t x := Finset.sum_le_sum fun x _ => hexc t x
      _ ≤ 2 * Fintype.card X * q ^ e t := hsum t
      _ = q ^ e t * (2 * Fintype.card X) := by ring
  have htot : ∑ x, ∑ t, (d t x + 1 - e t) ≤ ∑ _x : X, 2 * Fintype.card T := by
    rw [Finset.sum_comm]
    calc ∑ t, ∑ x, (d t x + 1 - e t) ≤ ∑ _t : T, 2 * Fintype.card X :=
          Finset.sum_le_sum fun t _ => havg t
      _ = ∑ _x : X, 2 * Fintype.card T := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  obtain ⟨x, -, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htot
  refine ⟨x, ?_⟩
  calc ∏ t, K t x ≤ ∏ t, q ^ (e t + (d t x + 1 - e t)) := Finset.prod_le_prod fun t _ => by
        have := Nat.lt_pow_succ_log_self hq (K t x)
        exact this.le.trans (Nat.pow_le_pow_right (by omega) (by simp only [hd]; omega))
    _ = q ^ (∑ t, e t + ∑ t, (d t x + 1 - e t)) := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
    _ ≤ q ^ (∑ t, e t + 2 * Fintype.card T) := Nat.pow_le_pow_right (by omega) (by omega)


end Algebraic.Cutwidth.MultiOutput.MatMul.Internal

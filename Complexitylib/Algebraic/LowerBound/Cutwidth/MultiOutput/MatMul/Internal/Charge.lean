/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Internal.Coordinates
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Internal.Kernel
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Internal

/-!
# The three charges bound the crossing signals

Let the wires `out` of a program over a finite field carry `matMul n`, and split the wires into
`S` and its complement, crossed by `w` signals, and place the terminals `matMulTermA`,
`matMulTermB`, `matMulTermC` as in `Tripartite` (`Tripartite.place`). Each charge is bounded
through the kernels of blocks of one `n × n` matrix, two blocks per vertex.

* **Charge `R_I`, fixing `B = B₀`** (`pow_le_mul_prodI`). On the inputs with second factor
  `B₀` the product is linear, and its change `δA ↦ δA B₀` is block diagonal over the rows `i`.
  The restricted rank-cut bound (`card_pow_le_supportedKernel_of_trace`) and the rowSet
  decomposition of the kernels give `|F| ^ (n²) ≤ |F| ^ w ∏ i, |ker₁ i| |ker₂ i|`, where
  `ker₁ i` and `ker₂ i` are left kernels of the blocks `B₀[rowSet a i, (rowSet c i)ᶜ]` and
  `B₀[(rowSet a i)ᶜ, rowSet c i]`.
* **Charge `R_K`, fixing `A = A₀`** (`pow_le_mul_prodK`): symmetrically, over the columns `k`.
* **Charge `R_J`, the Hessian** (`pow_le_mul_prodJ`). The combination `∑ i k, Λ i k C i k` is
  the quadratic form of `bilinForm Λ`, so the cross block of `H = M + Mᵀ` between the inputs
  in `S` and outside `S` has rank at most `w` (`blockRank_add_transpose_le_of_sum`). Its kernel
  is block diagonal over the inner index `j`, which gives
  `|F| ^ |X_T| ≤ |F| ^ w ∏ j, |ker₁ j| |ker₂ j|` with `|X_T|` the inputs outside `S`.

At a vertex with `a` and `c` placed terminals of its two kinds, a totally regular matrix makes
the two kernels miss `min (a, n - c) + min (n - a, c) = minority n (a + c)` dimensions
(`prodI_mul_pow_le` and its siblings), so each charge is at most `w`
(`chargeI_le_of_totallyRegular`, ...). For a uniformly random matrix each kernel has average
size at most twice the ideal one (`sum_card_supportedKernel_mul_pow_le`), so by averaging some
matrix loses at most `4 n` (`exists_prodI_mul_pow_le`, ...), and each charge is at most
`w + 4 n` over every finite field (`chargeI_le_add`, ...).
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.Internal

open Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Matrix Tripartite

variable {σ : Signature} {n s : Nat}

/-! ## Placing the terminals -/

section Place

variable (S : Finset (Wire (n * n + n * n) s)) (out : Fin (n * n) → Wire (n * n + n * n) s)

theorem mem_rowSet_placeA {i j : Fin n} :
    j ∈ rowSet (place (matMulTermA n s) S) i ↔ matMulLeft n i j ∈ inputsIn S := by
  simp only [rowSet, place, Finset.mem_filter, Finset.mem_univ, true_and, mem_inputsIn]
  rfl

theorem mem_colSet_placeA {i j : Fin n} :
    i ∈ colSet (place (matMulTermA n s) S) j ↔ matMulLeft n i j ∈ inputsIn S := by
  simp only [colSet, place, Finset.mem_filter, Finset.mem_univ, true_and, mem_inputsIn]
  rfl

theorem mem_rowSet_placeB {j k : Fin n} :
    k ∈ rowSet (place (matMulTermB n s) S) j ↔ matMulRight n j k ∈ inputsIn S := by
  simp only [rowSet, place, Finset.mem_filter, Finset.mem_univ, true_and, mem_inputsIn]
  rfl

theorem mem_colSet_placeB {j k : Fin n} :
    j ∈ colSet (place (matMulTermB n s) S) k ↔ matMulRight n j k ∈ inputsIn S := by
  simp only [colSet, place, Finset.mem_filter, Finset.mem_univ, true_and, mem_inputsIn]
  rfl

theorem mem_rowSet_placeC {i k : Fin n} :
    k ∈ rowSet (place (matMulTermC out) S) i ↔ matMulOutput n i k ∈ outputsIn out S := by
  simp only [rowSet, place, Finset.mem_filter, Finset.mem_univ, true_and, outputsIn]
  rfl

theorem mem_colSet_placeC {i k : Fin n} :
    i ∈ colSet (place (matMulTermC out) S) k ↔ matMulOutput n i k ∈ outputsIn out S := by
  simp only [colSet, place, Finset.mem_filter, Finset.mem_univ, true_and, outputsIn]
  rfl

end Place

/-! ## Arithmetic of the per-vertex bounds -/

section Arithmetic

theorem minority_add_eq {a c : Nat} (ha : a ≤ n) (hc : c ≤ n) :
    minority n (a + c) = min a (n - c) + min (n - a) c := by
  unfold minority
  omega

/-- **Multiplying the per-vertex bounds.** -/
theorem prod_mul_pow_le {q : Nat} (K₁ K₂ p₁ p₂ m₁ m₂ : Fin n → Nat)
    (h₁ : ∀ v, K₁ v * q ^ m₁ v ≤ q ^ p₁ v) (h₂ : ∀ v, K₂ v * q ^ m₂ v ≤ q ^ p₂ v) :
    (∏ v, (K₁ v * K₂ v)) * q ^ (∑ v, (m₁ v + m₂ v)) ≤ q ^ (∑ v, (p₁ v + p₂ v)) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod fun v _ => ?_
  calc K₁ v * K₂ v * q ^ (m₁ v + m₂ v) = (K₁ v * q ^ m₁ v) * (K₂ v * q ^ m₂ v) := by ring
    _ ≤ q ^ p₁ v * q ^ p₂ v := Nat.mul_le_mul (h₁ v) (h₂ v)
    _ = q ^ (p₁ v + p₂ v) := (pow_add _ _ _).symm

/-- **Averaging the per-vertex bounds.** If the two families of kernels at each vertex average
at most twice their ideal sizes, some choice loses at most `4 n` in the exponent. -/
theorem exists_prod_mul_pow_le {X : Type*} [Fintype X] [Nonempty X] {q : Nat} (hq : 1 < q)
    (K₁ K₂ : Fin n → X → Nat) (hK₁ : ∀ v x, 0 < K₁ v x) (hK₂ : ∀ v x, 0 < K₂ v x)
    (p₁ p₂ m₁ m₂ : Fin n → Nat) (hm₁ : ∀ v, m₁ v ≤ p₁ v) (hm₂ : ∀ v, m₂ v ≤ p₂ v)
    (h₁ : ∀ v, (∑ x, K₁ v x) * q ^ m₁ v ≤ 2 * Fintype.card X * q ^ p₁ v)
    (h₂ : ∀ v, (∑ x, K₂ v x) * q ^ m₂ v ≤ 2 * Fintype.card X * q ^ p₂ v) :
    ∃ x, (∏ v, (K₁ v x * K₂ v x)) * q ^ (∑ v, (m₁ v + m₂ v)) ≤
      q ^ (∑ v, (p₁ v + p₂ v) + 4 * n) := by
  have hq0 : 0 < q := by omega
  have hsum : ∀ (K : Fin n → X → Nat) (p m : Fin n → Nat), (∀ v, m v ≤ p v) →
      (∀ v, (∑ x, K v x) * q ^ m v ≤ 2 * Fintype.card X * q ^ p v) →
      ∀ v, ∑ x, K v x ≤ 2 * Fintype.card X * q ^ (p v - m v) := by
    intro K p m hm h v
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hq0 (m v))
    calc (∑ x, K v x) * q ^ m v ≤ 2 * Fintype.card X * q ^ p v := h v
      _ = 2 * Fintype.card X * q ^ (p v - m v) * q ^ m v := by
          rw [mul_assoc (2 * Fintype.card X), ← pow_add, Nat.sub_add_cancel (hm v)]
  obtain ⟨x, hx⟩ := exists_prod_le_pow hq (fun t : Fin n ⊕ Fin n => Sum.elim K₁ K₂ t)
    (fun t => by rcases t with v | v <;> simp [hK₁, hK₂])
    (Sum.elim (fun v => p₁ v - m₁ v) fun v => p₂ v - m₂ v)
    (fun t => by
      rcases t with v | v
      · exact hsum K₁ p₁ m₁ hm₁ h₁ v
      · exact hsum K₂ p₂ m₂ hm₂ h₂ v)
  refine ⟨x, ?_⟩
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type,
    Fintype.card_sum, Fintype.card_fin] at hx
  have hpm : ∑ v, (p₁ v - m₁ v) + ∑ v, (p₂ v - m₂ v) + ∑ v, (m₁ v + m₂ v) =
      ∑ v, (p₁ v + p₂ v) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have := hm₁ v
    have := hm₂ v
    omega
  calc (∏ v, (K₁ v x * K₂ v x)) * q ^ (∑ v, (m₁ v + m₂ v))
      = (∏ v, K₁ v x) * (∏ v, K₂ v x) * q ^ (∑ v, (m₁ v + m₂ v)) := by
        rw [Finset.prod_mul_distrib]
    _ ≤ q ^ (∑ v, (p₁ v - m₁ v) + ∑ v, (p₂ v - m₂ v) + 2 * (n + n)) *
          q ^ (∑ v, (m₁ v + m₂ v)) := Nat.mul_le_mul_right _ hx
    _ = q ^ (∑ v, (p₁ v + p₂ v) + 4 * n) := by
        rw [← pow_add, ← hpm]
        congr 1
        ring

/-- **Comparing exponents.** If `q ^ E ≤ q ^ w X` and `X q ^ R ≤ q ^ (E + L)`, then
`R ≤ w + L`. -/
theorem le_add_of_pow_le {q E w R L X : Nat} (hq : 1 < q) (h₁ : q ^ E ≤ q ^ w * X)
    (h₂ : X * q ^ R ≤ q ^ (E + L)) : R ≤ w + L := by
  have h : q ^ (E + R) ≤ q ^ (w + E + L) := by
    calc q ^ (E + R) = q ^ E * q ^ R := pow_add _ _ _
      _ ≤ q ^ w * X * q ^ R := Nat.mul_le_mul_right _ h₁
      _ = q ^ w * (X * q ^ R) := by ring
      _ ≤ q ^ w * q ^ (E + L) := Nat.mul_le_mul_left _ h₂
      _ = q ^ (w + E + L) := by rw [← pow_add, add_assoc]
  have := (Nat.pow_le_pow_iff_right hq).mp h
  omega

end Arithmetic

/-! ## Charge identities -/

section Identities

theorem card_compl_eq {X : Finset (Fin n)} : Xᶜ.card = n - X.card := by
  rw [Finset.card_compl, Fintype.card_fin]

theorem card_le_n (X : Finset (Fin n)) : X.card ≤ n := by
  simpa using Finset.card_le_univ X

theorem sum_min_eq_chargeI (a c : Finset (Fin n × Fin n)) :
    ∑ i, (min (rowSet a i).card ((rowSet c i)ᶜ).card +
      min ((rowSet a i)ᶜ).card (rowSet c i).card) = chargeI a c := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [card_compl_eq, card_compl_eq, degI, minority_add_eq (card_le_n _) (card_le_n _)]

theorem sum_min_eq_chargeK (b c : Finset (Fin n × Fin n)) :
    ∑ k, (min (colSet b k).card ((colSet c k)ᶜ).card +
      min ((colSet b k)ᶜ).card (colSet c k).card) = chargeK b c := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [card_compl_eq, card_compl_eq, degK, minority_add_eq (card_le_n _) (card_le_n _)]

theorem sum_min_eq_chargeJ (a b : Finset (Fin n × Fin n)) :
    ∑ j, (min ((colSet a j)ᶜ).card (rowSet b j).card +
      min ((rowSet b j)ᶜ).card (colSet a j).card) = chargeJ a b := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [card_compl_eq, card_compl_eq, degJ, minority_add_eq (card_le_n _) (card_le_n _)]
  omega

theorem sum_card_add_card_compl (X : Fin n → Finset (Fin n)) :
    ∑ v, ((X v).card + ((X v)ᶜ).card) = n * n := by
  simp [Finset.card_add_card_compl, Finset.sum_const]

theorem card_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (X : Finset α) :
    X.card = ∑ x, if x ∈ X then 1 else 0 := by
  rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **The inputs outside `S`**, counted at the vertices of `J`. -/
theorem card_compl_inputsIn (S : Finset (Wire (n * n + n * n) s)) :
    (inputsIn S)ᶜ.card = ∑ j, (((colSet (place (matMulTermA n s) S) j)ᶜ).card +
      ((rowSet (place (matMulTermB n s) S) j)ᶜ).card) := by
  rw [card_eq_sum_ite, sum_input, Finset.sum_comm (f := fun i j =>
    if matMulLeft n i j ∈ (inputsIn S)ᶜ then 1 else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [card_eq_sum_ite ((colSet _ j)ᶜ), card_eq_sum_ite ((rowSet _ j)ᶜ)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.mem_compl, mem_colSet_placeA]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Finset.mem_compl, mem_rowSet_placeB]

end Identities

/-! ## Kernel products -/

section Kernels

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The kernels of the rows of `δA ↦ δA B₀` at the split `S`. -/
noncomputable def prodI (B₀ : Matrix (Fin n) (Fin n) F) (S : Finset (Wire (n * n + n * n) s))
    (out : Fin (n * n) → Wire (n * n + n * n) s) : Nat :=
  ∏ i, ((supportedKernel (fun u => u ᵥ* B₀) (rowSet (place (matMulTermA n s) S) i)
      (rowSet (place (matMulTermC out) S) i)ᶜ).card *
    (supportedKernel (fun u => u ᵥ* B₀) (rowSet (place (matMulTermA n s) S) i)ᶜ
      (rowSet (place (matMulTermC out) S) i)).card)

/-- The kernels of the columns of `δB ↦ A₀ δB` at the split `S`. -/
noncomputable def prodK (A₀ : Matrix (Fin n) (Fin n) F) (S : Finset (Wire (n * n + n * n) s))
    (out : Fin (n * n) → Wire (n * n + n * n) s) : Nat :=
  ∏ k, ((supportedKernel (fun u => A₀ *ᵥ u) (colSet (place (matMulTermB n s) S) k)
      (colSet (place (matMulTermC out) S) k)ᶜ).card *
    (supportedKernel (fun u => A₀ *ᵥ u) (colSet (place (matMulTermB n s) S) k)ᶜ
      (colSet (place (matMulTermC out) S) k)).card)

/-- The kernels of the blocks of the Hessian of `∑ Λ i k C i k` at the split `S`. -/
noncomputable def prodJ (Λ : Matrix (Fin n) (Fin n) F) (S : Finset (Wire (n * n + n * n) s)) :
    Nat :=
  ∏ j, ((supportedKernel (fun u => u ᵥ* Λ) (colSet (place (matMulTermA n s) S) j)ᶜ
      (rowSet (place (matMulTermB n s) S) j)).card *
    (supportedKernel (fun u => Λ *ᵥ u) (rowSet (place (matMulTermB n s) S) j)ᶜ
      (colSet (place (matMulTermA n s) S) j)).card)

/-- **Row decomposition of the kernels with `B` fixed.** -/
theorem card_supportedKernel_shiftLeft_le (B₀ : Matrix (Fin n) (Fin n) F)
    (P : Finset (Fin (n * n + n * n))) (hP : P ⊆ leftCoords n) (Q : Finset (Fin (n * n))) :
    (supportedKernel (shiftLeft B₀) P Q).card ≤
      ∏ i, (supportedKernel (fun u => u ᵥ* B₀) (Finset.univ.filter fun j => matMulLeft n i j ∈ P)
        (Finset.univ.filter fun k => matMulOutput n i k ∈ Q)).card := by
  rw [← Fintype.card_piFinset]
  refine Finset.card_le_card_of_injOn (fun d i j => d (matMulLeft n i j)) ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, supportedKernel, Finset.mem_filter, Finset.mem_univ,
      true_and] at hd
    simp only [Finset.mem_coe, Fintype.mem_piFinset, supportedKernel, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro i
    refine ⟨fun j hj => hd.1 _ hj, fun k hk => ?_⟩
    have := hd.2 _ hk
    rw [shiftLeft_output] at this
    simpa [Matrix.vecMul, dotProduct] using this
  · intro d hd d' hd' h
    simp only [Finset.coe_filter, supportedKernel, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hd hd'
    funext x
    rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
    · exact congrFun (congrFun h i) j
    · have hx : matMulRight n j k ∉ P := fun hx => matMulRight_notMem_leftCoords j k (hP hx)
      rw [hd.1 _ hx, hd'.1 _ hx]

/-- **Column decomposition of the kernels with `A` fixed.** -/
theorem card_supportedKernel_shiftRight_le (A₀ : Matrix (Fin n) (Fin n) F)
    (P : Finset (Fin (n * n + n * n))) (hP : P ⊆ rightCoords n) (Q : Finset (Fin (n * n))) :
    (supportedKernel (shiftRight A₀) P Q).card ≤
      ∏ k, (supportedKernel (fun u => A₀ *ᵥ u) (Finset.univ.filter fun j => matMulRight n j k ∈ P)
        (Finset.univ.filter fun i => matMulOutput n i k ∈ Q)).card := by
  rw [← Fintype.card_piFinset]
  refine Finset.card_le_card_of_injOn (fun d k j => d (matMulRight n j k)) ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, supportedKernel, Finset.mem_filter, Finset.mem_univ,
      true_and] at hd
    simp only [Finset.mem_coe, Fintype.mem_piFinset, supportedKernel, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro k
    refine ⟨fun j hj => hd.1 _ hj, fun i hi => ?_⟩
    have := hd.2 _ hi
    rw [shiftRight_output] at this
    simpa [Matrix.mulVec, dotProduct] using this
  · intro d hd d' hd' h
    simp only [Finset.coe_filter, supportedKernel, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hd hd'
    funext x
    rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
    · have hx : matMulLeft n i j ∉ P := fun hx => matMulLeft_notMem_rightCoords i j (hP hx)
      rw [hd.1 _ hx, hd'.1 _ hx]
    · exact congrFun (congrFun h k) j

variable {p : Program σ (n * n + n * n) s} {I : Interpretation σ F}
  {out : Fin (n * n) → Wire (n * n + n * n) s}

/-- **The bound behind `R_I`.** Fixing the second factor to `B₀`,
`|F| ^ (n²) ≤ |F| ^ w · prodI B₀ S`. -/
theorem pow_le_mul_prodI (hf : ∀ z o, p.trace I z (out o) = matMul n z o)
    (S : Finset (Wire (n * n + n * n) s)) (B₀ : Matrix (Fin n) (Fin n) F) :
    Fintype.card F ^ (n * n) ≤
      Fintype.card F ^ ((forward p S).card + (backward p S).card) * prodI B₀ S out := by
  have h := card_pow_le_supportedKernel_of_trace p I out hf S (leftCoords n)
    (matMulInput 0 B₀) (shiftLeft B₀) fun z z' hz hz' => matMul_sub_left B₀ z z' hz hz'
  rw [card_leftCoords] at h
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  have h₁ := card_supportedKernel_shiftLeft_le B₀ (inputsIn S ∩ leftCoords n)
    Finset.inter_subset_right (outputsIn out S)ᶜ
  have h₂ := card_supportedKernel_shiftLeft_le B₀ ((inputsIn S)ᶜ ∩ leftCoords n)
    Finset.inter_subset_right (outputsIn out S)
  have e₁ : ∀ i, (Finset.univ.filter fun j => matMulLeft n i j ∈ inputsIn S ∩ leftCoords n) =
      rowSet (place (matMulTermA n s) S) i := fun i => by
    ext j
    simp [mem_rowSet_placeA, matMulLeft_mem_leftCoords]
  have e₂ : ∀ i, (Finset.univ.filter fun k => matMulOutput n i k ∈ (outputsIn out S)ᶜ) =
      (rowSet (place (matMulTermC out) S) i)ᶜ := fun i => by
    ext k
    simp [mem_rowSet_placeC]
  have e₃ : ∀ i, (Finset.univ.filter fun j => matMulLeft n i j ∈ (inputsIn S)ᶜ ∩ leftCoords n) =
      (rowSet (place (matMulTermA n s) S) i)ᶜ := fun i => by
    ext j
    simp [mem_rowSet_placeA, matMulLeft_mem_leftCoords]
  have e₄ : ∀ i, (Finset.univ.filter fun k => matMulOutput n i k ∈ outputsIn out S) =
      rowSet (place (matMulTermC out) S) i := fun i => by
    ext k
    simp [mem_rowSet_placeC]
  simp only [e₁, e₂, e₃, e₄] at h₁ h₂
  rw [prodI, Finset.prod_mul_distrib]
  exact Nat.mul_le_mul h₁ h₂

/-- **The bound behind `R_K`.** Fixing the first factor to `A₀`,
`|F| ^ (n²) ≤ |F| ^ w · prodK A₀ S`. -/
theorem pow_le_mul_prodK (hf : ∀ z o, p.trace I z (out o) = matMul n z o)
    (S : Finset (Wire (n * n + n * n) s)) (A₀ : Matrix (Fin n) (Fin n) F) :
    Fintype.card F ^ (n * n) ≤
      Fintype.card F ^ ((forward p S).card + (backward p S).card) * prodK A₀ S out := by
  have h := card_pow_le_supportedKernel_of_trace p I out hf S (rightCoords n)
    (matMulInput A₀ 0) (shiftRight A₀) fun z z' hz hz' => matMul_sub_right A₀ z z' hz hz'
  rw [card_rightCoords] at h
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  have h₁ := card_supportedKernel_shiftRight_le A₀ (inputsIn S ∩ rightCoords n)
    Finset.inter_subset_right (outputsIn out S)ᶜ
  have h₂ := card_supportedKernel_shiftRight_le A₀ ((inputsIn S)ᶜ ∩ rightCoords n)
    Finset.inter_subset_right (outputsIn out S)
  have e₁ : ∀ k, (Finset.univ.filter fun j => matMulRight n j k ∈ inputsIn S ∩ rightCoords n) =
      colSet (place (matMulTermB n s) S) k := fun k => by
    ext j
    simp [mem_colSet_placeB, matMulRight_mem_rightCoords]
  have e₂ : ∀ k, (Finset.univ.filter fun i => matMulOutput n i k ∈ (outputsIn out S)ᶜ) =
      (colSet (place (matMulTermC out) S) k)ᶜ := fun k => by
    ext i
    simp [mem_colSet_placeC]
  have e₃ : ∀ k,
      (Finset.univ.filter fun j => matMulRight n j k ∈ (inputsIn S)ᶜ ∩ rightCoords n) =
        (colSet (place (matMulTermB n s) S) k)ᶜ := fun k => by
    ext j
    simp [mem_colSet_placeB, matMulRight_mem_rightCoords]
  have e₄ : ∀ k, (Finset.univ.filter fun i => matMulOutput n i k ∈ outputsIn out S) =
      colSet (place (matMulTermC out) S) k := fun k => by
    ext i
    simp [mem_colSet_placeC]
  simp only [e₁, e₂, e₃, e₄] at h₁ h₂
  rw [prodK, Finset.prod_mul_distrib]
  exact Nat.mul_le_mul h₁ h₂

open Classical in
/-- **Kernels of the Hessian block.** The kernel of the cross block of `H = M + Mᵀ` between the
inputs in `S` and outside `S` embeds in the product of the kernels at the vertices `j`. -/
theorem card_ker_le_prodJ (Λ : Matrix (Fin n) (Fin n) F) (S : Finset (Wire (n * n + n * n) s)) :
    (Finset.univ.filter fun v => v ∈ LinearMap.ker
      ((bilinForm Λ + (bilinForm Λ)ᵀ).submatrix (fun x : ↥(inputsIn S) => (x : Fin _))
        (fun y : ↥(inputsIn S)ᶜ => (y : Fin _))).mulVecLin).card ≤ prodJ Λ S := by
  classical
  set H := bilinForm Λ + (bilinForm Λ)ᵀ with hH
  set B := H.submatrix (fun x : ↥(inputsIn S) => (x : Fin _))
    (fun y : ↥(inputsIn S)ᶜ => (y : Fin _)) with hB
  let ext : (↥(inputsIn S)ᶜ → F) → Fin (n * n + n * n) → F :=
    fun v x => if h : x ∈ (inputsIn S)ᶜ then v ⟨x, h⟩ else 0
  have hext0 : ∀ v x, x ∈ inputsIn S → ext v x = 0 := fun v x hx => by
    simp [ext, hx]
  have hext : ∀ v x (hx : x ∈ inputsIn S), (B *ᵥ v) ⟨x, hx⟩ = (H *ᵥ ext v) x := by
    intro v x hx
    simp only [Matrix.mulVec, dotProduct, hB, Matrix.submatrix_apply]
    rw [← sum_subtype_eq_sum (X := (inputsIn S)ᶜ) (fun y => H x y * ext v y)
      (fun y hy => by rw [hext0 v y (by simpa using hy), mul_zero])]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show ext v y = v y from dite_eq_left y.2]
  have hcard : prodJ Λ S = (Fintype.piFinset fun j =>
      supportedKernel (fun u => u ᵥ* Λ) (colSet (place (matMulTermA n s) S) j)ᶜ
        (rowSet (place (matMulTermB n s) S) j) ×ˢ
      supportedKernel (fun u => Λ *ᵥ u) (rowSet (place (matMulTermB n s) S) j)ᶜ
        (colSet (place (matMulTermA n s) S) j)).card := by
    rw [Fintype.card_piFinset, prodJ]
    simp only [Finset.card_product]
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun v j => (fun i => ext v (matMulLeft n i j), fun k => ext v (matMulRight n j k))) ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product, supportedKernel,
      Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    refine ⟨⟨fun i hi => ?_, fun k hk => ?_⟩, ⟨fun k hk => ?_, fun i hi => ?_⟩⟩
    · rw [Finset.mem_compl, not_not, mem_colSet_placeA] at hi
      exact hext0 v _ hi
    · rw [mem_rowSet_placeB] at hk
      have h := congrFun hv ⟨_, hk⟩
      rw [hext, hH, mulVec_add_transpose_right, Pi.zero_apply] at h
      simp only [Matrix.vecMul, dotProduct]
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · rw [Finset.mem_compl, not_not, mem_rowSet_placeB] at hk
      exact hext0 v _ hk
    · rw [mem_colSet_placeA] at hi
      have h := congrFun hv ⟨_, hi⟩
      rw [hext, hH, mulVec_add_transpose_left, Pi.zero_apply] at h
      simpa [Matrix.mulVec, dotProduct] using h
  · intro v _ v' _ h
    have hall : ∀ x, ext v x = ext v' x := by
      intro x
      rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
      · exact congrFun (congrArg Prod.fst (congrFun h j)) i
      · exact congrFun (congrArg Prod.snd (congrFun h j)) k
    funext y
    have := hall y
    rwa [show ext v y = v y from dite_eq_left y.2,
      show ext v' y = v' y from dite_eq_left y.2] at this

/-- **The bound behind `R_J`.** For every `Λ`, with `X_T` the inputs outside `S`,
`|F| ^ |X_T| ≤ |F| ^ w · prodJ Λ S`. -/
theorem pow_le_mul_prodJ (hf : ∀ z o, p.trace I z (out o) = matMul n z o)
    (S : Finset (Wire (n * n + n * n) s)) (Λ : Matrix (Fin n) (Fin n) F) :
    Fintype.card F ^ (inputsIn S)ᶜ.card ≤
      Fintype.card F ^ ((forward p S).card + (backward p S).card) * prodJ Λ S := by
  classical
  set coeff : Fin (n * n) → F := fun o => Λ (finProdFinEquiv.symm o).1 (finProdFinEquiv.symm o).2
  have hsum : ∀ z, ∑ o, coeff o * p.trace I z (out o) = quadForm (bilinForm Λ) z := by
    intro z
    rw [quadForm_bilinForm, sum_output]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    simp only [coeff, matMulOutput, Equiv.symm_apply_apply]
  have hrank := blockRank_add_transpose_le_of_sum p I out coeff (bilinForm Λ) hsum S
  set B := (bilinForm Λ + (bilinForm Λ)ᵀ).submatrix (fun x : ↥(inputsIn S) => (x : Fin _))
    (fun y : ↥(inputsIn S)ᶜ => (y : Fin _)) with hB
  have hker := card_filter_mem_ker B
  rw [Fintype.card_coe] at hker
  have hle : B.rank ≤ (inputsIn S)ᶜ.card :=
    (Matrix.rank_le_card_width B).trans (Fintype.card_coe _).le
  have hrank' : B.rank ≤ (forward p S).card + (backward p S).card := hrank
  calc Fintype.card F ^ (inputsIn S)ᶜ.card
      = Fintype.card F ^ B.rank * Fintype.card F ^ ((inputsIn S)ᶜ.card - B.rank) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
    _ ≤ Fintype.card F ^ ((forward p S).card + (backward p S).card) * prodJ Λ S :=
        Nat.mul_le_mul (Nat.pow_le_pow_right Fintype.card_pos hrank')
          (hker.symm.le.trans (card_ker_le_prodJ Λ S))

end Kernels

/-! ## The charges -/

section Charges

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Totally regular rows.** If `M` is totally regular,
`prodI M S · |F| ^ R_I ≤ |F| ^ (n²)`. -/
theorem prodI_mul_pow_le {M : Matrix (Fin n) (Fin n) F} (hM : TotallyRegular M)
    (S : Finset (Wire (n * n + n * n) s)) (out : Fin (n * n) → Wire (n * n + n * n) s) :
    prodI M S out *
        Fintype.card F ^ chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) ≤
      Fintype.card F ^ (n * n) := by
  have h := prod_mul_pow_le _ _ _ _ _ _
    (fun i => card_supportedKernel_vecMul_mul_pow_le hM (rowSet (place (matMulTermA n s) S) i)
      (rowSet (place (matMulTermC out) S) i)ᶜ)
    (fun i => card_supportedKernel_vecMul_mul_pow_le hM (rowSet (place (matMulTermA n s) S) i)ᶜ
      (rowSet (place (matMulTermC out) S) i))
  rwa [sum_card_add_card_compl, sum_min_eq_chargeI] at h

/-- **Totally regular columns.** If `M` is totally regular,
`prodK M S · |F| ^ R_K ≤ |F| ^ (n²)`. -/
theorem prodK_mul_pow_le {M : Matrix (Fin n) (Fin n) F} (hM : TotallyRegular M)
    (S : Finset (Wire (n * n + n * n) s)) (out : Fin (n * n) → Wire (n * n + n * n) s) :
    prodK M S out *
        Fintype.card F ^ chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
      Fintype.card F ^ (n * n) := by
  have h := prod_mul_pow_le _ _ _ _ _ _
    (fun k => card_supportedKernel_mul_pow_le hM (colSet (place (matMulTermB n s) S) k)
      (colSet (place (matMulTermC out) S) k)ᶜ)
    (fun k => card_supportedKernel_mul_pow_le hM (colSet (place (matMulTermB n s) S) k)ᶜ
      (colSet (place (matMulTermC out) S) k))
  rwa [sum_card_add_card_compl, sum_min_eq_chargeK] at h

/-- **A totally regular Hessian.** If `Λ` is totally regular,
`prodJ Λ S · |F| ^ R_J ≤ |F| ^ |X_T|`. -/
theorem prodJ_mul_pow_le {Λ : Matrix (Fin n) (Fin n) F} (hΛ : TotallyRegular Λ)
    (S : Finset (Wire (n * n + n * n) s)) :
    prodJ Λ S * Fintype.card F ^ chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) ≤
      Fintype.card F ^ (inputsIn S)ᶜ.card := by
  have h := prod_mul_pow_le _ _ _ _ _ _
    (fun j => card_supportedKernel_vecMul_mul_pow_le hΛ (colSet (place (matMulTermA n s) S) j)ᶜ
      (rowSet (place (matMulTermB n s) S) j))
    (fun j => card_supportedKernel_mul_pow_le hΛ (rowSet (place (matMulTermB n s) S) j)ᶜ
      (colSet (place (matMulTermA n s) S) j))
  rwa [← card_compl_inputsIn, sum_min_eq_chargeJ] at h

/-- **Uniform rows.** Some `B₀` has `prodI B₀ S · |F| ^ R_I ≤ |F| ^ (n² + 4 n)`. -/
theorem exists_prodI_mul_pow_le (S : Finset (Wire (n * n + n * n) s))
    (out : Fin (n * n) → Wire (n * n + n * n) s) :
    ∃ B₀ : Matrix (Fin n) (Fin n) F,
      prodI B₀ S out *
          Fintype.card F ^ chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) ≤
        Fintype.card F ^ (n * n + 4 * n) := by
  set R := fun i => rowSet (place (matMulTermA n s) S) i
  set C := fun i => rowSet (place (matMulTermC out) S) i
  obtain ⟨B₀, h⟩ := exists_prod_mul_pow_le (X := Matrix (Fin n) (Fin n) F) Fintype.one_lt_card
    (fun i B₀ => (supportedKernel (fun u => u ᵥ* B₀) (R i) (C i)ᶜ).card)
    (fun i B₀ => (supportedKernel (fun u => u ᵥ* B₀) (R i)ᶜ (C i)).card)
    (fun _ _ => card_supportedKernel_vecMul_pos _ _ _)
    (fun _ _ => card_supportedKernel_vecMul_pos _ _ _)
    (fun i => (R i).card) (fun i => ((R i)ᶜ).card)
    (fun i => min (R i).card ((C i)ᶜ).card) (fun i => min ((R i)ᶜ).card (C i).card)
    (fun _ => min_le_left _ _) (fun _ => min_le_left _ _)
    (fun _ => sum_card_supportedKernel_vecMul_mul_pow_le _ _)
    (fun _ => sum_card_supportedKernel_vecMul_mul_pow_le _ _)
  refine ⟨B₀, ?_⟩
  rwa [sum_card_add_card_compl, sum_min_eq_chargeI] at h

/-- **Uniform columns.** Some `A₀` has `prodK A₀ S · |F| ^ R_K ≤ |F| ^ (n² + 4 n)`. -/
theorem exists_prodK_mul_pow_le (S : Finset (Wire (n * n + n * n) s))
    (out : Fin (n * n) → Wire (n * n + n * n) s) :
    ∃ A₀ : Matrix (Fin n) (Fin n) F,
      prodK A₀ S out *
          Fintype.card F ^ chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
        Fintype.card F ^ (n * n + 4 * n) := by
  set R := fun k => colSet (place (matMulTermB n s) S) k
  set C := fun k => colSet (place (matMulTermC out) S) k
  obtain ⟨A₀, h⟩ := exists_prod_mul_pow_le (X := Matrix (Fin n) (Fin n) F) Fintype.one_lt_card
    (fun k A₀ => (supportedKernel (fun u => A₀ *ᵥ u) (R k) (C k)ᶜ).card)
    (fun k A₀ => (supportedKernel (fun u => A₀ *ᵥ u) (R k)ᶜ (C k)).card)
    (fun _ _ => card_supportedKernel_pos _ _ _)
    (fun _ _ => card_supportedKernel_pos _ _ _)
    (fun k => (R k).card) (fun k => ((R k)ᶜ).card)
    (fun k => min (R k).card ((C k)ᶜ).card) (fun k => min ((R k)ᶜ).card (C k).card)
    (fun _ => min_le_left _ _) (fun _ => min_le_left _ _)
    (fun _ => sum_card_supportedKernel_mul_pow_le _ _)
    (fun _ => sum_card_supportedKernel_mul_pow_le _ _)
  refine ⟨A₀, ?_⟩
  rwa [sum_card_add_card_compl, sum_min_eq_chargeK] at h

/-- **A uniform Hessian.** Some `Λ` has `prodJ Λ S · |F| ^ R_J ≤ |F| ^ (|X_T| + 4 n)`. -/
theorem exists_prodJ_mul_pow_le (S : Finset (Wire (n * n + n * n) s)) :
    ∃ Λ : Matrix (Fin n) (Fin n) F,
      prodJ Λ S * Fintype.card F ^ chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) ≤
        Fintype.card F ^ ((inputsIn S)ᶜ.card + 4 * n) := by
  set A := fun j => colSet (place (matMulTermA n s) S) j
  set B := fun j => rowSet (place (matMulTermB n s) S) j
  obtain ⟨Λ, h⟩ := exists_prod_mul_pow_le (X := Matrix (Fin n) (Fin n) F) Fintype.one_lt_card
    (fun j Λ => (supportedKernel (fun u => u ᵥ* Λ) (A j)ᶜ (B j)).card)
    (fun j Λ => (supportedKernel (fun u => Λ *ᵥ u) (B j)ᶜ (A j)).card)
    (fun _ _ => card_supportedKernel_vecMul_pos _ _ _)
    (fun _ _ => card_supportedKernel_pos _ _ _)
    (fun j => ((A j)ᶜ).card) (fun j => ((B j)ᶜ).card)
    (fun j => min ((A j)ᶜ).card (B j).card) (fun j => min ((B j)ᶜ).card (A j).card)
    (fun _ => min_le_left _ _) (fun _ => min_le_left _ _)
    (fun _ => sum_card_supportedKernel_vecMul_mul_pow_le _ _)
    (fun _ => sum_card_supportedKernel_mul_pow_le _ _)
  refine ⟨Λ, ?_⟩
  rwa [← card_compl_inputsIn, sum_min_eq_chargeJ] at h

variable {p : Program σ (n * n + n * n) s} {I : Interpretation σ F}
  {out : Fin (n * n) → Wire (n * n + n * n) s}

/-- **The three charges, with a totally regular matrix.** If `F` has a totally regular `n × n`
matrix, each charge of every split is at most the number of crossing signals. -/
theorem charges_le_of_totallyRegular (hf : ∀ z o, p.trace I z (out o) = matMul n z o)
    {M : Matrix (Fin n) (Fin n) F} (hM : TotallyRegular M) (S : Finset (Wire (n * n + n * n) s)) :
    chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) ≤
        (forward p S).card + (backward p S).card ∧
      chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) ≤
        (forward p S).card + (backward p S).card ∧
      chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
        (forward p S).card + (backward p S).card := by
  have hq := Fintype.one_lt_card (α := F)
  refine ⟨?_, ?_, ?_⟩
  · simpa using le_add_of_pow_le (L := 0) hq (pow_le_mul_prodI hf S M) (prodI_mul_pow_le hM S out)
  · simpa using le_add_of_pow_le (L := 0) hq (pow_le_mul_prodJ hf S M) (prodJ_mul_pow_le hM S)
  · simpa using le_add_of_pow_le (L := 0) hq (pow_le_mul_prodK hf S M) (prodK_mul_pow_le hM S out)

/-- **The three charges over every finite field.** Each charge of every split is at most the
number of crossing signals plus `4 n`. -/
theorem charges_le_add (hf : ∀ z o, p.trace I z (out o) = matMul n z o)
    (S : Finset (Wire (n * n + n * n) s)) :
    chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) ≤
        (forward p S).card + (backward p S).card + 4 * n ∧
      chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) ≤
        (forward p S).card + (backward p S).card + 4 * n ∧
      chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
        (forward p S).card + (backward p S).card + 4 * n := by
  have hq := Fintype.one_lt_card (α := F)
  obtain ⟨B₀, hB⟩ := exists_prodI_mul_pow_le (F := F) S out
  obtain ⟨Λ, hΛ⟩ := exists_prodJ_mul_pow_le (F := F) S
  obtain ⟨A₀, hA⟩ := exists_prodK_mul_pow_le (F := F) S out
  exact ⟨le_add_of_pow_le hq (pow_le_mul_prodI hf S B₀) hB,
    le_add_of_pow_le hq (pow_le_mul_prodJ hf S Λ) hΛ,
    le_add_of_pow_le hq (pow_le_mul_prodK hf S A₀) hA⟩

end Charges

end Algebraic.Cutwidth.MultiOutput.MatMul.Internal

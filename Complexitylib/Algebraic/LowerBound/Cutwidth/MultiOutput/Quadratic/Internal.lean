/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Proofs for quadratic forms

* *Sylvester's rank inequality* (`rank_add_rank_le_rank_mul_add_card`):
  `rank B + rank V ≤ rank (B V) + width B`, by rank–nullity for `B` restricted to the column
  space of `V`.
* *The product-class bound* (`card_mul_card_le_of_dotProduct_mulVec_eq_zero`): if
  `(l - l')ᵀ B (r - r') = 0` on `L × R`, let `V` have the columns `r - r₀`. Then `R` embeds
  in the column space of `V`, and the differences `l - l₀` lie in the kernel of `(B V)ᵀ`, so
  `|L| |R| ≤ |F| ^ (|ι| - rank (B V) + rank V) ≤ |F| ^ (|ι| + |κ| - rank B)`.
* *The mixed second difference* (`trace_add_trace_eq_trace_mix_add_trace_mix`,
  `quadForm_add_quadForm_eq`): by cut and paste, mixing two inputs with equal boundary keys
  only swaps the output values; writing each input as the sum of its parts on `X_S` and `X_T`
  (`mix S x 0 + mix S 0 x`), bilinearity leaves only the cross terms of the quadratic form.
* *The rank-cut bound* (`blockRank_add_transpose_le`): on a class of equal boundary keys,
  mixing two members realizes any left part with any right part (`SingleCut.mix_mem_filter`),
  so the parts satisfy the hypothesis of the product-class bound; summing over the at most
  `|F| ^ (|A| + |B|)` classes and comparing exponents gives `rank ≤ |A| + |B|`. Only the
  vanishing of the mixed second difference is used (`blockRank_add_transpose_le_of_mix`), so the
  bound also holds when a combination of several output wires is the quadratic form
  (`blockRank_add_transpose_le_of_sum`).
* *Symmetric Cauchy matrices* (`totallyRegular_hankelCauchyZMod_add_transpose`): `M + Mᵀ = 2 M`
  for symmetric `M`, and scaling a square block by `2 ≠ 0` keeps it nonsingular.
* *The finite bound* (`half_le_of_quadForm`): the component of an input wire is closed, so the
  rank-cut bound and total regularity put every input into it
  (`input_mem_component_of_quadForm`). Along the ranking of `MultiOutput.exists_rank`, the
  number of inputs in a prefix grows by at most one per wire, so the prefix ending at some input
  holds exactly `⌊N/2⌋` inputs; it is crossed by at least `⌊N/2⌋` signals and charged to the
  component holding all inputs.
* *The asymptotic bound* (`eventually_lt_size_of_quadForm_of_orderingBound`): assume at most
  `(1 + 1/(2A) - ε) N` gates and choose `η = A² ε`; the cycle term is then at most
  `(1/2 - A ε/2) N`, and the logarithmic term is `O(log N)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Matrix Filter Module

variable {σ : Signature} {n s : Nat}

/-! ## Linear algebra -/

section LinearAlgebra

variable {F : Type*} [Field F]

/-- **Sylvester's rank inequality.** For a matrix `B` with columns indexed by `κ` and a matrix
`V` with rows indexed by `κ`, `rank B + rank V ≤ rank (B V) + |κ|`. -/
theorem rank_add_rank_le_rank_mul_add_card {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (B : Matrix ι κ F) (V : Matrix κ μ F) :
    B.rank + V.rank ≤ (B * V).rank + Fintype.card κ := by
  classical
  set D := LinearMap.range V.mulVecLin
  let f := B.mulVecLin.domRestrict D
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrange : LinearMap.range f = LinearMap.range (B * V).mulVecLin := by
    rw [LinearMap.range_domRestrict, Matrix.mulVecLin_mul, LinearMap.range_comp]
  have hker : finrank F (LinearMap.ker f) ≤ finrank F (LinearMap.ker B.mulVecLin) := by
    rw [← Submodule.finrank_map_subtype_eq D (LinearMap.ker f)]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨v, hv, rfl⟩
    simpa [f] using hv
  have hB := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hB
  rw [hrange] at hrn
  change finrank F (LinearMap.range (B * V).mulVecLin) + _ = finrank F D at hrn
  change finrank F (LinearMap.range B.mulVecLin) + finrank F D ≤
    finrank F (LinearMap.range (B * V).mulVecLin) + _
  omega

/-- The kernel of a matrix has dimension `width - rank`. -/
theorem finrank_ker_mulVecLin {ι κ : Type*} [Fintype κ] (A : Matrix ι κ F) :
    finrank F (LinearMap.ker A.mulVecLin) = Fintype.card κ - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  change A.rank + _ = _ at h
  omega

section Finite

variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- A submodule of a finite space over a finite field has `|F| ^ finrank` elements. -/
theorem card_filter_mem_submodule {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (P : Submodule F V) [DecidablePred (· ∈ P)] :
    (Finset.univ.filter (· ∈ P)).card = Fintype.card F ^ finrank F P := by
  rw [← Module.card_eq_pow_finrank (K := F) (V := P), Fintype.card_subtype]

/-- **The product-class bound.** If `(l - l') ⬝ B (r - r') = 0` for all `l, l' ∈ L` and
`r, r' ∈ R`, then `|L| |R| ≤ |F| ^ (|ι| + |κ| - rank B)`. -/
theorem card_mul_card_le_of_dotProduct_mulVec_eq_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ F) (L : Finset (ι → F)) (R : Finset (κ → F))
    (h : ∀ l ∈ L, ∀ l' ∈ L, ∀ r ∈ R, ∀ r' ∈ R, (l - l') ⬝ᵥ (B *ᵥ (r - r')) = 0) :
    L.card * R.card ≤ Fintype.card F ^ (Fintype.card ι + Fintype.card κ - B.rank) := by
  classical
  rcases L.eq_empty_or_nonempty with hL | ⟨l₀, hl₀⟩
  · simp [hL]
  rcases R.eq_empty_or_nonempty with hR | ⟨r₀, hr₀⟩
  · simp [hR]
  -- The columns `r - r₀` of `V` span the differences of `R`.
  let V : Matrix κ ↥R F := Matrix.of fun k r => (r.1 - r₀) k
  have hV : ∀ r (hr : r ∈ R), V *ᵥ Pi.single ⟨r, hr⟩ 1 = r - r₀ := by
    intro r hr
    funext k
    simp [V]
  have hRcard : R.card ≤ Fintype.card F ^ V.rank := by
    rw [Matrix.rank, ← card_filter_mem_submodule (LinearMap.range V.mulVecLin)]
    refine Finset.card_le_card_of_injOn (fun r => r - r₀) (fun r hr => ?_)
      (fun r _ r' _ hrr => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact ⟨Pi.single ⟨r, hr⟩ 1, hV r hr⟩
    · exact sub_left_injective hrr
  -- The differences of `L` lie in the kernel of `(B V)ᵀ`.
  have hLcard : L.card ≤ Fintype.card F ^ (Fintype.card ι - (B * V).rank) := by
    rw [← Matrix.rank_transpose (B * V), ← finrank_ker_mulVecLin,
      ← card_filter_mem_submodule (LinearMap.ker (B * V)ᵀ.mulVecLin)]
    refine Finset.card_le_card_of_injOn (fun l => l - l₀) (fun l hl => ?_)
      (fun l _ l' _ hll => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext r
      rw [Matrix.mulVec_transpose, Pi.zero_apply]
      have := h l hl l₀ hl₀ r.1 r.2 r₀ hr₀
      rw [← hV r.1 r.2, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at this
      simpa [dotProduct_single] using this
    · exact sub_left_injective hll
  have hsyl := rank_add_rank_le_rank_mul_add_card B V
  have hG : (B * V).rank ≤ Fintype.card ι := Matrix.rank_le_card_height _
  calc L.card * R.card ≤ Fintype.card F ^ (Fintype.card ι - (B * V).rank) *
        Fintype.card F ^ V.rank := Nat.mul_le_mul hLcard hRcard
    _ = Fintype.card F ^ (Fintype.card ι - (B * V).rank + V.rank) := (pow_add _ _ _).symm
    _ ≤ Fintype.card F ^ (Fintype.card ι + Fintype.card κ - B.rank) :=
        Nat.pow_le_pow_right Fintype.card_pos (by omega)

end Finite

end LinearAlgebra

/-! ## The mixed second difference -/

section Mix

/-- **Values on a class are additive under mixing.** If two inputs have the same boundary key,
the values of any wire at the two inputs sum to its values at the two mixed inputs: the mixed
second difference vanishes. -/
theorem trace_add_trace_eq_trace_mix_add_trace_mix {U : Type*} [AddCommMonoid U]
    (p : Program σ n s) (I : Interpretation σ U) {S : Finset (Wire n s)} {x x' : Fin n → U}
    (h : boundaryKey p I S x = boundaryKey p I S x') (w : Wire n s) :
    p.trace I x w + p.trace I x' w = p.trace I (mix S x x') w + p.trace I (mix S x' x) w := by
  rw [trace_mix p I (agree_forward_of_boundaryKey_eq h) (agree_backward_of_boundaryKey_eq h),
    trace_mix p I (agree_forward_of_boundaryKey_eq h.symm)
      (agree_backward_of_boundaryKey_eq h.symm)]
  split_ifs
  · rfl
  · exact add_comm _ _

variable {F : Type*} [CommRing F]

/-- A sum over the inputs placed in `S` is a full sum with the other terms zeroed. -/
theorem sum_inputsIn_eq (S : Finset (Wire n s)) (g : Fin n → F) :
    ∑ i : ↥(inputsIn S), g i = ∑ i, if Wire.input i ∈ S then g i else 0 := by
  rw [Finset.sum_coe_sort (inputsIn S) g, inputsIn, Finset.sum_filter]

/-- A sum over the inputs placed outside `S` is a full sum with the other terms zeroed. -/
theorem sum_inputsIn_compl_eq (S : Finset (Wire n s)) (g : Fin n → F) :
    ∑ j : ↥(inputsIn S)ᶜ, g j = ∑ j, if Wire.input j ∈ S then 0 else g j := by
  rw [Finset.sum_coe_sort (inputsIn S)ᶜ g, inputsIn, Finset.compl_filter, Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp_all

/-- **The mixed second difference of a quadratic form** is the bilinear cross term
`(x_S - x'_S)ᵀ (M + Mᵀ)[X_S, X_T] (x_T - x'_T)`. -/
theorem quadForm_add_quadForm_eq (M : Matrix (Fin n) (Fin n) F) (S : Finset (Wire n s))
    (x x' : Fin n → F) :
    quadForm M x + quadForm M x' = quadForm M (mix S x x') + quadForm M (mix S x' x) +
      (leftPart S x - leftPart S x') ⬝ᵥ
        ((M + Mᵀ).submatrix (fun i : ↥(inputsIn S) => (i : Fin n))
          (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)) *ᵥ (rightPart S x - rightPart S x')) := by
  have hsplit : ∀ y y' : Fin n → F, mix S y y' = mix S y 0 + mix S 0 y' := by
    intro y y'
    funext j
    simp only [mix, Pi.add_apply, Pi.zero_apply]
    split_ifs <;> simp
  have hself : ∀ y : Fin n → F, y = mix S y 0 + mix S 0 y := by
    intro y
    rw [← hsplit]
    funext j
    simp only [mix]
    split_ifs <;> rfl
  have key : ∀ a b a' b' : Fin n → F, quadForm M (a + b) + quadForm M (a' + b') =
      quadForm M (a + b') + quadForm M (a' + b) + (a - a') ⬝ᵥ ((M + Mᵀ) *ᵥ (b - b')) := by
    intro a b a' b'
    have htrans : (a - a') ⬝ᵥ (Mᵀ *ᵥ (b - b')) = (b - b') ⬝ᵥ (M *ᵥ (a - a')) := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
    rw [Matrix.add_mulVec, dotProduct_add, htrans]
    simp only [quadForm, dotProduct_add, add_dotProduct, Matrix.mulVec_add, dotProduct_sub,
      sub_dotProduct, Matrix.mulVec_sub]
    ring
  have hconv : (mix S x 0 - mix S x' 0) ⬝ᵥ ((M + Mᵀ) *ᵥ (mix S 0 x - mix S 0 x')) =
      (leftPart S x - leftPart S x') ⬝ᵥ
        ((M + Mᵀ).submatrix (fun i : ↥(inputsIn S) => (i : Fin n))
          (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)) *ᵥ (rightPart S x - rightPart S x')) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, leftPart, rightPart,
      Pi.sub_apply]
    rw [sum_inputsIn_eq S fun i => (x i - x' i) * ∑ j : ↥(inputsIn S)ᶜ,
      (M + Mᵀ) i j * (x j - x' j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_inputsIn_compl_eq S fun j => (M + Mᵀ) i j * (x j - x' j)]
    by_cases hi : Wire.input i ∈ S
    · simp only [mix, hi, ite_true, Pi.zero_apply]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : Wire.input j ∈ S <;> simp [hj]
    · simp [mix, hi]
  rw [hsplit x x', hsplit x' x, ← hconv]
  conv_lhs => rw [hself x, hself x']
  exact key _ _ _ _

end Mix

/-! ## The rank-cut bound for quadratic forms -/

section RankCut

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Classes are isotropic.** If the quadratic form of `M` is additive under mixing inputs with
equal boundary keys, then on the inputs with a given key any two left parts and any two right
parts satisfy `(l - l')ᵀ (M + Mᵀ)[X_S, X_T] (r - r') = 0`. -/
theorem dotProduct_mulVec_eq_zero_of_mix (p : Program σ n s) (I : Interpretation σ F)
    (M : Matrix (Fin n) (Fin n) F) (S : Finset (Wire n s))
    (hmix : ∀ x x', boundaryKey p I S x = boundaryKey p I S x' →
      quadForm M x + quadForm M x' = quadForm M (mix S x x') + quadForm M (mix S x' x))
    {κ : (↥(forward p S) → F) × (↥(backward p S) → F)}
    {l l' : ↥(inputsIn S) → F} (hl : l ∈ leftParts p I S Finset.univ κ)
    (hl' : l' ∈ leftParts p I S Finset.univ κ) {r r' : ↥(inputsIn S)ᶜ → F}
    (hr : r ∈ rightParts p I S Finset.univ κ) (hr' : r' ∈ rightParts p I S Finset.univ κ) :
    (l - l') ⬝ᵥ ((M + Mᵀ).submatrix (fun i : ↥(inputsIn S) => (i : Fin n))
      (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)) *ᵥ (r - r')) = 0 := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hl'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hr'
  have hZ : ∀ x ∈ (Finset.univ : Finset (Fin n → F)), ∀ x' ∈ (Finset.univ : Finset (Fin n → F)),
      boundaryKey p I S x = boundaryKey p I S x' → mix S x x' ∈ Finset.univ :=
    fun _ _ _ _ _ => Finset.mem_univ _
  have hu := mix_mem_filter p I hZ hx hy
  have hu' := mix_mem_filter p I hZ hx' hy'
  have hkey : boundaryKey p I S (mix S x y) = boundaryKey p I S (mix S x' y') :=
    (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hu').2.symm
  have h₁ := hmix _ _ hkey
  have h₂ := quadForm_add_quadForm_eq M S (mix S x y) (mix S x' y')
  rw [leftPart_mix, leftPart_mix, rightPart_mix, rightPart_mix] at h₂
  linear_combination h₁ - h₂

/-- **Classes are isotropic.** On the inputs with a given boundary key, any two left parts and
any two right parts satisfy `(l - l')ᵀ (M + Mᵀ)[X_S, X_T] (r - r') = 0`, when a wire carries
the quadratic form of `M`. -/
theorem dotProduct_mulVec_eq_zero_of_mem_parts (p : Program σ n s) (I : Interpretation σ F)
    (out : Wire n s) (M : Matrix (Fin n) (Fin n) F) (hf : ∀ x, p.trace I x out = quadForm M x)
    (S : Finset (Wire n s)) {κ : (↥(forward p S) → F) × (↥(backward p S) → F)}
    {l l' : ↥(inputsIn S) → F} (hl : l ∈ leftParts p I S Finset.univ κ)
    (hl' : l' ∈ leftParts p I S Finset.univ κ) {r r' : ↥(inputsIn S)ᶜ → F}
    (hr : r ∈ rightParts p I S Finset.univ κ) (hr' : r' ∈ rightParts p I S Finset.univ κ) :
    (l - l') ⬝ᵥ ((M + Mᵀ).submatrix (fun i : ↥(inputsIn S) => (i : Fin n))
      (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)) *ᵥ (r - r')) = 0 :=
  dotProduct_mulVec_eq_zero_of_mix p I M S (fun x x' h => by
    rw [← hf, ← hf, ← hf, ← hf]
    exact trace_add_trace_eq_trace_mix_add_trace_mix p I h out) hl hl' hr hr'

/-- **The rank-cut bound for quadratic forms additive under mixing.** If the quadratic form of
`M` is additive under mixing inputs with equal boundary keys for the split `S`, then
`rank (M + Mᵀ)[X_S, X_T] ≤ |A| + |B|`. -/
theorem blockRank_add_transpose_le_of_mix (p : Program σ n s) (I : Interpretation σ F)
    (M : Matrix (Fin n) (Fin n) F) (S : Finset (Wire n s))
    (hmix : ∀ x x', boundaryKey p I S x = boundaryKey p I S x' →
      quadForm M x + quadForm M x' = quadForm M (mix S x x') + quadForm M (mix S x' x)) :
    blockRank (M + Mᵀ) (inputsIn S) (inputsIn S)ᶜ ≤ (forward p S).card + (backward p S).card := by
  set B := (M + Mᵀ).submatrix (fun i : ↥(inputsIn S) => (i : Fin n))
    (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)) with hB
  have hZ : ∀ x ∈ (Finset.univ : Finset (Fin n → F)), ∀ x' ∈ (Finset.univ : Finset (Fin n → F)),
      boundaryKey p I S x = boundaryKey p I S x' → mix S x x' ∈ Finset.univ :=
    fun _ _ _ _ _ => Finset.mem_univ _
  have hcard : Fintype.card ↥(inputsIn S) + Fintype.card ↥(inputsIn S)ᶜ = n := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_add_card_compl, Fintype.card_fin]
  have hclass : ∀ κ, (leftParts p I S Finset.univ κ).card * (rightParts p I S Finset.univ κ).card
      ≤ Fintype.card F ^ (n - B.rank) := by
    intro κ
    have := card_mul_card_le_of_dotProduct_mulVec_eq_zero B (leftParts p I S Finset.univ κ)
      (rightParts p I S Finset.univ κ) fun l hl l' hl' r hr r' hr' =>
        dotProduct_mulVec_eq_zero_of_mix p I M S hmix hl hl' hr hr'
    rwa [hcard] at this
  have h : Fintype.card F ^ n ≤
      Fintype.card F ^ ((forward p S).card + (backward p S).card) *
        Fintype.card F ^ (n - B.rank) := by
    calc Fintype.card F ^ n = (Finset.univ : Finset (Fin n → F)).card := by simp
      _ = ∑ κ ∈ Finset.univ.image (boundaryKey p I S),
            (Finset.univ.filter fun x => boundaryKey p I S x = κ).card :=
          Finset.card_eq_sum_card_image _ _
      _ = ∑ κ ∈ Finset.univ.image (boundaryKey p I S),
            (leftParts p I S Finset.univ κ).card * (rightParts p I S Finset.univ κ).card :=
          Finset.sum_congr rfl fun κ _ => card_filter_boundaryKey_eq p I hZ κ
      _ ≤ ∑ _κ ∈ Finset.univ.image (boundaryKey p I S), Fintype.card F ^ (n - B.rank) :=
          Finset.sum_le_sum fun κ _ => hclass κ
      _ = (Finset.univ.image (boundaryKey p I S)).card * Fintype.card F ^ (n - B.rank) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Fintype.card F ^ ((forward p S).card + (backward p S).card) *
            Fintype.card F ^ (n - B.rank) :=
          Nat.mul_le_mul_right _ (card_image_boundaryKey_le p I S Finset.univ)
  rw [← pow_add] at h
  have hexp := (Nat.pow_le_pow_iff_right (Fintype.one_lt_card (α := F))).mp h
  have hrank : B.rank ≤ n := (Matrix.rank_le_card_width B).trans (by omega)
  change B.rank ≤ _
  omega

/-- **The rank-cut bound for quadratic forms.** If the wire `out` of a program over a finite
field carries the quadratic form of `M`, then every split `S` has
`rank (M + Mᵀ)[X_S, X_T] ≤ |A| + |B|`. -/
theorem blockRank_add_transpose_le (p : Program σ n s) (I : Interpretation σ F) (out : Wire n s)
    (M : Matrix (Fin n) (Fin n) F) (hf : ∀ x, p.trace I x out = quadForm M x)
    (S : Finset (Wire n s)) :
    blockRank (M + Mᵀ) (inputsIn S) (inputsIn S)ᶜ ≤ (forward p S).card + (backward p S).card :=
  blockRank_add_transpose_le_of_mix p I M S fun x x' h => by
    rw [← hf, ← hf, ← hf, ← hf]
    exact trace_add_trace_eq_trace_mix_add_trace_mix p I h out

/-- **The rank-cut bound for a combination of outputs.** If the combination
`∑ o, coeff o · out o` of output wires of a program over a finite field is the quadratic form of
`M`, then every split `S` has `rank (M + Mᵀ)[X_S, X_T] ≤ |A| + |B|`: the mixed second difference
vanishes on every class for each output wire, hence for the combination. -/
theorem blockRank_add_transpose_le_of_sum {m : Nat} (p : Program σ n s) (I : Interpretation σ F)
    (out : Fin m → Wire n s) (coeff : Fin m → F) (M : Matrix (Fin n) (Fin n) F)
    (hf : ∀ x, ∑ o, coeff o * p.trace I x (out o) = quadForm M x) (S : Finset (Wire n s)) :
    blockRank (M + Mᵀ) (inputsIn S) (inputsIn S)ᶜ ≤ (forward p S).card + (backward p S).card :=
  blockRank_add_transpose_le_of_mix p I M S fun x x' h => by
    rw [← hf, ← hf, ← hf, ← hf, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← mul_add, ← mul_add, trace_add_trace_eq_trace_mix_add_trace_mix p I h (out o)]

end RankCut

/-! ## Symmetric totally regular matrices -/

section Symmetric

variable {F : Type*} [Field F]

/-- If `M` is symmetric and totally regular and `2 ≠ 0`, then `M + Mᵀ = 2 M` is totally
regular. -/
theorem totallyRegular_add_transpose {N : Nat} {M : Matrix (Fin N) (Fin N) F}
    (hM : TotallyRegular M) (hsymm : Mᵀ = M) (h2 : (2 : F) ≠ 0) : TotallyRegular (M + Mᵀ) := by
  intro k r c hr hc
  have hsub : (M + Mᵀ).submatrix r c = (2 : F) • M.submatrix r c := by
    ext i j
    simp [hsymm, two_mul]
  rw [hsub, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ h2) (hM k r c hr hc)

/-- The Hankel Cauchy matrix is the Cauchy matrix with nodes `x i = i + 1` and
`y j = -(j + 1)`. -/
theorem hankelCauchyZMod_eq_cauchy (q N : Nat) [Fact q.Prime] :
    hankelCauchyZMod q N =
      cauchy (fun i : Fin N => ((i : Nat) + 1 : ZMod q)) fun j => -((j : Nat) + 1 : ZMod q) := by
  ext i j
  simp only [hankelCauchyZMod, cauchy, Matrix.of_apply]
  congr 1
  push_cast
  ring

/-- **The Hankel Cauchy matrix is totally regular** over `ZMod q` for a prime `q > 2 N`. -/
theorem totallyRegular_hankelCauchyZMod (q N : Nat) [Fact q.Prime] (hq : 2 * N < q) :
    TotallyRegular (hankelCauchyZMod q N) := by
  have hcast : ∀ a b : Nat, a < q → b < q → (a : ZMod q) = b → a = b := by
    intro a b ha hb h
    have := (ZMod.natCast_eq_natCast_iff' a b q).mp h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  rw [hankelCauchyZMod_eq_cauchy]
  refine totallyRegular_cauchy _ _ (fun i i' h => ?_) (fun j j' h => ?_) fun i j h => ?_
  · have h' : (((i : Nat) + 1 : Nat) : ZMod q) = (((i' : Nat) + 1 : Nat) : ZMod q) := by
      push_cast
      exact h
    have := hcast _ _ (by omega) (by omega) h'
    exact Fin.ext (by omega)
  · have h' : (((j : Nat) + 1 : Nat) : ZMod q) = (((j' : Nat) + 1 : Nat) : ZMod q) := by
      push_cast
      exact neg_inj.mp h
    have := hcast _ _ (by omega) (by omega) h'
    exact Fin.ext (by omega)
  · have h' : (((i : Nat) + j + 2 : Nat) : ZMod q) = ((0 : Nat) : ZMod q) := by
      push_cast
      linear_combination h
    have := hcast _ _ (by omega) (by omega) h'
    omega

/-- **The symmetrized Hankel Cauchy matrix is totally regular** over `ZMod q` for a prime
`q > 2 N`: it is twice a symmetric totally regular matrix, and `2 ≠ 0` as `q` is odd. -/
theorem totallyRegular_hankelCauchyZMod_add_transpose (q N : Nat) [Fact q.Prime]
    (hq : 2 * N < q) :
    TotallyRegular (hankelCauchyZMod q N + (hankelCauchyZMod q N)ᵀ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · intro k r c hr hc
    cases k with
    | zero => simp
    | succ k => exact (r 0).elim0
  refine totallyRegular_add_transpose (totallyRegular_hankelCauchyZMod q N hq) ?_ ?_
  · ext i j
    simp only [hankelCauchyZMod, Matrix.transpose_apply, Matrix.of_apply]
    congr 2
    omega
  · intro h
    have h' : ((2 : Nat) : ZMod q) = ((0 : Nat) : ZMod q) := by
      push_cast
      exact h
    have := (ZMod.natCast_eq_natCast_iff' 2 0 q).mp h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
    omega

end Symmetric

/-! ## The finite bound -/

section Finite

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **All inputs lie in one component.** If `M + Mᵀ` is totally regular, the component of an
input wire contains every input: it is closed, hence crossed by no signal, so by the rank-cut
bound its inputs form a block of rank zero. -/
theorem input_mem_component_of_quadForm (p : Program σ n s) (I : Interpretation σ F)
    (out : Wire n s) {M : Matrix (Fin n) (Fin n) F} (hM : TotallyRegular (M + Mᵀ))
    (hf : ∀ x, p.trace I x out = quadForm M x) (j j' : Fin n) :
    Wire.input j' ∈ component p (Wire.input j) := by
  set W := component p (Wire.input j)
  have hclosed := component_closed p (Wire.input j)
  have hzero := blockRank_add_transpose_le p I out M hf W
  rw [forward_eq_empty_of_closed hclosed, backward_eq_empty_of_closed hclosed] at hzero
  have hmin := min_card_le_blockRank hM (inputsIn W) (inputsIn W)ᶜ
  have hjW : j ∈ inputsIn W := mem_inputsIn.mpr (mem_component_self p _)
  have hpos := Finset.card_pos.mpr ⟨j, hjW⟩
  have hcompl : (inputsIn W)ᶜ.card = 0 := by
    simp only [Finset.card_empty, add_zero] at hzero
    omega
  by_contra hj'
  have hmem : j' ∈ (inputsIn W)ᶜ := Finset.mem_compl.mpr fun h => hj' (mem_inputsIn.mp h)
  rw [Finset.card_eq_zero.mp hcompl] at hmem
  exact Finset.notMem_empty _ hmem

/-- **The finite bound for quadratic forms.** A fan-in-two program over any signature whose
wire `out` carries the quadratic form of `M`, with `M + Mᵀ` totally regular, has
`⌊N/2⌋ ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`. -/
theorem half_le_of_quadForm {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {N s : Nat} (p : Program σ N s)
    (hp : p.FanInAtMost 2) (I : Interpretation σ F) (out : Wire N s)
    {M : Matrix (Fin N) (Fin N) F} (hM : TotallyRegular (M + Mᵀ))
    (hf : ∀ x, p.trace I x out = quadForm M x) :
    ((N / 2 : Nat) : ℝ) ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C := by
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 ((N : ℝ) + 3 * s) := by
    rcases Nat.eq_zero_or_pos (N + 3 * s) with h | h
    · have : ((N : ℝ) + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - N) 0 := mul_nonneg hAη (le_max_right _ _)
  rcases Nat.eq_zero_or_pos (N / 2) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    linarith
  -- The ranking, and the prefix holding `⌊N/2⌋` inputs.
  obtain ⟨rank, hrank, hlt, hbound⟩ := exists_rank hAη order p hp
  let τ : Nat → Nat := fun t => (inputsIn (prefixBelow rank t)).card
  have hτ0 : τ 0 = 0 := by
    simp [τ, inputsIn, prefixBelow]
  have hτT : N / 2 ≤ τ (N + s) := by
    have hall : prefixBelow rank (N + s) = Finset.univ := by
      ext w
      simp [prefixBelow, hlt w]
    have huniv : inputsIn (Finset.univ : Finset (Wire N s)) = Finset.univ := by
      ext j
      simp [mem_inputsIn]
    show N / 2 ≤ (inputsIn (prefixBelow rank (N + s))).card
    rw [hall, huniv, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, hτt, hτt1⟩ := exists_cross τ hτ0 hpos (N + s) hτT
  have hstep := card_inputsIn_prefixBelow_succ_le rank hrank t
  have hτeq : (inputsIn (prefixBelow rank (t + 1))).card = N / 2 := by
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
  have hcut := blockRank_add_transpose_le p I out M hf S
  have hmin := min_card_le_blockRank hM (inputsIn S) (inputsIn S)ᶜ
  have hXc : (inputsIn S)ᶜ.card = N - N / 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hτeq]
  rw [hτeq, hXc] at hmin
  have hlower : N / 2 ≤ (forward p S).card + (backward p S).card := by
    have : min (N / 2) (N - N / 2) = N / 2 := min_eq_left (by omega)
    omega
  -- The upper bound at the prefix, charged to the component holding all inputs.
  have hupper := hbound (Wire.input j₀)
  have hinputs : (inputsIn (component p (Wire.input j₀))).card = N := by
    have : inputsIn (component p (Wire.input j₀)) = Finset.univ := by
      ext j
      simp only [mem_inputsIn, Finset.mem_univ, iff_true]
      exact input_mem_component_of_quadForm p I out hM hf j₀ j
    rw [this, Finset.card_univ, Fintype.card_fin]
  rw [← hprefix, hinputs] at hupper
  have hgates : ((gatesIn (component p (Wire.input j₀))).card : ℝ) ≤ s := by
    exact_mod_cast (by simpa using Finset.card_le_univ (gatesIn (component p (Wire.input j₀))))
  have hmax : (A + η) * max (((gatesIn (component p (Wire.input j₀))).card : ℝ) - N) 0 ≤
      (A + η) * max ((s : ℝ) - N) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hAη
  have hlowerR : ((N / 2 : Nat) : ℝ) ≤
      (((forward p S).card + (backward p S).card : Nat) : ℝ) := by
    exact_mod_cast hlower
  linarith

end Finite

/-! ## Asymptotics -/

universe u v

/-- **The asymptotic bound for quadratic forms** with a general ordering coefficient. -/
theorem eventually_lt_size_of_quadForm_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular (M + Mᵀ) →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N 1),
        c.FanInAtMost 2 → c.Computes I (fun x _ => quadForm M x) →
          (1 + 1 / (2 * A) - ε) * N < c.size := by
  set ε' := min ε (1 / (2 * A)) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 1 / (2 * A) := min_le_right _ _
  set η := A ^ 2 * ε' with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  set B : ℝ := 4 + 3 / (2 * A) with hB
  have hBpos : 0 < B := by positivity
  filter_upwards [eventually_mul_logb_add_lt 3 (3 * Real.logb 2 B + C + 1)
    (show 0 < A * ε' / 2 by positivity), eventually_ge_atTop 1] with N hlog hN1
  intro F _ _ _ M hM σ I c hfan hc
  by_contra hs
  rw [not_lt] at hs
  have hs' : (c.size : ℝ) ≤ (1 + 1 / (2 * A) - ε') * N :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have core := half_le_of_quadForm hAη hC c.program hfan I (c.outputs 0) hM
    (fun x => congrFun (hc x) 0)
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- `⌊N/2⌋ ≥ (N - 1)/2`.
  have hhalf : ((N : ℝ) - 1) / 2 ≤ ((N / 2 : Nat) : ℝ) := by
    have h₁ : N ≤ 2 * (N / 2) + 1 := by omega
    have h₂ : (N : ℝ) ≤ 2 * ((N / 2 : Nat) : ℝ) + 1 := by exact_mod_cast h₁
    linarith
  -- The cycle-rank term.
  have hrest : 0 ≤ (1 / (2 * A) - ε') * N := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((c.size : ℝ) - N) 0 ≤ (1 / (2 * A) - ε') * N :=
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
  have hprod : (A + η) * max ((c.size : ℝ) - N) 0 ≤ (1 / 2 - A * ε' / 2) * N := by
    calc (A + η) * max ((c.size : ℝ) - N) 0 ≤ (A + η) * ((1 / (2 * A) - ε') * N) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (1 / (2 * A) - ε') * N := by ring
      _ ≤ (1 / 2 - A * ε' / 2) * N := mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- The logarithmic term.
  have hVle : (N : ℝ) + 3 * c.size ≤ B * N := by
    have h₁ : (1 + 1 / (2 * A) - ε') * (N : ℝ) ≤ (1 + 1 / (2 * A)) * N :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (N : ℝ) = N + 3 * ((1 + 1 / (2 * A)) * N) := by
      rw [hB]
      ring
    linarith
  have hVpos : (0 : ℝ) < N + 3 * c.size := by positivity
  have hlogV : Real.logb 2 ((N : ℝ) + 3 * c.size) ≤ Real.logb 2 B + Real.logb 2 N := by
    calc Real.logb 2 ((N : ℝ) + 3 * c.size) ≤ Real.logb 2 (B * N) :=
          (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVle
      _ = Real.logb 2 B + Real.logb 2 N := Real.logb_mul hBpos.ne' (by positivity)
  have hsplit : (1 / 2 - A * ε' / 2) * (N : ℝ) = N / 2 - A * ε' / 2 * N := by ring
  linarith

end Algebraic.Cutwidth.MultiOutput.Internal

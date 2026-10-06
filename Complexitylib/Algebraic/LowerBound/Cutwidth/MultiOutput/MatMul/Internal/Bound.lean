/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Internal.Component
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.PolyMul.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Arithmetic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian

/-!
# The size bounds for matrix multiplication

* **The finite bound** (`sq_sub_le_of_charges`). Suppose every split has total charge at most
  three times its crossing signals plus `3 L`. Along the ranking of `MultiOutput.exists_rank`,
  the threshold prefix of `Tripartite.exists_threshold` ends at a terminal and satisfies
  `3 n² ≤ 2 (R_I + R_J + R_K) + 3` (`Tripartite.three_mul_sq_le_two_mul_charge`), so it is
  crossed by at least `(n² - 2 L - 1)/2` signals. It is charged to the component holding all
  terminals (`mem_component_of_trace`), which has `2 n²` inputs and at most `s` gates. With a
  totally regular matrix `L = 0` (`half_sq_le_of_totallyRegular`); over every finite field
  `L = 4 n` (`sq_sub_le`); for polynomial gates over any field `K`, evaluating over `K(t)` with
  the generic Hankel matrix gives `L = 0` (`half_sq_le_of_formallyComputes`).
* **The asymptotic bound** (`eventually_lt_size_of_orderingBound_matMul`,
  `eventually_lt_size_of_orderingBound_matMul_polynomial`). Assume at most
  `(2 + 1/(2A) - ε) n²` gates and choose `η = A² ε`; the cycle term is then at most
  `(1/2 - A ε/2) n²`, while the loss `4 n` and the logarithmic term are `o(n²)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.Internal

open Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Tripartite Filter

variable {σ : Signature} {n s : Nat}

/-! ## The finite bound -/

section Finite

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- **The finite bound from the charges.** If every split of a fan-in-two program whose wires
`out` carry `matMul n` has total charge at most three times its crossing signals plus `3 L`,
then `(n² - 2 L - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem sq_sub_le_of_charges {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (p : Program σ (n * n + n * n) s)
    (hp : p.FanInAtMost 2) (I : Interpretation σ F) (out : Fin (n * n) → Wire (n * n + n * n) s)
    (hf : ∀ z o, p.trace I z (out o) = matMul n z o) (L : Nat)
    (hcharge : ∀ S : Finset (Wire (n * n + n * n) s),
      chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) +
          chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) +
          chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
        3 * ((forward p S).card + (backward p S).card) + 3 * L) :
    ((n : ℝ) ^ 2 - 2 * L - 1) / 2 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 (2 * (n : ℝ) ^ 2 + 3 * s) := by
    rcases Nat.eq_zero_or_pos (2 * n ^ 2 + 3 * s) with h | h
    · have : (2 * (n : ℝ) ^ 2 + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 := mul_nonneg hAη (le_max_right _ _)
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have h0 : (n : ℝ) ^ 2 = 0 := by
      rw [hn]
      norm_num
    have hneg : ((n : ℝ) ^ 2 - 2 * L - 1) / 2 < 0 := by
      rw [h0]
      linarith
    exact hneg.le.trans (add_nonneg (add_nonneg hmax0 (by linarith)) hC)
  -- All terminals lie in one component, on distinct wires.
  obtain ⟨hin, houtW⟩ := mem_component_of_trace hn hf
  set W₀ := component p (out (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩)) with hW₀
  have hterm := terminal_injective hf
  -- The ranking and the threshold prefix.
  obtain ⟨rank, hrank, hlt, hbound⟩ := exists_rank hAη order p hp
  obtain ⟨t, ⟨x, hx⟩, hlo, hhi⟩ :=
    exists_threshold hn (matMulTermA n s) (matMulTermB n s) (matMulTermC out) hterm rank hrank _ hlt
  set S := prefixBelow rank (t + 1) with hS
  set w₀ := Sum.elim (matMulTermA n s) (Sum.elim (matMulTermB n s) (matMulTermC out)) x with hw₀def
  have hprefix : S = prefixUpTo rank w₀ := by
    ext v
    simp only [hS, prefixBelow, prefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and, hx]
    omega
  have hw₀ : w₀ ∈ W₀ := by
    rcases x with q | q | q
    · exact hin _
    · exact hin _
    · exact houtW _
  have hcomp : component p w₀ = W₀ := component_eq_of_mem hw₀
  have hinputs : (inputsIn W₀).card = n * n + n * n := by
    have : inputsIn W₀ = Finset.univ := by
      ext k
      simp [mem_inputsIn, hin k]
    rw [this, Finset.card_univ, Fintype.card_fin]
  have hupper := hbound w₀
  rw [← hprefix, hcomp, hinputs] at hupper
  -- The charging inequality at the threshold prefix.
  have hsq := three_mul_sq_le_two_mul_charge _ _ _ hlo hhi
  have hch := hcharge S
  have hlower : n ^ 2 ≤ 2 * ((forward p S).card + (backward p S).card) + 2 * L + 1 := by
    omega
  have hgates : ((gatesIn W₀).card : ℝ) ≤ s := by
    exact_mod_cast (by simpa using Finset.card_le_univ (gatesIn W₀))
  have hNR : ((n * n + n * n : Nat) : ℝ) = 2 * (n : ℝ) ^ 2 := by
    push_cast
    ring
  rw [hNR] at hupper
  have hmax : (A + η) * max (((gatesIn W₀).card : ℝ) - 2 * n ^ 2) 0 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hAη
  have hlowerR : ((n : ℝ) ^ 2 - 2 * L - 1) / 2 ≤
      (((forward p S).card + (backward p S).card : Nat) : ℝ) := by
    have : ((n ^ 2 : Nat) : ℝ) ≤
        ((2 * ((forward p S).card + (backward p S).card) + 2 * L + 1 : Nat) : ℝ) := by
      exact_mod_cast hlower
    push_cast at this ⊢
    linarith
  linarith

/-- **The finite bound with a totally regular matrix.** A fan-in-two program over a finite field
with a totally regular `n × n` matrix, whose wires `out` carry `matMul n`, has
`(n² - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem half_sq_le_of_totallyRegular {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {M : Matrix (Fin n) (Fin n) F}
    (hM : TotallyRegular M) (p : Program σ (n * n + n * n) s) (hp : p.FanInAtMost 2)
    (I : Interpretation σ F) (out : Fin (n * n) → Wire (n * n + n * n) s)
    (hf : ∀ z o, p.trace I z (out o) = matMul n z o) :
    ((n : ℝ) ^ 2 - 1) / 2 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  have h := sq_sub_le_of_charges hAη order p hp I out hf 0 fun S => by
    obtain ⟨h₁, h₂, h₃⟩ := charges_le_of_totallyRegular hf hM S
    omega
  simpa using h

/-- **The finite bound over every finite field.** A fan-in-two program over any finite field
whose wires `out` carry `matMul n` has
`(n² - 8 n - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem sq_sub_le {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    (p : Program σ (n * n + n * n) s) (hp : p.FanInAtMost 2) (I : Interpretation σ F)
    (out : Fin (n * n) → Wire (n * n + n * n) s)
    (hf : ∀ z o, p.trace I z (out o) = matMul n z o) :
    ((n : ℝ) ^ 2 - 8 * n - 1) / 2 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  have h := sq_sub_le_of_charges hAη order p hp I out hf (4 * n) fun S => by
    obtain ⟨h₁, h₂, h₃⟩ := charges_le_add hf S
    omega
  push_cast at h
  linarith

end Finite

/-! ## Polynomial gates over arbitrary fields -/

section Polynomial

open Matrix

/-- Evaluating the formal matrix product at a point of an algebra gives the matrix product. -/
theorem aeval_matMul_X {K R : Type*} [CommSemiring K] [CommSemiring R] [Algebra K R]
    (z : Fin (n * n + n * n) → R) (o : Fin (n * n)) :
    MvPolynomial.aeval z
      (matMul n (MvPolynomial.X : Fin (n * n + n * n) → MvPolynomial (Fin (n * n + n * n)) K) o) =
      matMul n z o := by
  simp [matMul]

/-- Evaluating the formal matrix product at a point gives the matrix product. -/
theorem eval_matMul_X {K : Type*} [CommSemiring K] (z : Fin (n * n + n * n) → K)
    (o : Fin (n * n)) :
    MvPolynomial.eval z
      (matMul n (MvPolynomial.X : Fin (n * n + n * n) → MvPolynomial (Fin (n * n + n * n)) K) o) =
      matMul n z o := by
  simp [matMul]

/-- Every output entry of matrix multiplication is a nonconstant function. -/
theorem matMul_nonconstant {K : Type*} [Field K] (o : Fin (n * n)) :
    ∃ x y : Fin (n * n + n * n) → K, matMul n x o ≠ matMul n y o := by
  set i := (finProdFinEquiv.symm o).1
  set k := (finProdFinEquiv.symm o).2
  refine ⟨0, matMulInput 1 (Matrix.single i k 1), ?_⟩
  rw [output_eq o, matMul_output, matMul_matMulInput]
  simp [i, k]

/-- **Subspace decomposition across totally regular blocks.** -/
theorem finrank_add_sum_min_le {L : Type*} [Field L] {ι : Type*} [Fintype ι] {N : Nat}
    (U : Submodule L (Fin N → L)) (coord : ι → Fin n → Fin N)
    (hinj : ∀ u ∈ U, (∀ t j, u (coord t j) = 0) → u = 0)
    (M : ι → Matrix (Fin n) (Fin n) L) (hM : ∀ t, TotallyRegular (M t))
    (P Q : ι → Finset (Fin n))
    (hsupp : ∀ u ∈ U, ∀ t, ∀ j, j ∉ P t → u (coord t j) = 0)
    (hker : ∀ u ∈ U, ∀ t, ∀ k ∈ Q t, (M t *ᵥ fun j => u (coord t j)) k = 0) :
    Module.finrank L U + ∑ t : ι, min (P t).card (Q t).card ≤ ∑ t : ι, (P t).card := by
  classical
  set K : ι → Submodule L (Fin n → L) :=
    fun t => U.map (LinearMap.funLeft L L (coord t))
  let Φ : ↥U →ₗ[L] ∀ t : ι, ↥(K t) :=
    { toFun := fun u t => ⟨fun j => u.1 (coord t j), Submodule.mem_map_of_mem u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦ : Function.Injective Φ := by
    intro u u' h
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine hinj (u.1 - u'.1) (U.sub_mem u.2 u'.2) fun t j => ?_
    have htj := congrFun (congrArg Subtype.val (congrFun h t)) j
    simpa [Φ, sub_eq_zero] using htj
  have hU : Module.finrank L U ≤ ∑ t : ι, Module.finrank L (K t) := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hΦ
    rwa [Module.finrank_pi_fintype] at h1
  have hK : ∀ t : ι, Module.finrank L (K t) + min (P t).card (Q t).card ≤ (P t).card := by
    intro t
    have h1 := Taylor.Internal.finrank_add_blockRank_le (M t) (Q t) (P t) (K t)
      (by rintro _ ⟨u, hu, rfl⟩ j hj; exact hsupp u hu t j hj)
      (by rintro _ ⟨u, hu, rfl⟩ k hk; exact hker u hu t k hk)
    have h2 : min (P t).card (Q t).card ≤ blockRank (M t) (Q t) (P t) := by
      rw [min_comm]
      exact min_card_le_blockRank (hM t) (Q t) (P t)
    omega
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hK t
  rw [Finset.sum_add_distrib] at hsum
  omega

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
  (p : Program σ (n * n + n * n) s) (out : Fin (n * n) → Wire (n * n + n * n) s)

/-- At `A = 0, B = M`, the Jacobian of formal matrix multiplication sends a direction `v`
supported on `A` to `C i k = ∑ j, v (A i j) M j k`. -/
theorem jacobian_matMulInput_zero_right
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o)
    (M : Matrix (Fin n) (Fin n) L) {v : Fin (n * n + n * n) → L}
    (hv : ∀ x, x ∉ leftCoords n → v x = 0) (i k : Fin n) :
    (Taylor.jacobian (Taylor.wirePolynomial P p) (matMulInput 0 M) *ᵥ v)
      (out (matMulOutput n i k)) = (Mᵀ *ᵥ fun j => v (matMulLeft n i j)) k := by
  change ∑ x, MvPolynomial.aeval (matMulInput 0 M)
    (MvPolynomial.pderiv x (Taylor.wirePolynomial P p (out (matMulOutput n i k)))) * v x = _
  have h := congrArg TrivSqZeroExt.snd (Taylor.Internal.aeval_inl_add_inr
    (Taylor.wirePolynomial P p (out (matMulOutput n i k))) (matMulInput 0 M) v)
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h
  rw [← h, hf, aeval_matMul_X, matMul_output, TrivSqZeroExt.snd_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [matMulInput_left, Matrix.zero_apply, matMulInput_right,
    hv _ (matMulRight_notMem_leftCoords j k)]
  simp [mul_comm]

/-- At `A = M, B = 0`, the Jacobian of formal matrix multiplication sends a direction `v`
supported on `B` to `C i k = ∑ j, M i j v (B j k)`. -/
theorem jacobian_matMulInput_zero_left
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o)
    (M : Matrix (Fin n) (Fin n) L) {v : Fin (n * n + n * n) → L}
    (hv : ∀ x, x ∉ rightCoords n → v x = 0) (i k : Fin n) :
    (Taylor.jacobian (Taylor.wirePolynomial P p) (matMulInput M 0) *ᵥ v)
      (out (matMulOutput n i k)) = (M *ᵥ fun j => v (matMulRight n j k)) i := by
  change ∑ x, MvPolynomial.aeval (matMulInput M 0)
    (MvPolynomial.pderiv x (Taylor.wirePolynomial P p (out (matMulOutput n i k)))) * v x = _
  have h := congrArg TrivSqZeroExt.snd (Taylor.Internal.aeval_inl_add_inr
    (Taylor.wirePolynomial P p (out (matMulOutput n i k))) (matMulInput M 0) v)
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h
  rw [← h, hf, aeval_matMul_X, matMul_output, TrivSqZeroExt.snd_sum]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [matMulInput_left, matMulInput_right, Matrix.zero_apply,
    hv _ (matMulLeft_notMem_rightCoords i j)]
  simp

/-- The Hessian of the output `C i k` of formal matrix multiplication, as a bilinear form. -/
theorem dotProduct_hessian_matMulOutput
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o)
    (v u : Fin (n * n + n * n) → L) (i k : Fin n) :
    v ⬝ᵥ (Taylor.hessian (Taylor.wirePolynomial P p (out (matMulOutput n i k))) 0 *ᵥ u) =
      ∑ j, (v (matMulLeft n i j) * u (matMulRight n j k) +
        u (matMulLeft n i j) * v (matMulRight n j k)) := by
  have h := congrArg (fun z : DualNumber (DualNumber L) => z.snd.snd)
    (Taylor.Internal.aeval_jet
      (Taylor.wirePolynomial P p (out (matMulOutput n i k))) 0 v u)
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h
  rw [← h, hf, aeval_matMul_X, matMul_output, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Taylor.Internal.jet, Pi.zero_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    add_zero, DualNumber.snd_mul, mul_zero, zero_add]

omit [Field K] [Algebra K L] in
/-- The symmetrized bilinear form of `M` is the `M`-weighted sum of the output Hessian forms. -/
theorem dotProduct_bilinForm_add_transpose (M : Matrix (Fin n) (Fin n) L)
    (v u : Fin (n * n + n * n) → L) :
    v ⬝ᵥ ((bilinForm M + (bilinForm M)ᵀ) *ᵥ u) =
      ∑ i, ∑ k, M i k * ∑ j, (v (matMulLeft n i j) * u (matMulRight n j k) +
        u (matMulLeft n i j) * v (matMulRight n j k)) := by
  rw [dotProduct, sum_input]
  simp only [mulVec_add_transpose_left, mulVec_add_transpose_right, Finset.mul_sum,
    mul_add, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  · rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The charge `R_I` for polynomial gates.** With a totally regular matrix `M` over an
extension field, `R_I` is at most the number of forward and backward signals. -/
theorem chargeI_le_of_formallyComputes_of_totallyRegular
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o)
    {M : Matrix (Fin n) (Fin n) L} (hM : TotallyRegular M)
    (S : Finset (Wire (n * n + n * n) s)) :
    chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) ≤
      (forward p S).card + (backward p S).card := by
  set J := Taylor.jacobian (Taylor.wirePolynomial P p) (matMulInput 0 M)
  set V₁ := Taylor.Internal.matSubKer J (inputsIn S ∩ leftCoords n) (forward p S)
  set W₁ := Taylor.Internal.matSubKer J ((inputsIn S)ᶜ ∩ leftCoords n) (backward p S)
  have hdimV : (inputsIn S ∩ leftCoords n).card ≤ Module.finrank L V₁ + (forward p S).card :=
    Taylor.Internal.card_le_finrank_matSubKer_add J (inputsIn S ∩ leftCoords n) (forward p S)
  have hdimW : ((inputsIn S)ᶜ ∩ leftCoords n).card ≤ Module.finrank L W₁ + (backward p S).card :=
    Taylor.Internal.card_le_finrank_matSubKer_add J ((inputsIn S)ᶜ ∩ leftCoords n) (backward p S)
  have hcard : (inputsIn S ∩ leftCoords n).card + ((inputsIn S)ᶜ ∩ leftCoords n).card = n * n :=
    (card_inter_add_card_compl_inter (inputsIn S) (leftCoords n)).trans card_leftCoords
  have hV_left : ∀ v ∈ V₁, ∀ x, x ∉ leftCoords n → v x = 0 := fun v hv x hx =>
    Taylor.Internal.support_of_mem_matSubKer hv fun h => hx (Finset.mem_inter.mp h).2
  have hW_left : ∀ u ∈ W₁, ∀ x, x ∉ leftCoords n → u x = 0 := fun u hu x hx =>
    Taylor.Internal.support_of_mem_matSubKer hu fun h => hx (Finset.mem_inter.mp h).2
  have h₁ := finrank_add_sum_min_le V₁ (fun i j => matMulLeft n i j)
    (fun v hv h => by
      funext x
      rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
      · exact h i j
      · exact hV_left v hv _ (matMulRight_notMem_leftCoords j k))
    (fun _ => Mᵀ) (fun _ => totallyRegular_transpose hM)
    (fun i => rowSet (place (matMulTermA n s) S) i)
    (fun i => (rowSet (place (matMulTermC out) S) i)ᶜ)
    (fun v hv i j hj => Taylor.Internal.support_of_mem_matSubKer hv fun h =>
      hj ((mem_rowSet_placeA S).mpr (Finset.mem_inter.mp h).1))
    (fun v hv i k hk => by
      rw [← jacobian_matMulInput_zero_right P p out hf M (hV_left v hv) i k]
      have hout : out (matMulOutput n i k) ∉ S := by
        simpa [mem_rowSet_placeC, outputsIn] using hk
      exact Taylor.Internal.jacobian_mulVec_eq_zero_of_forward P p S (matMulInput 0 M)
        (fun x hx => Taylor.Internal.support_of_mem_matSubKer hv
          fun h => hx (Finset.mem_inter.mp h).1)
        (fun _ hc => Taylor.Internal.mulVec_eq_zero_of_mem_matSubKer hv hc) hout)
  have h₂ := finrank_add_sum_min_le W₁ (fun i j => matMulLeft n i j)
    (fun u hu h => by
      funext x
      rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
      · exact h i j
      · exact hW_left u hu _ (matMulRight_notMem_leftCoords j k))
    (fun _ => Mᵀ) (fun _ => totallyRegular_transpose hM)
    (fun i => (rowSet (place (matMulTermA n s) S) i)ᶜ)
    (fun i => rowSet (place (matMulTermC out) S) i)
    (fun u hu i j hj => Taylor.Internal.support_of_mem_matSubKer hu fun h =>
      hj (Finset.mem_compl.mpr fun hA => (Finset.mem_compl.mp (Finset.mem_inter.mp h).1)
        ((mem_rowSet_placeA S).mp hA)))
    (fun u hu i k hk => by
      rw [← jacobian_matMulInput_zero_right P p out hf M (hW_left u hu) i k]
      have hout : out (matMulOutput n i k) ∈ S := by
        simpa [mem_rowSet_placeC, outputsIn] using hk
      exact Taylor.Internal.jacobian_mulVec_eq_zero_of_backward P p S (matMulInput 0 M)
        (fun x hx => Taylor.Internal.support_of_mem_matSubKer hu
          fun h => (Finset.mem_compl.mp (Finset.mem_inter.mp h).1) hx)
        (fun _ hc => Taylor.Internal.mulVec_eq_zero_of_mem_matSubKer hu hc) hout)
  have hsum_min := sum_min_eq_chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S)
  have hsum_card := sum_card_add_card_compl (fun i => rowSet (place (matMulTermA n s) S) i)
  rw [Finset.sum_add_distrib] at hsum_min hsum_card
  omega

/-- **The charge `R_K` for polynomial gates.** With a totally regular matrix `M` over an
extension field, `R_K` is at most the number of forward and backward signals. -/
theorem chargeK_le_of_formallyComputes_of_totallyRegular
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o)
    {M : Matrix (Fin n) (Fin n) L} (hM : TotallyRegular M)
    (S : Finset (Wire (n * n + n * n) s)) :
    chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
      (forward p S).card + (backward p S).card := by
  set J := Taylor.jacobian (Taylor.wirePolynomial P p) (matMulInput M 0)
  set V₂ := Taylor.Internal.matSubKer J (inputsIn S ∩ rightCoords n) (forward p S)
  set W₂ := Taylor.Internal.matSubKer J ((inputsIn S)ᶜ ∩ rightCoords n) (backward p S)
  have hdimV : (inputsIn S ∩ rightCoords n).card ≤ Module.finrank L V₂ + (forward p S).card :=
    Taylor.Internal.card_le_finrank_matSubKer_add J (inputsIn S ∩ rightCoords n) (forward p S)
  have hdimW : ((inputsIn S)ᶜ ∩ rightCoords n).card ≤ Module.finrank L W₂ + (backward p S).card :=
    Taylor.Internal.card_le_finrank_matSubKer_add J ((inputsIn S)ᶜ ∩ rightCoords n) (backward p S)
  have hcard : (inputsIn S ∩ rightCoords n).card + ((inputsIn S)ᶜ ∩ rightCoords n).card = n * n :=
    (card_inter_add_card_compl_inter (inputsIn S) (rightCoords n)).trans card_rightCoords
  have hV_right : ∀ v ∈ V₂, ∀ x, x ∉ rightCoords n → v x = 0 := fun v hv x hx =>
    Taylor.Internal.support_of_mem_matSubKer hv fun h => hx (Finset.mem_inter.mp h).2
  have hW_right : ∀ u ∈ W₂, ∀ x, x ∉ rightCoords n → u x = 0 := fun u hu x hx =>
    Taylor.Internal.support_of_mem_matSubKer hu fun h => hx (Finset.mem_inter.mp h).2
  have h₁ := finrank_add_sum_min_le V₂ (fun k j => matMulRight n j k)
    (fun v hv h => by
      funext x
      rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
      · exact hV_right v hv _ (matMulLeft_notMem_rightCoords i j)
      · exact h k j)
    (fun _ => M) (fun _ => hM)
    (fun k => colSet (place (matMulTermB n s) S) k)
    (fun k => (colSet (place (matMulTermC out) S) k)ᶜ)
    (fun v hv k j hj => Taylor.Internal.support_of_mem_matSubKer hv fun h =>
      hj ((mem_colSet_placeB S).mpr (Finset.mem_inter.mp h).1))
    (fun v hv k i hi => by
      rw [← jacobian_matMulInput_zero_left P p out hf M (hV_right v hv) i k]
      have hout : out (matMulOutput n i k) ∉ S := by
        simpa [mem_colSet_placeC, outputsIn] using hi
      exact Taylor.Internal.jacobian_mulVec_eq_zero_of_forward P p S (matMulInput M 0)
        (fun x hx => Taylor.Internal.support_of_mem_matSubKer hv
          fun h => hx (Finset.mem_inter.mp h).1)
        (fun _ hc => Taylor.Internal.mulVec_eq_zero_of_mem_matSubKer hv hc) hout)
  have h₂ := finrank_add_sum_min_le W₂ (fun k j => matMulRight n j k)
    (fun u hu h => by
      funext x
      rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
      · exact hW_right u hu _ (matMulLeft_notMem_rightCoords i j)
      · exact h k j)
    (fun _ => M) (fun _ => hM)
    (fun k => (colSet (place (matMulTermB n s) S) k)ᶜ)
    (fun k => colSet (place (matMulTermC out) S) k)
    (fun u hu k j hj => Taylor.Internal.support_of_mem_matSubKer hu fun h =>
      hj (Finset.mem_compl.mpr fun hB => (Finset.mem_compl.mp (Finset.mem_inter.mp h).1)
        ((mem_colSet_placeB S).mp hB)))
    (fun u hu k i hi => by
      rw [← jacobian_matMulInput_zero_left P p out hf M (hW_right u hu) i k]
      have hout : out (matMulOutput n i k) ∈ S := by
        simpa [mem_colSet_placeC, outputsIn] using hi
      exact Taylor.Internal.jacobian_mulVec_eq_zero_of_backward P p S (matMulInput M 0)
        (fun x hx => Taylor.Internal.support_of_mem_matSubKer hu
          fun h => (Finset.mem_compl.mp (Finset.mem_inter.mp h).1) hx)
        (fun _ hc => Taylor.Internal.mulVec_eq_zero_of_mem_matSubKer hu hc) hout)
  have hsum_min := sum_min_eq_chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S)
  have hsum_card := sum_card_add_card_compl (fun k => colSet (place (matMulTermB n s) S) k)
  rw [Finset.sum_add_distrib] at hsum_min hsum_card
  omega

/-- **The charge `R_J` for polynomial gates.** With a totally regular matrix `M` over an
extension field, `R_J` is at most the number of forward and backward signals, by the Hessian
cut bound. -/
theorem chargeJ_le_of_formallyComputes_of_totallyRegular
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o)
    {M : Matrix (Fin n) (Fin n) L} (hM : TotallyRegular M)
    (S : Finset (Wire (n * n + n * n) s)) :
    chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) ≤
      (forward p S).card + (backward p S).card := by
  set H := bilinForm M + (bilinForm M)ᵀ
  set U := Taylor.Internal.matSubKer H (inputsIn S)ᶜ (inputsIn S)
  have hdimU : (inputsIn S)ᶜ.card ≤ Module.finrank L U + blockRank H (inputsIn S) (inputsIn S)ᶜ :=
    Taylor.Internal.card_le_finrank_matSubKer_add_rank H (inputsIn S)ᶜ (inputsIn S)
  have hrank : blockRank H (inputsIn S) (inputsIn S)ᶜ ≤
      (forward p S).card + (backward p S).card :=
    Taylor.Internal.blockRank_le_of_orthogonal P p S (0 : Fin _ → L) H fun v u h => by
      rw [dotProduct_bilinForm_add_transpose]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      rw [← dotProduct_hessian_matMulOutput P p out hf v u i k, h (out (matMulOutput n i k)),
        mul_zero]
  have h := finrank_add_sum_min_le (ι := Fin n ⊕ Fin n) U
    (Sum.elim (fun j i => matMulLeft n i j) (fun j k => matMulRight n j k))
    (fun u _ hu => by
      funext x
      rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
      · exact hu (Sum.inl j) i
      · exact hu (Sum.inr j) k)
    (Sum.elim (fun _ => Mᵀ) (fun _ => M))
    (fun t => by rcases t with j | j; exacts [totallyRegular_transpose hM, hM])
    (Sum.elim (fun j => (colSet (place (matMulTermA n s) S) j)ᶜ)
      (fun j => (rowSet (place (matMulTermB n s) S) j)ᶜ))
    (Sum.elim (fun j => rowSet (place (matMulTermB n s) S) j)
      (fun j => colSet (place (matMulTermA n s) S) j))
    (fun u hu t d hd => by
      rcases t with j | j
      · exact Taylor.Internal.support_of_mem_matSubKer hu fun h =>
          hd (Finset.mem_compl.mpr fun hA =>
            (Finset.mem_compl.mp h) ((mem_colSet_placeA S).mp hA))
      · exact Taylor.Internal.support_of_mem_matSubKer hu fun h =>
          hd (Finset.mem_compl.mpr fun hB =>
            (Finset.mem_compl.mp h) ((mem_rowSet_placeB S).mp hB)))
    (fun u hu t d hd => by
      rcases t with j | j
      · simp only [Sum.elim_inl, Matrix.mulVec, dotProduct, Matrix.transpose_apply] at hd ⊢
        have hright := Taylor.Internal.mulVec_eq_zero_of_mem_matSubKer hu
          ((mem_rowSet_placeB S).mp hd)
        rwa [mulVec_add_transpose_right] at hright
      · simp only [Sum.elim_inr, Matrix.mulVec, dotProduct] at hd ⊢
        have hleft := Taylor.Internal.mulVec_eq_zero_of_mem_matSubKer hu
          ((mem_colSet_placeA S).mp hd)
        rwa [mulVec_add_transpose_left] at hleft)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib,
    sum_min_eq_chargeJ, ← card_compl_inputsIn] at h
  omega

/-- **The three charges for polynomial gates over any field.** -/
theorem charges_le_of_formallyComputes
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o)
    (S : Finset (Wire (n * n + n * n) s)) :
    chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) ≤
        (forward p S).card + (backward p S).card ∧
      chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) ≤
        (forward p S).card + (backward p S).card ∧
      chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
        (forward p S).card + (backward p S).card := by
  have hM : TotallyRegular (hankel n fun m => (RatFunc.X : RatFunc K) ^ (m ^ 2)) :=
    PolyMul.Internal.totallyRegular_genericHankel
  exact ⟨chargeI_le_of_formallyComputes_of_totallyRegular P p out hf hM S,
    chargeJ_le_of_formallyComputes_of_totallyRegular P p out hf hM S,
    chargeK_le_of_formallyComputes_of_totallyRegular P p out hf hM S⟩

/-- **The finite bound for polynomial gates over any field.** -/
theorem half_sq_le_of_formallyComputes {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (hp : p.FanInAtMost 2)
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMul n MvPolynomial.X o) :
    ((n : ℝ) ^ 2 - 1) / 2 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  have htrace : ∀ (z : Fin (n * n + n * n) → RatFunc K) (o : Fin (n * n)),
      p.trace (Taylor.algebraInterpretation P (RatFunc K)) z (out o) = matMul n z o := by
    intro z o
    rw [Taylor.Internal.trace_eq_aeval_wirePolynomial, hf, aeval_matMul_X]
  have h := sq_sub_le_of_charges hAη order p hp
    (Taylor.algebraInterpretation P (RatFunc K)) out htrace 0 fun S => by
      obtain ⟨h₁, h₂, h₃⟩ := charges_le_of_formallyComputes P p out hf S
      omega
  simpa using h

end Polynomial

/-! ## Asymptotics -/

universe u v

/-- **The asymptotic bound from the finite inequality.** -/
theorem eventually_lt_of_sq_sub_le {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ s : Nat,
      (∀ η C : ℝ, 0 ≤ A + η → Multigraph.OrderingBound A η C →
        ((n : ℝ) ^ 2 - 8 * n - 1) / 2 ≤
          (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C) →
      (2 + 1 / (2 * A) - ε) * n ^ 2 < s := by
  set ε' := min ε (1 / (2 * A)) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 1 / (2 * A) := min_le_right _ _
  set η := A ^ 2 * ε' with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  set B : ℝ := 8 + 3 / (2 * A) with hB
  have hBpos : 0 < B := by positivity
  have hδ : 0 < A * ε' / 2 := by positivity
  filter_upwards [eventually_mul_logb_add_lt 6 (3 * Real.logb 2 B + C + 1) one_pos,
    eventually_ge_atTop 1, eventually_ge_atTop ⌈10 / (A * ε')⌉₊] with n hlog hn1 hnbig
  intro s bound
  by_contra hs
  rw [not_lt] at hs
  have hs' : (s : ℝ) ≤ (2 + 1 / (2 * A) - ε') * n ^ 2 :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have core := bound η C hAη hC
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnbig' : 10 / (A * ε') ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnbig)
  -- The cycle-rank term.
  have hrest : 0 ≤ (1 / (2 * A) - ε') * n ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((s : ℝ) - 2 * n ^ 2) 0 ≤ (1 / (2 * A) - ε') * n ^ 2 :=
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
  have hprod : (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 ≤ (1 / 2 - A * ε' / 2) * n ^ 2 := by
    calc (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 ≤ (A + η) * ((1 / (2 * A) - ε') * n ^ 2) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (1 / (2 * A) - ε') * n ^ 2 := by ring
      _ ≤ (1 / 2 - A * ε' / 2) * n ^ 2 := mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- The logarithmic term.
  have hVle : 2 * (n : ℝ) ^ 2 + 3 * s ≤ B * n ^ 2 := by
    have h₁ : (2 + 1 / (2 * A) - ε') * (n : ℝ) ^ 2 ≤ (2 + 1 / (2 * A)) * n ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (n : ℝ) ^ 2 = 2 * n ^ 2 + 3 * ((2 + 1 / (2 * A)) * n ^ 2) := by
      rw [hB]
      ring
    linarith
  have hVpos : (0 : ℝ) < 2 * n ^ 2 + 3 * s := by positivity
  have hlogV : Real.logb 2 (2 * (n : ℝ) ^ 2 + 3 * s) ≤ Real.logb 2 B + 2 * Real.logb 2 n := by
    calc Real.logb 2 (2 * (n : ℝ) ^ 2 + 3 * s) ≤ Real.logb 2 (B * n ^ 2) :=
          (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVle
      _ = Real.logb 2 B + 2 * Real.logb 2 n := by
          rw [Real.logb_mul hBpos.ne' (by positivity), Real.logb_pow]
          push_cast
          ring
  -- The quadratic gap beats the linear loss.
  have hgap : 5 * (n : ℝ) ≤ A * ε' / 2 * n ^ 2 := by
    have h₁ : 10 ≤ A * ε' * n := by
      rw [div_le_iff₀ (by positivity)] at hnbig'
      linarith
    nlinarith
  simp only [one_mul] at hlog
  nlinarith

/-- **The asymptotic bound for matrix multiplication** with a general ordering coefficient. -/
theorem eventually_lt_size_of_orderingBound_matMul {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → c.Computes I (matMul n) → (2 + 1 / (2 * A) - ε) * n ^ 2 < c.size := by
  filter_upwards [eventually_lt_of_sq_sub_le hA order hε] with n hn
  intro F _ _ σ I c hfan hc
  classical
  exact hn c.size fun η C hAη hC =>
    sq_sub_le hAη hC c.program hfan I c.outputs fun z o => congrFun (hc z) o

/-- **The asymptotic bound for polynomial gates over any field** with a general ordering
coefficient. -/
theorem eventually_lt_size_of_orderingBound_matMul_polynomial {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (K : Type u) [Field K] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
      (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (matMul n MvPolynomial.X) →
          (2 + 1 / (2 * A) - ε) * n ^ 2 < c.size := by
  filter_upwards [eventually_lt_of_sq_sub_le hA order hε] with n hn
  intro K _ σ P c hfan hc
  refine hn c.size fun η C hAη hC => ?_
  have h := half_sq_le_of_formallyComputes P c.program c.outputs hAη hC hfan hc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end Algebraic.Cutwidth.MultiOutput.MatMul.Internal

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.ClearedCircuit
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Exact Fourier circuits: fftcircuit

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/FFTCircuit.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- The exact radix-two DAG used for scalar convolution in the finite-win proof.
All multiplies by the roots and normalization scalars are charged. -/
namespace ExactFourier.RadixTwo
open scoped BigOperators

theorem exists_fft_dag (k : ℕ) (ω : ℂ) (hω : IsPrimitiveRoot ω (2^k)) :
    ∃ C : LinearDAG (2^k) (2^k), C.size ≤ 3*k*2^k ∧
      ∀ x, C.eval x = eval (2^k) ω x := by
  induction k generalizing ω with
  | zero =>
      refine ⟨LinearDAG.wires (fun i => i.castSucc), by simp [LinearDAG.wires], ?_⟩
      intro x
      funext i
      have hi : i = 0 := by
        apply Fin.ext
        have h := i.isLt
        simp only [pow_zero] at h
        omega
      simp [LinearDAG.eval_wires, eval, evalAt, hi]
  | succ k ih =>
      have hn : 0 < 2^k := pow_pos (by decide) _
      have hEq : 2^(k+1) = 2^k + 2^k := by rw [pow_succ]; omega
      have hs : IsPrimitiveRoot (ω^2) (2^k) :=
        IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ]; omega)
      have hh : ω^(2^k) = -1 :=
        (IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ])).eq_neg_one_of_two_right
      obtain ⟨C, hsize, heval⟩ := ih (ω^2) hs
      let D := ((C.withInputs (evenIndex (2^k))).fanout
        (C.withInputs (oddIndex (2^k)))).butterflies (fun i => ω^i.val)
      have hDsize : D.size ≤ 3*(k+1)*(2^k+2^k) := by
        simp only [D, LinearDAG.butterflies, LinearDAG.size_fanout,
          LinearDAG.size_withInputs]
        nlinarith
      have hDeval : ∀ x, D.eval x = eval (2^k+2^k) ω x := by
        intro x
        dsimp only [D]
        rw [LinearDAG.eval_butterflies]
        simp only [LinearDAG.eval_fanout]
        simp only [Fin.addCases_left, Fin.addCases_right,
          LinearDAG.eval_withInputs, heval]
        exact (eval_split (2^k) ω hh x).symm
      rw [hEq]
      exact ⟨D, hDsize, hDeval⟩

end ExactFourier.RadixTwo

end

section
/- The uniform scalar-convolution main dependency. All operations are charged;
truncated series and constants may vary with the requested length. -/
namespace ExactFourier.ScalarConvolution
open Polynomial CoefficientTime RadixTwo
open scoped BigOperators

/-- Select an input index when present and otherwise select the free zero wire. -/
def padIndex (t m : ℕ) (i : Fin m) : Fin (t+1) :=
  if h : i.val < t then (⟨i.val,h⟩ : Fin t).castSucc else Fin.last t

/-- Extend or truncate an input vector to the requested length using zeros. -/
def padded {t m : ℕ} (x : Fin t → ℂ) (i : Fin m) : ℂ :=
  if h : i.val < t then x ⟨i.val,h⟩ else 0

theorem eval_padding (t m : ℕ) (x : Fin t → ℂ) :
    (LinearDAG.wires (padIndex t m)).eval x = (padded x : Fin m → ℂ) := by
  funext i
  rw [LinearDAG.eval_wires]
  by_cases h : i.val < t
  · simp only [padIndex, dite_eq_left h, padded]
    exact @Fin.snoc_castSucc t (fun _ => ℂ) 0 x ⟨i.val,h⟩
  · simp only [padIndex, dite_eq_right h, padded, Fin.snoc_last]

theorem ofFn_padded {t m : ℕ} (htm : t ≤ m) (x : Fin t → ℂ) :
    Polynomial.ofFn m (padded x) = Polynomial.ofFn t x := by
  ext j
  by_cases hj : j < t
  · have hjm : j < m := hj.trans_le htm
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hjm,
      Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
    simp [padded, hj]
  · have hjt : t ≤ j := by omega
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hjt]
    by_cases hjm : j < m
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hjm]
      simp [padded, hj]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]

/-- A fixed diagonal layer charges exactly one multiplication per coordinate. -/
def diagonalDAG {m : ℕ} (c : Fin m → ℂ) : LinearDAG m m :=
  LinearDAG.layer (fun i => .scale (c i) i.castSucc)

theorem diagonalDAG_eval {m : ℕ} (c : Fin m → ℂ) (x : Fin m → ℂ) :
    (diagonalDAG c).eval x = fun i => c i * x i := by
  rw [diagonalDAG, LinearDAG.eval_layer]
  funext i
  simp [Gate.eval]

/-- Polynomial convolution on any containing radix-two length. -/
theorem convolution_dag_at_power (k t : ℕ) (ht : 0 < t) (htm : 2*t ≤ 2^k)
    (f : ℂ[X]) (hf : f.natDegree < t) :
    ∃ C : LinearDAG t t, C.size ≤ (6*k+1)*2^k ∧
      ∀ x i, C.eval x i = (f * Polynomial.ofFn t x).coeff i.val := by
  have hm : 0 < 2^k := pow_pos (by decide) _
  let ω := zeta (2^k)
  have hω : IsPrimitiveRoot ω (2^k) :=
    Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hm)
  obtain ⟨F, hFsize, hFeval⟩ := exists_fft_dag k ω hω
  obtain ⟨I, hIsize, hIeval⟩ := exists_fft_dag k ω⁻¹ hω.inv
  let c : Fin (2^k) → ℂ := fun i => (2^k : ℂ)⁻¹ * f.eval (ω^i.val)
  let D := I.comp ((diagonalDAG c).comp (F.comp (LinearDAG.wires (padIndex t (2^k)))))
  let out : Fin t → Fin (2^k) := fun i => ⟨i.val, by have := i.isLt; omega⟩
  refine ⟨D.withOutputs out, ?_, ?_⟩
  · change D.size ≤ _
    dsimp only [D, LinearDAG.comp, diagonalDAG, LinearDAG.layer, LinearDAG.wires]
    nlinarith
  · intro x i
    change D.eval x (out i) = _
    dsimp only [D]
    rw [LinearDAG.eval_comp, LinearDAG.eval_comp, LinearDAG.eval_comp,
      eval_padding, hFeval, diagonalDAG_eval, hIeval]
    have hev (j : Fin (2^k)) : eval (2^k) ω (padded x) j =
        (Polynomial.ofFn t x).eval (ω^j.val) := by
      rw [← eval_ofFn, ofFn_padded (by omega)]
    simp_rw [hev]
    have hfg : (f * Polynomial.ofFn t x).natDegree < 2^k := by
      have hx := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ t) x
      have hh := Polynomial.natDegree_mul_le (p := f) (q := Polynomial.ofFn t x)
      omega
    have hconv := convolution_formula hm ω hω f (Polynomial.ofFn t x) hfg
    simpa [c, out] using congrFun hconv (out i)

/-- Uniform linear-DAG construction, with logarithmic cost independent of coefficients. -/
theorem exists_truncation_dag (t : ℕ) (ht : 0 < t) (f : PowerSeries ℂ) :
    ∃ C : LinearDAG t t, C.size ≤ 52 * t * (Nat.log 2 t + 1) ∧
      ∀ x, C.eval x = (truncMatrix t f).mulVec x := by
  let k := Nat.log 2 t + 2
  have hl := Nat.pow_log_le_self 2 (Nat.ne_of_gt ht)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2) t
  have hsmall : 2*t ≤ 2^k := by
    dsimp [k]
    rw [pow_add]
    simp only [Nat.succ_eq_add_one, pow_add, pow_one] at hu
    norm_num at ⊢
    omega
  have hlarge : 2^k ≤ 4*t := by
    dsimp [k]
    rw [pow_add]
    norm_num
    omega
  have hdeg : (PowerSeries.trunc t f).natDegree < t := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
    exact PowerSeries.natDegree_trunc_lt f s
  obtain ⟨C, hC, hEval⟩ := convolution_dag_at_power k t ht hsmall
    (PowerSeries.trunc t f) hdeg
  refine ⟨C, ?_, ?_⟩
  · calc
      C.size ≤ (6*k+1)*2^k := hC
      _ ≤ (6*k+1)*(4*t) := Nat.mul_le_mul_left _ hlarge
      _ ≤ 52*t*(Nat.log 2 t+1) := by dsimp [k]; nlinarith
  · intro x
    funext i
    rw [hEval]
    rw [← Polynomial.coeff_coe, Polynomial.coe_mul, coeff_mul_truncated]
    simp only [Matrix.mulVec, dotProduct, truncMatrix]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j.val ≤ i.val
    · have hlt : i.val-j.val < t := by have := i.isLt; omega
      simp [hji, PowerSeries.coeff_trunc, hlt,
        Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt]
    · simp [hji]

/-- Inversion commutes exactly with truncated scalar multiplication. -/
theorem truncMatrix_inv (t : ℕ) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (truncMatrix t f)⁻¹ = truncMatrix t f⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← truncMatrix_mul, PowerSeries.mul_inv_cancel _ hf, truncMatrix_one]

theorem price_truncation_nat (p : MatrixPrice) (t : ℕ) (ht : 0 < t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (truncMatrix t f) ≤ 627 * (t : ℝ) * (Nat.log 2 t + 1) := by
  obtain ⟨C, hC, hCe⟩ := exists_truncation_dag t ht f
  obtain ⟨D, hD, hDe⟩ := exists_truncation_dag t ht f⁻¹
  have hU := trunc_isUnit t f (isUnit_iff_ne_zero.mpr hf)
  have hInv : ∀ x, D.eval x = (truncMatrix t f)⁻¹.mulVec x := by
    intro x
    rw [truncMatrix_inv t f hf]
    exact hDe x
  have hb := p.twoWay_DAG_bound (truncMatrix t f) hU C D hCe hInv
  have hc' : (C.size : ℝ) ≤ 52 * (t : ℝ) * (Nat.log 2 t + 1) := by exact_mod_cast hC
  have hd' : (D.size : ℝ) ≤ 52 * (t : ℝ) * (Nat.log 2 t + 1) := by exact_mod_cast hD
  have ht' : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hl' : (0 : ℝ) ≤ Nat.log 2 t := Nat.cast_nonneg _
  nlinarith

/-- The literal O(t log(2t)) estimate, with one absolute constant, uniform in f and t. -/
theorem price_truncation (p : MatrixPrice) (t : ℕ) (ht : 0 < t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (truncMatrix t f) ≤ (627 / Real.log 2) * (t : ℝ) * Real.log (2*t) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (2 : ℝ) ^ Nat.log 2 t ≤ t := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt ht)
  have hl : (Nat.log 2 t : ℝ) * Real.log 2 ≤ Real.log t := by
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) _) hp
  have hb : (Nat.log 2 t : ℝ)+1 ≤ Real.log (2*t) / Real.log 2 := by
    apply (le_div_iff₀ h2).mpr
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht')]
    linarith
  calc
    p.value (truncMatrix t f) ≤ 627*(t : ℝ)*(Nat.log 2 t+1) :=
      price_truncation_nat p t ht f hf
    _ ≤ 627*(t : ℝ)*(Real.log (2*t) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (627 / Real.log 2) * (t : ℝ) * Real.log (2*t) := by ring

end ExactFourier.ScalarConvolution

end

section
/- Unsigned scalar preprocessing and exact elimination of the cleared
initial-state response, using triangular monotonicity only. -/
namespace ExactFourier
open scoped Kronecker
open CoefficientTime TensorTools
namespace CoefficientTime
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem blockTrunc_smul_one (t : ℕ) (q : PowerSeries ℂ) :
    blockTruncHom t (q • (1 : Matrix α α (PowerSeries ℂ))) =
      truncMatrix t q ⊗ₖ (1 : Matrix α α ℂ) := by
  ext i j
  by_cases h : i.2=j.2 <;> by_cases ht : j.1.val ≤ i.1.val <;>
    simp [blockTruncHom_apply,truncMatrix,Matrix.kroneckerMap_apply,Matrix.one_apply,h,ht]

theorem scalar_correction
    {α : Type} {β : Type} [Fintype α]  [DecidableEq α]  (H : Matrix α α (PowerSeries ℂ))
    (E Q : Matrix α β (PowerSeries ℂ)) (q : PowerSeries ℂ)
    (hq : PowerSeries.constantCoeff q ≠ 0) (hQ : H*Q=q•E) (t : ℕ) :
    blockTruncHom t H * (truncMatrix t q⁻¹ ⊗ₖ (1 : Matrix α α ℂ)) *
      coefficientColumns t Q = coefficientColumns t E := by
  rw [← blockTrunc_smul_one,← map_mul,blocks_mul_columns,
    Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hQ,smul_smul,
    PowerSeries.inv_mul_cancel _ hq,one_smul]

end CoefficientTime
namespace MatrixPrice
variable (p : MatrixPrice) {α β : Type} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem eliminate_series (H : Matrix α α (PowerSeries ℂ))
    (E Q : Matrix α β (PowerSeries ℂ)) (q : PowerSeries ℂ) (t : ℕ)
    (K : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ)
    (hK : IsUnit K) (hH : IsUnit (H.map PowerSeries.constantCoeff))
    (hdata : K.toBlocks₁₁=blockTruncHom t H)
    (hstate : K.toBlocks₁₂=coefficientColumns t E)
    (hq : PowerSeries.constantCoeff q ≠ 0) (hQ : H*Q=q•E) :
    p.value (blockTruncHom t H) ≤ p.value K +
      2*(Fintype.card α : ℝ)*p.value (truncMatrix t q⁻¹) +
      p.value (rectangularShear (coefficientColumns t Q)) := by
  have hqi : PowerSeries.constantCoeff q⁻¹ ≠ 0 := by simpa using inv_ne_zero hq
  have hP := trunc_isUnit t q⁻¹ (isUnit_iff_ne_zero.mpr hqi)
  have he : Matrix.fromBlocks (blockTruncHom t H) (coefficientColumns t E)
      K.toBlocks₂₁ K.toBlocks₂₂ = K := by rw [← hdata,← hstate]; exact Matrix.fromBlocks_toBlocks K
  have h := p.eliminate_top_right (blockTruncHom t H)
    (truncMatrix t q⁻¹ ⊗ₖ (1 : Matrix α α ℂ)) (coefficientColumns t E) (coefficientColumns t Q)
    K.toBlocks₂₁ K.toBlocks₂₂ (he.symm ▸ hK) (blockTrunc_isUnit t H hH)
    (unit_tensor _ _ hP isUnit_one) (scalar_correction H E Q q hq hQ t)
  rw [he,p.tensor _ _ hP isUnit_one,p.one] at h
  simpa only [mul_zero,add_zero,mul_assoc] using h

end MatrixPrice
end ExactFourier

end

section
namespace ExactFourier
open scoped Kronecker
open TensorAxis CoefficientTime PolynomialDAG
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem q_constant (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hM : IsUnit M) (k : ℕ) :
    PowerSeries.constantCoeff (CellPoly.ps ((CellPoly.b M C B D)^k)) ≠ 0 := by
  have hd : M.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  simpa [Polynomial.coeff_zero_eq_eval_zero] using pow_ne_zero k hd

theorem coefficients_eq_columns {σ ρ : Type}
    (Q : Matrix σ ρ (Polynomial ℂ)) (t : ℕ) :
    coefficients Q t = coefficientColumns t (Q.map CellPoly.ps) := by
  ext i j
  simp [coefficients,coefficientColumns]

theorem uniform_bound (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hM : IsUnit M)
    (hK : IsUnit (Matrix.fromBlocks M C B D)) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ k t : ℕ, 0 < t →
      p.value (blockTruncHom t (power (CellSeries.transfer M C B D) k)) ≤
      (t : ℝ)*Fintype.card (Fibers α k)*p.value (Matrix.fromBlocks M C B D) +
      CK*((Fintype.card α : ℝ)^k*t*Real.log (2*t) + (k+1:ℝ)^3*Fintype.card α^k) := by
  obtain ⟨A,hA⟩ := exists_cleared_coeff_dag (CellPoly.b M C B D) (CellPoly.L M C B D)
    (CellPoly.T M C B D)
  let CK : ℝ := 1256 / Real.log 2 + 8*A
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨CK,by dsimp [CK]; positivity,?_⟩
  intro k t ht
  let H := power (CellSeries.transfer M C B D) k
  let E := response (CellSeries.transfer M C B D) (CellSeries.state C D) k
  let Q := cleared (CellPoly.b M C B D) (CellPoly.L M C B D) (CellPoly.T M C B D) k
  let q := CellPoly.ps ((CellPoly.b M C B D)^k)
  have hH : IsUnit (H.map PowerSeries.constantCoeff) := by
    dsimp only [H]
    rw [map_power,CellSeries.constant_transfer]
    exact unit_power M hM k
  have hq : PowerSeries.constantCoeff q ≠ 0 := q_constant M C B D hM k
  have hqi : PowerSeries.constantCoeff q⁻¹ ≠ 0 := by simpa using inv_ne_zero hq
  have helim := p.eliminate_series H E (Q.map CellPoly.ps) q t
    (run (Matrix.fromBlocks M C B D) t k) (unit _ hK t k) hH
    (data_block M C B D t k) (state_block M C B D t k) hq (cell_clearing M C B D k)
  obtain ⟨cq,hcq,heq⟩ := hA k t
  rw [coefficients_eq_columns] at heq
  have hshear := cq.shear_price p (coefficientColumns t (Q.map CellPoly.ps)) heq
  have hcq' : (cq.size : ℝ) ≤ (A : ℝ)*(k+1:ℝ)^3*Fintype.card α^k := by exact_mod_cast hcq
  have hprice := price p (Matrix.fromBlocks M C B D) hK t k
  have hp := ScalarConvolution.price_truncation p t ht q⁻¹ hqi
  have hN : (0:ℝ) ≤ Fintype.card (Space α k) := Nat.cast_nonneg _
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 2*Fintype.card (Space α k))
  rw [Fintype.card_prod,Fintype.card_fin,card_space] at hshear
  rw [card_space] at helim hp'
  push_cast at helim hshear hp'
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlog : Real.log 2 ≤ Real.log (2*(t : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hlog' : 1 ≤ Real.log (2*(t : ℝ)) / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hlog)
  have htn : (0:ℝ) ≤ (Fintype.card α : ℝ)^k*t := by positivity
  have hpad := mul_le_mul_of_nonneg_left hlog' (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) htn)
  have hlognn : 0 ≤ (Fintype.card α : ℝ)^k*t*Real.log (2*t) :=
    mul_nonneg htn (hl2.le.trans hlog)
  have hpoly : 0 ≤ (k+1:ℝ)^3*(Fintype.card α : ℝ)^k := by positivity
  change p.value (blockTruncHom t H) ≤ _
  dsimp [CK]
  have hdiv : (0:ℝ) ≤ 1256/Real.log 2 := by positivity
  have hAcross : 0 ≤ 8*(A:ℝ)*((Fintype.card α : ℝ)^k*t*Real.log (2*t)) := by positivity
  have hCcross := mul_nonneg hdiv hpoly
  simp only [div_eq_mul_inv] at hp' hpad hCcross ⊢
  nlinarith only [helim,hshear,hcq',hprice,hp',hpad,hAcross,hCcross]

end Cascade
end ExactFourier

end

end Complexity

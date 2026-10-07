/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.CircuitExtensions
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Exact Fourier circuits: cleared circuit

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/ClearedCircuit.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
/- The O_K(k² n^k) evaluation DAG and O_K((k+1)³ n^k) coefficient
DAG for the literal polynomial state correction, uniform in truncation length. -/
namespace ExactFourier
open scoped Kronecker
open TensorAxis TypedDAG PolynomialDAG
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A scalar circuit realizing the recursively cleared cascade response. -/
noncomputable def clearedDAG (b : ℂ) (L : Matrix α α ℂ) (T : Matrix α β ℂ) :
    (k : ℕ) → TypedDAG (States α β k) (Space α k)
  | 0 => wires (fun _ => none)
  | k+1 => blockCols (scalar b ((clearedDAG b L T k).tensor identity))
      ((TypedDAG.tensorPower L k).tensor (matrix T))

theorem eval_clearedDAG
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α]  (b : ℂ) (L : Matrix α α ℂ) (T
      : Matrix α β ℂ)
    (k : ℕ) (x : States α β k → ℂ) :
    (clearedDAG b L T k).eval x = (cleared b L T k).mulVec x := by
  induction k with
  | zero => funext j; simp [clearedDAG,cleared]
  | succ k ih =>
    apply eval_blockCols _ _ _ _ ?_ ?_ x
    · exact fun y => eval_scalar _ _ _ (fun z => eval_tensor _ _ _ _ ih
        (fun z => by simp) z) y
    · exact fun y => eval_tensor _ _ _ _ (eval_tensorPower L k) (eval_matrix T) y

theorem size_clearedDAG
    {α β : Type} [Fintype α] [Fintype β] (b : ℂ) (L : Matrix α α ℂ)
    (T : Matrix α β ℂ) (k : ℕ) :
    (clearedDAG b L T k).size ≤
      2*(Fintype.card β+Fintype.card α+1)*k^2*Fintype.card α^k := by
  let n := Fintype.card α
  let r := Fintype.card β
  change _ ≤ 2*(r+n+1)*k^2*n^k
  induction k with
  | zero => simp [clearedDAG]
  | succ k ih =>
    have hc : (clearedDAG b L T (k+1)).size = n*(clearedDAG b L T k).size +
        (2*r+2*n*k+2)*(n^k*n) := by
      simp [clearedDAG,size_tensorPower,Fintype.card_prod,card_space,n,r]
      ring
    rw [hc,pow_succ]
    calc
      n*(clearedDAG b L T k).size + (2*r+2*n*k+2)*(n^k*n) ≤
          (2*(r+n+1)*k^2 + (2*r+2*n*k+2))*(n^k*n) := by
        have h := Nat.mul_le_mul_left n ih
        nlinarith only [h]
      _ ≤ 2*(r+n+1)*(k+1)^2*(n^k*n) := by
        apply Nat.mul_le_mul_right
        nlinarith

omit [DecidableEq β] in
theorem exists_cleared_coeff_dag (b : Polynomial ℂ) (L : Matrix α α (Polynomial ℂ))
    (T : Matrix α β (Polynomial ℂ)) :
    ∃ A : ℕ, ∀ k t, ∃ C : TypedDAG (States α β k) (Fin t × Space α k),
      C.size ≤ A*(k+1)^3*Fintype.card α^k ∧
      ∀ x, C.eval x=(coefficients (cleared b L T k) t).mulVec x := by
  obtain ⟨d,hd⟩ := exists_cleared_degree b L T
  let a := 2*(Fintype.card β+Fintype.card α+1)
  refine ⟨(d+1)*a+2*(d+1)^2,?_⟩
  intro k t
  have hcirc : ∀ z : ℂ, ∃ C : TypedDAG (States α β k) (Space α k),
      C.size ≤ a*k^2*Fintype.card α^k ∧
      ∀ x, C.eval x=(evalMatrix (cleared b L T k) z).mulVec x := by
    intro z
    refine ⟨clearedDAG (b.eval z) (L.map (Polynomial.evalRingHom z)) (T.map
      (Polynomial.evalRingHom z)) k,
      size_clearedDAG _ _ _ k,?_⟩
    intro x
    rw [eval_clearedDAG]
    change _ = ((cleared b L T k).map (Polynomial.evalRingHom z)).mulVec x
    rw [map_cleared]
    rfl
  obtain ⟨C,hC,he⟩ := exists_coefficients (cleared b L T k) (k*d+1) t
    (a*k^2*Fintype.card α^k) (fun i j => Nat.lt_succ_of_le (hd k i j)) hcirc
  refine ⟨C,le_trans hC ?_,he⟩
  rw [card_space]
  have hm : k*d+1 ≤ (d+1)*(k+1) := by nlinarith
  have hk : k^2 ≤ (k+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have h1 := Nat.mul_le_mul hm (Nat.mul_le_mul_left a hk)
  have h2 := Nat.mul_le_mul hm hm
  calc
    (k*d+1)*(a*k^2*Fintype.card α^k)+2*(k*d+1)*(k*d+1)*Fintype.card α^k =
        ((k*d+1)*(a*k^2)+2*((k*d+1)^2))*Fintype.card α^k := by ring
    _ ≤ (((d+1)*a+2*(d+1)^2)*(k+1)^3)*Fintype.card α^k := by
      apply Nat.mul_le_mul_right
      have hp : (k+1)^2 ≤ (k+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    _ = _ := by ring

end Cascade
end ExactFourier

end

section
/- Exact finite elimination of initial-state contamination. No corner principle
is used: only the already proved triangular monotonicity and dirty shear replay. -/
namespace ExactFourier
open scoped Kronecker BigOperators

namespace TypedDAG
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem circuit_eval_of_matrix (C : TypedDAG ι κ) (A : Matrix κ ι ℂ)
    (hC : ∀ x, C.eval x = A.mulVec x) (x : Fin (Fintype.card ι) → ℂ) :
    C.circuit.eval x =
      (Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) A).mulVec x := by
  funext j
  have h := congrFun (hC (x ∘ Fintype.equivFin ι)) ((Fintype.equivFin κ).symm j)
  simp only [eval, Function.comp_def, Equiv.apply_symm_apply] at h
  rw [h]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
  simpa only [Equiv.apply_symm_apply] using ((Fintype.equivFin ι).symm.sum_comp
    (fun i => A ((Fintype.equivFin κ).symm j) i * x (Fintype.equivFin ι i))).symm

theorem shear_price (p : MatrixPrice) [DecidableEq ι] [DecidableEq κ]
    (C : TypedDAG ι κ) (A : Matrix κ ι ℂ) (hC : ∀ x, C.eval x = A.mulVec x) :
    p.value (rectangularShear A) ≤ 8 * (C.size : ℝ) + 2 * Fintype.card κ := by
  have he : Matrix.reindex (Equiv.sumCongr (Fintype.equivFin κ) (Fintype.equivFin ι))
        (Equiv.sumCongr (Fintype.equivFin κ) (Fintype.equivFin ι)) (rectangularShear A) =
      rectangularShear (Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) A) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.reindex_apply, rectangularShear, Matrix.fromBlocks, Matrix.one_apply]
  have h := p.rectangularShear_bound C.circuit _ (circuit_eval_of_matrix C A hC)
  rw [← he, p.reindex _ _ (rectangularShear_unit A)] at h
  exact h
end TypedDAG

namespace MatrixPrice
variable (p : MatrixPrice) {α β : Type} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem eliminate_top_right (A P : Matrix α α ℂ) (E Q : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ)
    (hK : IsUnit (Matrix.fromBlocks A E B D)) (hA : IsUnit A) (hP : IsUnit P)
    (hQ : A * P * Q = E) :
    p.value A ≤ p.value (Matrix.fromBlocks A E B D) +
      2 * p.value P + p.value (rectangularShear Q) := by
  let K := Matrix.fromBlocks A E B D
  let PP := Matrix.fromBlocks P 0 0 (1 : Matrix β β ℂ)
  let L := K * PP * rectangularShear (-Q)
  have hPP : IsUnit PP := Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hP,isUnit_one⟩
  have hL : IsUnit L := (hK.mul hPP).mul (rectangularShear_unit (-Q))
  have he : L = Matrix.fromBlocks (A*P) 0 (B*P) (D-B*P*Q) := by
    dsimp [L,K,PP,rectangularShear]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero,       add_zero, zero_add,
      Matrix.mul_one, Matrix.mul_neg]
    rw [hQ, neg_add_cancel]
    simp only [sub_eq_add_neg, add_comm]
  have hD : IsUnit (D-B*P*Q) :=
    (Matrix.isUnit_fromBlocks_zero₁₂.mp (he ▸ hL)).2
  have hlower := p.lower_triangular (A*P) (B*P) (D-B*P*Q) (hA.mul hP) hD
  rw [← he] at hlower
  have hnonneg := p.nonneg _ hD
  have h1 := p.mul_le K PP hK hPP
  have h2 := p.mul_le (K*PP) (rectangularShear (-Q)) (hK.mul hPP)
    (rectangularShear_unit (-Q))
  change p.value L ≤ _ at h2
  rw [p.rectangularShear_neg] at h2
  have hpp : p.value PP = p.value P := p.identity_pad P hP
  rw [hpp] at h1
  have hi : IsUnit P⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h3 := p.mul_le (A*P) P⁻¹ (hA.mul hP) hi
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv P (Matrix.isUnit_iff_isUnit_det _ |>.mp hP),
    Matrix.mul_one, p.inverse P hP] at h3
  dsimp only [K] at h1 h2
  linarith

end MatrixPrice
end ExactFourier

end

section
/- Radix-two algebra for the scalar-convolution bound in the finite-win proof.
This supplies the ordinary O(n log n) support algorithm. -/
namespace ExactFourier.RadixTwo
open scoped BigOperators
open Polynomial

/-- Embed an index into the even positions of a vector of twice the length. -/
def evenIndex (n : ℕ) (i : Fin n) : Fin (n+n) := ⟨2*i.val, by have := i.isLt; omega⟩
/-- Embed an index into the odd positions of a vector of twice the length. -/
def oddIndex (n : ℕ) (i : Fin n) : Fin (n+n) := ⟨2*i.val+1, by have := i.isLt; omega⟩

/-- Identify an index with its quotient by two and its parity. -/
def parityEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (n+n) where
  toFun p := ⟨2*p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun j := (⟨j.val/2, by have := j.isLt; omega⟩, ⟨j.val%2, by omega⟩)
  left_inv p := by
    apply Prod.ext <;> apply Fin.ext
    · change (2*p.1.val+p.2.val)/2 = p.1.val
      have := p.2.isLt
      omega
    · change (2*p.1.val+p.2.val)%2 = p.2.val
      have := p.2.isLt
      omega
  right_inv j := by
    apply Fin.ext
    change 2*(j.val/2)+j.val%2=j.val
    omega

theorem sum_even_odd {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Fin (n+n) → R) :
    ∑ i, f i = (∑ i : Fin n, f (evenIndex n i)) + ∑ i : Fin n, f (oddIndex n i) := by
  rw [← Fintype.sum_equiv (parityEquiv n) (fun p => f (parityEquiv n p)) f (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  exact Finset.sum_add_distrib

/-- Evaluate the coefficient vector at the specified power of `ω`. -/
noncomputable def evalAt (n : ℕ) (ω : ℂ) (x : Fin n → ℂ) (r : ℕ) : ℂ :=
  ∑ j, ω ^ (r*j.val) * x j

/-- Evaluate at the first `n` powers of `ω`, yielding a Fourier-type transform. -/
noncomputable def eval (n : ℕ) (ω : ℂ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => evalAt n ω x i.val

theorem power_even (ω : ℂ) (r j : ℕ) : ω^(r*(2*j)) = (ω^2)^(r*j) := by
  rw [← pow_mul]
  congr 1
  ring

theorem power_odd (ω : ℂ) (r j : ℕ) : ω^(r*(2*j+1)) = ω^r * (ω^2)^(r*j) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

theorem evalAt_split (n : ℕ) (ω : ℂ) (x : Fin (n+n) → ℂ) (r : ℕ) :
    evalAt (n+n) ω x r = evalAt n (ω^2) (x ∘ evenIndex n) r +
      ω^r * evalAt n (ω^2) (x ∘ oddIndex n) r := by
  rw [evalAt, sum_even_odd]
  simp only [evenIndex, oddIndex, power_even, power_odd, Function.comp_apply, evalAt,
    Finset.mul_sum, mul_assoc]

theorem evalAt_periodic (n : ℕ) (ω : ℂ) (hω : ω^n=1) (x : Fin n → ℂ) (r : ℕ) :
    evalAt n ω x (r+n) = evalAt n ω x r := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_mul, pow_add, pow_mul ω n j.val, hω, one_pow, mul_one]

theorem square_period {n : ℕ} (ω : ℂ) (hω : ω^n = -1) : (ω^2)^n = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hω]
  norm_num

/-- First and second frequency halves are the sum and difference butterfly. -/
theorem eval_split (n : ℕ) (ω : ℂ) (hω : ω^n = -1) (x : Fin (n+n) → ℂ) :
    eval (n+n) ω x = Fin.addCases
      (fun i => eval n (ω^2) (x ∘ evenIndex n) i + ω^i.val * eval n (ω^2) (x ∘ oddIndex n) i)
      (fun i => eval n (ω^2) (x ∘ evenIndex n) i - ω^i.val * eval n (ω^2) (x ∘ oddIndex n) i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [eval, Fin.val_castAdd, Fin.addCases_left] using evalAt_split n ω x j.val
  · simp only [eval, Fin.val_natAdd, Fin.addCases_right]
    rw [Nat.add_comm n j.val, evalAt_split,
      evalAt_periodic n (ω^2) (square_period ω hω),
      evalAt_periodic n (ω^2) (square_period ω hω), pow_add, hω]
    ring

/-- Orthogonality of the exact n-th root evaluation matrix. -/
theorem orthogonality {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (i k : Fin n) :
    (∑ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(k.val*j.val)) =
      if i=k then (n : ℂ) else 0 := by
  have hn0 := Nat.ne_of_gt hn
  have hω0 := hω.ne_zero hn0
  have he : ∀ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(k.val*j.val) =
      (ω^k.val / ω^i.val)^j.val := by
    intro j
    simp only [div_eq_mul_inv, mul_pow, inv_pow, pow_mul]
    rw [mul_comm]
  simp only [he]
  by_cases hik : i=k
  · subst k
    simp [hω0]
  · rw [ite_eq_right hik, Fin.sum_univ_eq_sum_range]
    have hne : ω^k.val / ω^i.val ≠ 1 := by
      intro h
      have hh : ω^k.val = ω^i.val := (div_eq_one_iff_eq (pow_ne_zero _ hω0)).mp h
      exact hik ((Fin.ext (hω.pow_inj k.isLt i.isLt hh)).symm)
    rw [geom_sum_eq hne]
    have hp : (ω^k.val / ω^i.val)^n = 1 := by
      rw [div_pow, ← pow_mul, Nat.mul_comm k.val n, pow_mul, hω.pow_eq_one,
        ← pow_mul, Nat.mul_comm i.val n, pow_mul, hω.pow_eq_one]
      simp
    rw [hp]
    simp

/-- The inverse FFT uses the inverse root and one scalar normalization. -/
theorem eval_inverse {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (x : Fin n → ℂ) :
    eval n ω⁻¹ (eval n ω x) = fun i => (n : ℂ) * x i := by
  classical
  funext i
  simp only [eval, evalAt, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul]
  have ho : ∀ k : Fin n,
      (∑ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(j.val*k.val)) =
        if i=k then (n : ℂ) else 0 := by
    intro k
    simpa only [Nat.mul_comm k.val] using orthogonality hn ω hω i k
  simp only [ho]
  simp

/-- Polynomial evaluation of the vector of coefficients is exactly the DFT. -/
theorem eval_ofFn (n : ℕ) (ω : ℂ) (x : Fin n → ℂ) (i : Fin n) :
    (Polynomial.ofFn n x).eval (ω^i.val) = eval n ω x i := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, eval, evalAt, pow_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- Transform, multiply by precomputed scalar evaluations, inverse transform.
The only degree condition is that the product is represented by fewer than n
coefficients, so there is no wraparound. -/
theorem convolution_formula {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (f g : ℂ[X]) (hfg : (f*g).natDegree < n) :
    eval n ω⁻¹ (fun i => (n : ℂ)⁻¹ * f.eval (ω^i.val) * g.eval (ω^i.val)) =
      fun i => (f*g).coeff i.val := by
  classical
  let y : Fin n → ℂ := fun i => (f*g).coeff i.val
  have hy : Polynomial.ofFn n y = f*g := by
    ext j
    by_cases hj : j<n
    · simp [Polynomial.ofFn_coeff_eq_val_of_lt _ hj, y]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hev : (fun i : Fin n => f.eval (ω^i.val) * g.eval (ω^i.val)) = eval n ω y := by
    funext i
    rw [← Polynomial.eval_mul, ← hy, eval_ofFn]
  have hscale : ∀ (z : Fin n → ℂ) (c : ℂ),
      eval n ω⁻¹ (fun i => c*z i) = fun i => c*eval n ω⁻¹ z i := by
    intro z c
    funext i
    simp only [eval, evalAt, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [mul_assoc (n : ℂ)⁻¹]
  have hev' (i : Fin n) : f.eval (ω^i.val) * g.eval (ω^i.val) = eval n ω y i :=
    congrFun hev i
  simp_rw [hev']
  rw [hscale, eval_inverse hn ω hω]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  funext i
  simp [y, hnC]

end ExactFourier.RadixTwo

end

end Complexity

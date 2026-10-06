/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Arithmetic.Rank
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Arithmetic.Accounting
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.PolyMul
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics

/-!
# Proofs for arithmetic matrix multiplication

Let a program with polynomial gates over a field `K` carry the polynomials `matMulPolynomial K n`
on its output wires `out`.

* **The cut bounds** (`chargeJ_le_of_formal`, `jacobianChargeI_le_of_formal`,
  `jacobianChargeK_le_of_formal`). Every split `S`, crossed by `w` signals, has
  `R_J, L_I, L_K ≤ w`. Over `K(t)` the Hankel matrix `M = (t ^ ((i + j)²))` is totally regular
  (`totallyRegular_genericHankel`). The Hessian consequence of the Taylor cut lemma, for the
  combination `∑ M i k C i k`, bounds `R_J` (`chargeJ_le_blockRank_hessian`); its Jacobian
  consequence at the point `A = B = M` bounds the forward and the backward block together, so
  `L_I` and `L_K` (`jacobianRows_le_blockRank`, `jacobianCols_le_blockRank`).
* **One component** (`mem_component_of_formal`). The component of the output `C 0 0` is crossed
  by no signal, so both Jacobian blocks vanish at the point `A = B = 1` (all ones), where the
  output `C i k` has derivative one in every `A i j` and every `B j k`. So `C i k`, `A i j` and
  `B j k` lie together in or out of the component, which spreads to every terminal.
* **The finite bound** (`fifteen_mul_sq_sub_le`). At the threshold prefix of
  `Tripartite.exists_threshold`, `15 n² ≤ 8 (R_J + L_I + L_K) + 6 n + 9 ≤ 24 w + 6 n + 9`
  (`fifteen_mul_sq_le`), and the prefix is charged to the component of all `2 n²` inputs.
* **The asymptotic bound** (`eventually_lt_of_le`). Assume at most `(2 + 5/(8 A) - ε) n²`
  gates and choose `η = A² ε/2`; the cycle term is then at most `(5/8 - A ε/2) n²`, while the
  linear loss and the logarithmic term are `o(n²)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.ArithmeticInternal

open Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Tripartite Filter MatMul.Internal

variable {n : Nat}

/-! ## Evaluating the polynomials -/

/-- Over every commutative algebra, the polynomials evaluate to the product. -/
theorem aeval_matMulPolynomial {K A : Type*} [CommSemiring K] [CommSemiring A] [Algebra K A]
    (z : Fin (n * n + n * n) → A) (o : Fin (n * n)) :
    MvPolynomial.aeval z (matMulPolynomial K n o) = matMul n z o := by
  rw [output_eq o, matMulPolynomial, matMul_output, matMul_output, map_sum]
  simp

/-- The polynomials evaluate to the product. -/
theorem eval_matMulPolynomial {K : Type*} [CommSemiring K] (z : Fin (n * n + n * n) → K)
    (o : Fin (n * n)) : MvPolynomial.eval z (matMulPolynomial K n o) = matMul n z o := by
  rw [output_eq o, matMulPolynomial, matMul_output, matMul_output, map_sum]
  simp

/-- Every output of matrix multiplication is a nonconstant function: it vanishes at zero and is
one at `A = E i j`, `B = E j k`. -/
theorem matMul_nonconstant {K : Type*} [Field K] (hn : 0 < n) (o : Fin (n * n)) :
    ∃ x y : Fin (n * n + n * n) → K, matMul n x o ≠ matMul n y o := by
  classical
  rw [output_eq o]
  set i := (finProdFinEquiv.symm o).1
  set k := (finProdFinEquiv.symm o).2
  refine ⟨0, matMulInput (Matrix.single i ⟨0, hn⟩ 1) (Matrix.single ⟨0, hn⟩ k 1), ?_⟩
  rw [matMul_matMulInput, Matrix.single_mul_single_same, Matrix.single_apply_same, mul_one,
    matMul_output]
  simp

/-! ## The cut bounds -/

section Cut

variable {σ : Signature} {s : Nat} {K : Type*} [Field K]
  (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) {p : Program σ (n * n + n * n) s}
  {out : Fin (n * n) → Wire (n * n + n * n) s}

theorem mem_placeA {S : Finset (Wire (n * n + n * n) s)} {i j : Fin n} :
    (i, j) ∈ place (matMulTermA n s) S ↔ matMulLeft n i j ∈ inputsIn S := by
  simp only [place, Finset.mem_filter, Finset.mem_univ, true_and, mem_inputsIn]
  rfl

theorem mem_placeB {S : Finset (Wire (n * n + n * n) s)} {j k : Fin n} :
    (j, k) ∈ place (matMulTermB n s) S ↔ matMulRight n j k ∈ inputsIn S := by
  simp only [place, Finset.mem_filter, Finset.mem_univ, true_and, mem_inputsIn]
  rfl

theorem mem_placeC {S : Finset (Wire (n * n + n * n) s)} {i k : Fin n} :
    (i, k) ∈ place (matMulTermC out) S ↔ matMulOutput n i k ∈ outputsIn out S := by
  simp only [place, Finset.mem_filter, Finset.mem_univ, true_and, outputsIn]
  rfl

/-- A program formally computing the polynomials computes the product over its coefficient
field. -/
theorem trace_eq_matMul (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMulPolynomial K n o)
    (z : Fin (n * n + n * n) → K) (o : Fin (n * n)) :
    p.trace (Taylor.algebraInterpretation P K) z (out o) = matMul n z o := by
  rw [Taylor.trace_eq_aeval_wirePolynomial, hf, aeval_matMulPolynomial]

/-- **The Hessian charge.** -/
theorem chargeJ_le_of_formal
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMulPolynomial K n o)
    (S : Finset (Wire (n * n + n * n) s)) :
    chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) ≤
      (forward p S).card + (backward p S).card := by
  classical
  set M := hankel n fun m => (RatFunc.X : RatFunc K) ^ (m ^ 2)
  have h := Taylor.blockRank_hessian_le_of_trace P p out S (0 : Fin (n * n + n * n) → RatFunc K)
    fun o => M (finProdFinEquiv.symm o).1 (finProdFinEquiv.symm o).2
  simp only [hf] at h
  exact (chargeJ_le_blockRank_hessian totallyRegular_genericHankel 0 (inputsIn S) _ _
    (fun _ _ => mem_placeA) (fun _ _ => mem_placeB)).trans h

/-- **The row Jacobian charge.** -/
theorem jacobianChargeI_le_of_formal
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMulPolynomial K n o)
    (S : Finset (Wire (n * n + n * n) s)) :
    jacobianChargeI (place (matMulTermA n s) S) (place (matMulTermB n s) S)
        (place (matMulTermC out) S) ≤
      (forward p S).card + (backward p S).card := by
  classical
  set M := hankel n fun m => (RatFunc.X : RatFunc K) ^ (m ^ 2)
  have hM : TotallyRegular M := totallyRegular_genericHankel
  have h := Taylor.blockRank_jacobian_add_blockRank_le_of_trace P p out S (matMulInput M M)
  simp only [hf] at h
  have h₁ := jacobianRows_le_blockRank (K := K) hM hM (outputsIn out S)ᶜ (inputsIn S)
    (place (matMulTermC out) S)ᶜ (place (matMulTermA n s) S) (place (matMulTermB n s) S)
    (heavyI (place (matMulTermA n s) S) (place (matMulTermC out) S))
    (fun q hq => Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hq (mem_placeC.mpr h))
    (fun q hq => mem_placeA.mp hq) (fun q hq => mem_placeB.mp hq)
  have h₂ := jacobianRows_le_blockRank (K := K) hM hM (outputsIn out S) (inputsIn S)ᶜ
    (place (matMulTermC out) S) (place (matMulTermA n s) S)ᶜ (place (matMulTermB n s) S)ᶜ
    (heavyI (place (matMulTermA n s) S) (place (matMulTermC out) S))ᶜ
    (fun q hq => mem_placeC.mp hq)
    (fun q hq => Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hq (mem_placeA.mpr h))
    (fun q hq => Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hq (mem_placeB.mpr h))
  exact (Nat.add_le_add h₁ h₂).trans h

/-- **The column Jacobian charge.** -/
theorem jacobianChargeK_le_of_formal
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMulPolynomial K n o)
    (S : Finset (Wire (n * n + n * n) s)) :
    jacobianChargeK (place (matMulTermA n s) S) (place (matMulTermB n s) S)
        (place (matMulTermC out) S) ≤
      (forward p S).card + (backward p S).card := by
  classical
  set M := hankel n fun m => (RatFunc.X : RatFunc K) ^ (m ^ 2)
  have hM : TotallyRegular M := totallyRegular_genericHankel
  have h := Taylor.blockRank_jacobian_add_blockRank_le_of_trace P p out S (matMulInput M M)
  simp only [hf] at h
  have h₁ := jacobianCols_le_blockRank (K := K) hM hM (outputsIn out S)ᶜ (inputsIn S)
    (place (matMulTermC out) S)ᶜ (place (matMulTermA n s) S) (place (matMulTermB n s) S)
    (heavyK (place (matMulTermB n s) S) (place (matMulTermC out) S))
    (fun q hq => Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hq (mem_placeC.mpr h))
    (fun q hq => mem_placeA.mp hq) (fun q hq => mem_placeB.mp hq)
  have h₂ := jacobianCols_le_blockRank (K := K) hM hM (outputsIn out S) (inputsIn S)ᶜ
    (place (matMulTermC out) S) (place (matMulTermA n s) S)ᶜ (place (matMulTermB n s) S)ᶜ
    (heavyK (place (matMulTermB n s) S) (place (matMulTermC out) S))ᶜ
    (fun q hq => mem_placeC.mp hq)
    (fun q hq => Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hq (mem_placeA.mpr h))
    (fun q hq => Finset.mem_compl.mpr fun h => Finset.mem_compl.mp hq (mem_placeB.mpr h))
  exact (Nat.add_le_add h₁ h₂).trans h

end Cut

end Algebraic.Cutwidth.MultiOutput.MatMul.ArithmeticInternal

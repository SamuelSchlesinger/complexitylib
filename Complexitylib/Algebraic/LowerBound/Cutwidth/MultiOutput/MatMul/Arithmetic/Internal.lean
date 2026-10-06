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

/-! ## One component -/

section Component

/-- A block with a nonzero entry has positive rank. -/
theorem one_le_blockRank {L : Type*} [Field L] {m N : Nat} {M : Matrix (Fin m) (Fin N) L}
    {Y : Finset (Fin m)} {X : Finset (Fin N)} {y : Fin m} {x : Fin N} (hy : y ∈ Y) (hx : x ∈ X)
    (h : M y x ≠ 0) : 1 ≤ blockRank M Y X := by
  have hdet : ((M.submatrix (fun i : ↥Y => (i : Fin m)) (fun j : ↥X => (j : Fin N))).submatrix
      (fun _ : Unit => (⟨y, hy⟩ : ↥Y)) (fun _ : Unit => (⟨x, hx⟩ : ↥X))).det ≠ 0 := by
    rw [Matrix.det_unique]
    exact h
  have hrank := Matrix.rank_of_det_ne_zero hdet
  rw [Fintype.card_unit] at hrank
  rw [blockRank, ← hrank]
  exact Matrix.rank_submatrix_le _ _ _

variable {σ : Signature} {s : Nat} {K : Type*} [Field K]
  (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) {p : Program σ (n * n + n * n) s}
  {out : Fin (n * n) → Wire (n * n + n * n) s}

/-- **All terminals lie in one component.** If the wires `out` of a program with polynomial
gates carry the polynomials of matrix multiplication and `n ≥ 1`, the component of the output
`C 0 0` contains every input and every output. -/
theorem mem_component_of_formal (hn : 0 < n)
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMulPolynomial K n o) :
    (∀ x, Wire.input x ∈ component p (out (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩))) ∧
      ∀ o, out o ∈ component p (out (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩)) := by
  classical
  set z₀ : Fin n := ⟨0, hn⟩
  set W := component p (out (matMulOutput n z₀ z₀)) with hW
  have hclosed := component_closed p (out (matMulOutput n z₀ z₀))
  have hfwd : forward p W = ∅ := forward_eq_empty_of_closed hclosed
  have hbwd : backward p W = ∅ := backward_eq_empty_of_closed hclosed
  have h := Taylor.blockRank_jacobian_add_blockRank_le_of_trace P p out W
    fun _ : Fin (n * n + n * n) => (1 : K)
  rw [hfwd, hbwd, Finset.card_empty, add_zero] at h
  simp only [hf] at h
  have memOut : ∀ i k, matMulOutput n i k ∈ outputsIn out W ↔ out (matMulOutput n i k) ∈ W :=
    fun i k => by simp [outputsIn]
  -- An output and the inputs it depends on lie together in or out of the component.
  have together : ∀ {y : Fin (n * n)} {x : Fin (n * n + n * n)},
      Taylor.jacobian (fun o => matMulPolynomial K n o) (fun _ => (1 : K)) y x ≠ 0 →
      (y ∈ outputsIn out W ↔ x ∈ inputsIn W) := by
    intro y x hyx
    constructor
    · intro hy
      by_contra hx
      have := one_le_blockRank hy (Finset.mem_compl.mpr hx) hyx
      omega
    · intro hx
      by_contra hy
      have := one_le_blockRank (Finset.mem_compl.mpr hy) hx hyx
      omega
  have hA : ∀ i j k, (matMulOutput n i k ∈ outputsIn out W ↔ matMulLeft n i j ∈ inputsIn W) :=
    fun i j k => together (by simp [jacobian_left])
  have hB : ∀ i j k, (matMulOutput n i k ∈ outputsIn out W ↔ matMulRight n j k ∈ inputsIn W) :=
    fun i j k => together (by simp [jacobian_right])
  have hC₀ : matMulOutput n z₀ z₀ ∈ outputsIn out W := (memOut _ _).mpr (mem_component_self _ _)
  have hCall : ∀ i k, matMulOutput n i k ∈ outputsIn out W := by
    intro i k
    rw [hB i z₀ k, ← hB z₀ z₀ k, hA z₀ z₀ k, ← hA z₀ z₀ z₀]
    exact hC₀
  refine ⟨fun x => ?_, fun o => ?_⟩
  · rcases input_cases x with ⟨i, j, rfl⟩ | ⟨j, k, rfl⟩
    · exact mem_inputsIn.mp ((hA i j z₀).mp (hCall i z₀))
    · exact mem_inputsIn.mp ((hB z₀ j k).mp (hCall z₀ k))
  · rw [output_eq o]
    exact (memOut _ _).mp (hCall _ _)

end Component

/-! ## The finite bound -/

section Finite

variable {σ : Signature} {s : Nat} {K : Type*} [Field K]

/-- **The finite bound.** A fan-in-two program with polynomial gates over a field, whose wires
`out` carry the polynomials of matrix multiplication, has
`(15 n² - 6 n - 9)/24 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem fifteen_mul_sq_sub_le {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C)
    (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (p : Program σ (n * n + n * n) s)
    (hp : p.FanInAtMost 2) (out : Fin (n * n) → Wire (n * n + n * n) s)
    (hf : ∀ o, Taylor.wirePolynomial P p (out o) = matMulPolynomial K n o) :
    (15 * (n : ℝ) ^ 2 - 6 * n - 9) / 24 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  classical
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 (2 * (n : ℝ) ^ 2 + 3 * s) := by
    rcases Nat.eq_zero_or_pos (2 * n ^ 2 + 3 * s) with h | h
    · have : (2 * (n : ℝ) ^ 2 + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 := mul_nonneg hAη (le_max_right _ _)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have h0 : (n : ℝ) = 0 := by exact_mod_cast hn
    have hneg : (15 * (n : ℝ) ^ 2 - 6 * n - 9) / 24 < 0 := by
      rw [h0]
      norm_num
    exact hneg.le.trans (add_nonneg (add_nonneg hmax0 (by linarith)) hC)
  -- All terminals lie in one component, on distinct wires.
  obtain ⟨hin, houtW⟩ := mem_component_of_formal P hn hf
  set W₀ := component p (out (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩)) with hW₀
  have hterm := terminal_injective (trace_eq_matMul P hf)
  -- The ranking and the threshold prefix.
  obtain ⟨rank, hrank, hlt, hbound⟩ := exists_rank hAη order p hp
  obtain ⟨t, ⟨x, hx⟩, hlo, hhi⟩ :=
    exists_threshold hn (matMulTermA n s) (matMulTermB n s) (matMulTermC out) hterm rank hrank _ hlt
  set S := prefixBelow rank (t + 1) with hS
  set w₀ := Sum.elim (matMulTermA n s) (Sum.elim (matMulTermB n s) (matMulTermC out)) x
    with hw₀def
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
  have hsq := fifteen_mul_sq_le _ _ _ hlo hhi
  have hJ := chargeJ_le_of_formal P hf S
  have hI := jacobianChargeI_le_of_formal P hf S
  have hK := jacobianChargeK_le_of_formal P hf S
  have hlower : 15 * n ^ 2 ≤ 24 * ((forward p S).card + (backward p S).card) + 6 * n + 9 := by
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
  have hlowerR : (15 * (n : ℝ) ^ 2 - 6 * n - 9) / 24 ≤
      (((forward p S).card + (backward p S).card : Nat) : ℝ) := by
    have : ((15 * n ^ 2 : Nat) : ℝ) ≤
        ((24 * ((forward p S).card + (backward p S).card) + 6 * n + 9 : Nat) : ℝ) := by
      exact_mod_cast hlower
    push_cast at this ⊢
    linarith
  linarith

end Finite

/-! ## Asymptotics -/

/-- **The asymptotic bound.** If the graph-ordering hypothesis holds with coefficient `A > 0` for
every positive slack, then for every `ε > 0` and all large `n`, every size `s` satisfying the
finite bound for every ordering has `s > (2 + 5/(8 A) - ε) n²`. -/
theorem eventually_lt_of_le {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ s : Nat, (∀ η C : ℝ, 0 ≤ A + η → Multigraph.OrderingBound A η C →
      (15 * (n : ℝ) ^ 2 - 6 * n - 9) / 24 ≤
        (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C) →
      (2 + 5 / (8 * A) - ε) * n ^ 2 < s := by
  set ε' := min ε (5 / (8 * A)) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 5 / (8 * A) := min_le_right _ _
  set η := A ^ 2 * ε' / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  set B : ℝ := 8 + 15 / (8 * A) with hB
  have hBpos : 0 < B := by positivity
  filter_upwards [eventually_mul_logb_add_lt 6 (3 * Real.logb 2 B + C + 1) one_pos,
    eventually_ge_atTop 1, eventually_ge_atTop ⌈10 / (A * ε')⌉₊] with n hlog hn1 hnbig
  intro s bound
  by_contra hs
  rw [not_lt] at hs
  have hs' : (s : ℝ) ≤ (2 + 5 / (8 * A) - ε') * n ^ 2 :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have core := bound η C hAη hC
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnbig' : 10 / (A * ε') ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnbig)
  -- The cycle-rank term.
  have hrest : 0 ≤ (5 / (8 * A) - ε') * n ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((s : ℝ) - 2 * n ^ 2) 0 ≤ (5 / (8 * A) - ε') * n ^ 2 :=
    max_le (by linarith) hrest
  have hcoef : (A + η) * (5 / (8 * A) - ε') ≤ 5 / 8 - A * ε' / 2 := by
    have h₁ : (A + η) * (5 / (8 * A) - ε') = 5 / 8 - A * ε' + 5 * η / (8 * A) - η * ε' := by
      field_simp
      ring
    have h₂ : 5 * η / (8 * A) = 5 * (A * ε') / 16 := by
      rw [hη]
      field_simp
      ring
    have h₃ : 0 ≤ η * ε' := by positivity
    have h₄ : 0 ≤ A * ε' := by positivity
    linarith
  have hprod : (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 ≤ (5 / 8 - A * ε' / 2) * n ^ 2 := by
    calc (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 ≤ (A + η) * ((5 / (8 * A) - ε') * n ^ 2) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (5 / (8 * A) - ε') * n ^ 2 := by ring
      _ ≤ (5 / 8 - A * ε' / 2) * n ^ 2 := mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- The logarithmic term.
  have hVle : 2 * (n : ℝ) ^ 2 + 3 * s ≤ B * n ^ 2 := by
    have h₁ : (2 + 5 / (8 * A) - ε') * (n : ℝ) ^ 2 ≤ (2 + 5 / (8 * A)) * n ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (n : ℝ) ^ 2 = 2 * n ^ 2 + 3 * ((2 + 5 / (8 * A)) * n ^ 2) := by
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

end Algebraic.Cutwidth.MultiOutput.MatMul.ArithmeticInternal

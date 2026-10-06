/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Internal
public import Mathlib.Algebra.DualNumber

/-!
# Proofs for the Taylor cut lemma

* *Jets* (`fst_aeval_dualNumber`, `snd_aeval_dualNumber`, `aeval_jet`): over the dual numbers
  `R[ε]`, a polynomial takes the value `P(x) + ε ∑ⱼ ∂ⱼP(x) dⱼ` at `x + ε d`. Applied twice, over
  `L[s][t] = L[s, t]/(s², t²)` it takes at `a + s v + t u` the value with coefficients `P(a)`,
  `∇P(a) · v`, `∇P(a) · u` and `vᵀ H u`, where `H` is the Hessian of `P` at `a`.
* *Formal evaluation* (`trace_eq_aeval_wirePolynomial`): over every commutative algebra, the value
  of a wire is its wire polynomial evaluated at the input.
* *The cut kernel* (`cutKernel`): the directions `δ` along which no crossing wire moves to first
  order. It has codimension at most the number of crossing signals.
* *Mixing jets*: two jets whose crossing wires agree have equal boundary keys, so cut and paste
  (`SingleCut.trace_mix`) and the vanishing mixed second difference
  (`trace_add_trace_eq_trace_mix_add_trace_mix`) apply over `L[s, t]`. Reading off coefficients
  shows that the cut kernel splits into its parts on the two sides of the cut, that a direction
  on one side does not move the wires of the other side, and that the Hessian of every wire
  pairs the two sides to zero.
* *Linear algebra* (`finrank_add_finrank_add_rank_le`): subspaces `V` and `W` orthogonal through
  a matrix `B` have `dim V + dim W + rank B ≤` the sum of the dimensions, by Sylvester's rank
  inequality applied to basis matrices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Taylor.Internal

open SingleCut Matrix MvPolynomial TrivSqZeroExt Module

variable {K : Type*} [CommRing K] {σ : Signature} {n s m : ℕ}

/-! ## Jets -/

section Jet

variable {R : Type*} [CommRing R] [Algebra K R]

/-- The real part of a polynomial at a dual number is its value at the real parts. -/
theorem fst_aeval_dualNumber (P : MvPolynomial (Fin n) K) (u : Fin n → DualNumber R) :
    (aeval u P).fst = aeval (fun j => (u j).fst) P :=
  comp_aeval_apply u (fstHom K R R) P

/-- **First-order Taylor expansion.** The dual part of `P(x + ε d)` is `∑ⱼ ∂ⱼP(x) dⱼ`. -/
theorem snd_aeval_dualNumber (P : MvPolynomial (Fin n) K) (u : Fin n → DualNumber R) :
    (aeval u P).snd = ∑ j, aeval (fun i => (u i).fst) (pderiv j P) * (u j).snd := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [algebraMap_eq_inl']
  | add P Q hP hQ => simp [hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    rw [map_mul, aeval_X, DualNumber.snd_mul, fst_aeval_dualNumber, hP, Finset.sum_mul]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X,
      Pi.single_apply, add_mul, Finset.sum_add_distrib]
    simp [mul_comm, mul_left_comm]

variable {L : Type*} [Field L] [Algebra K L]

/-- **First-order Taylor expansion at a point of `L`.** -/
theorem aeval_inl_add_inr (P : MvPolynomial (Fin n) K) (a v : Fin n → L) :
    aeval (fun j => (inl (a j) + inr (v j) : DualNumber L)) P =
      inl (aeval a P) + inr (∑ j, aeval a (pderiv j P) * v j) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [fst_aeval_dualNumber]
  · simp [snd_aeval_dualNumber]

/-- The point `a + s v + t u` over `L[s][t] = L[s, t]/(s², t²)`. -/
def jet (a v u : Fin n → L) : Fin n → DualNumber (DualNumber L) :=
  fun j => inl (inl (a j) + inr (v j)) + inr (inl (u j))

/-- **Second-order Taylor expansion.** At `a + s v + t u`, a polynomial takes the value
`P(a) + s ∇P(a)·v + t ∇P(a)·u + s t vᵀ H u`, with `H` its Hessian at `a`. -/
theorem aeval_jet (P : MvPolynomial (Fin n) K) (a v u : Fin n → L) :
    aeval (jet a v u) P =
      inl (inl (aeval a P) + inr (∑ j, aeval a (pderiv j P) * v j)) +
        inr (inl (∑ j, aeval a (pderiv j P) * u j) +
          inr (v ⬝ᵥ (hessian P a *ᵥ u))) := by
  have hbase : (fun j => (jet a v u j).fst) = fun j => (inl (a j) + inr (v j) : DualNumber L) := by
    funext j
    simp [jet]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_aeval_dualNumber, hbase, aeval_inl_add_inr, fst_add, fst_inl, fst_inr, add_zero]
  · rw [snd_aeval_dualNumber, hbase]
    simp only [aeval_inl_add_inr]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [jet, fst_sum]
    · simp only [jet, snd_sum, fst_add, snd_add, fst_inl, fst_inr, snd_inl, snd_inr, add_zero,
        DualNumber.snd_mul, mul_zero, zero_add]
      simp only [dotProduct, mulVec, hessian, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

end Jet

/-- **The second derivatives of a product of two variables.** `∂ₖ ∂ₗ (Xₚ X_q)` is the number of
ways to match `(l, k)` with `(p, q)` or `(q, p)`. -/
theorem aeval_pderiv_pderiv_X_mul_X {R : Type*} [CommRing R] [Algebra K R] (a : Fin n → R)
    (p q k l : Fin n) :
    aeval a (pderiv k (pderiv l (X p * X q : MvPolynomial (Fin n) K))) =
      (if l = p ∧ k = q then 1 else 0) + (if l = q ∧ k = p then 1 else 0) := by
  have h₁ : pderiv l (X p * X q : MvPolynomial (Fin n) K) =
      C (if q = l then 1 else 0) * X p + C (if p = l then 1 else 0) * X q := by
    rw [Derivation.leibniz, pderiv_X, pderiv_X, Pi.single_apply, Pi.single_apply, smul_eq_mul,
      smul_eq_mul]
    split_ifs <;> simp [mul_comm]
  have h₂ : ∀ r : Fin n, aeval a (pderiv k (X r : MvPolynomial (Fin n) K)) =
      if r = k then 1 else 0 := by
    intro r
    rw [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have h₃ : ∀ u v w z : Fin n,
      algebraMap K R (if u = v then 1 else 0) * (if w = z then 1 else 0) =
        if v = u ∧ z = w then 1 else 0 := by
    intro u v w z
    by_cases h : u = v <;> by_cases h' : w = z <;> simp [h, h', eq_comm]
  rw [h₁, map_add, pderiv_C_mul, pderiv_C_mul, map_add, map_mul, map_mul, h₂, h₂, aeval_C,
    aeval_C, add_comm, h₃, h₃]

/-! ## Formal evaluation -/

section Formal

variable (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)

/-- Evaluating a program with polynomial gates commutes with algebra homomorphisms. -/
theorem map_trace_algebraInterpretation {A B : Type*} [CommSemiring A] [Algebra K A]
    [CommSemiring B] [Algebra K B] (φ : A →ₐ[K] B) (p : Program σ n s) (x : Fin n → A)
    (w : Wire n s) :
    φ (p.trace (algebraInterpretation P A) x w) =
      p.trace (algebraInterpretation P B) (fun j => φ (x j)) w :=
  congrFun (p.map_trace ⟨φ, fun op y => comp_aeval_apply y φ (P op)⟩ x) w

/-- Over every commutative algebra, a wire carries its wire polynomial evaluated at the
input. -/
theorem trace_eq_aeval_wirePolynomial {A : Type*} [CommSemiring A] [Algebra K A]
    (p : Program σ n s) (x : Fin n → A) (w : Wire n s) :
    p.trace (algebraInterpretation P A) x w = aeval x (wirePolynomial P p w) := by
  rw [wirePolynomial, map_trace_algebraInterpretation P (aeval x)]
  simp only [aeval_X]

end Formal

/-! ## The cut kernel -/

section Cut

variable {L : Type*} [Field L] [Algebra K L]
  (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (p : Program σ n s)
  (S : Finset (Wire n s)) (a : Fin n → L)

/-- The value of every wire at a jet. -/
theorem trace_jet (v u : Fin n → L) (w : Wire n s) :
    p.trace (algebraInterpretation P (DualNumber (DualNumber L))) (jet a v u) w =
      inl (inl (aeval a (wirePolynomial P p w)) +
          inr ((jacobian (wirePolynomial P p) a *ᵥ v) w)) +
        inr (inl ((jacobian (wirePolynomial P p) a *ᵥ u) w) +
          inr (v ⬝ᵥ (hessian (wirePolynomial P p w) a *ᵥ u))) := by
  rw [trace_eq_aeval_wirePolynomial, aeval_jet]
  rfl

omit [Algebra K L] in
/-- Mixing two jets mixes their directions. -/
theorem mix_jet (v u v' u' : Fin n → L) :
    mix S (jet a v u) (jet a v' u') = jet a (mix S v v') (mix S u u') := by
  funext j
  simp only [mix, jet]
  split_ifs <;> rfl

omit [Field L] [Algebra K L] in
theorem mix_self (v : Fin n → L) : mix S v v = v := by
  funext j
  simp only [mix]
  split_ifs <;> rfl

/-- Two inputs with the same values on every crossing wire have the same boundary key. -/
theorem boundaryKey_eq_of_forall {U : Type*} {I : Interpretation σ U} {x x' : Fin n → U}
    (h : ∀ c ∈ forward p S ∪ backward p S, p.trace I x c = p.trace I x' c) :
    boundaryKey p I S x = boundaryKey p I S x' :=
  Prod.ext (funext fun c => h c (Finset.mem_union_left _ c.2))
    (funext fun c => h c (Finset.mem_union_right _ c.2))

/-- **The cut kernel**: the directions along which no crossing wire moves to first order. -/
noncomputable def cutKernel : Submodule L (Fin n → L) :=
  LinearMap.ker ((jacobian (wirePolynomial P p) a).submatrix
    (fun c : ↥(forward p S ∪ backward p S) => (c : Wire n s)) id).mulVecLin

theorem mem_cutKernel {δ : Fin n → L} :
    δ ∈ cutKernel P p S a ↔
      ∀ c ∈ forward p S ∪ backward p S, (jacobian (wirePolynomial P p) a *ᵥ δ) c = 0 := by
  simp only [cutKernel, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
  exact ⟨fun h c hc => h ⟨c, hc⟩, fun h c => h c c.2⟩

/-- The cut kernel has codimension at most the number of crossing signals. -/
theorem le_finrank_cutKernel_add :
    n ≤ finrank L (cutKernel P p S a) + ((forward p S).card + (backward p S).card) := by
  have hker := MultiOutput.Internal.finrank_ker_mulVecLin
    ((jacobian (wirePolynomial P p) a).submatrix
      (fun c : ↥(forward p S ∪ backward p S) => (c : Wire n s)) id)
  have hrank := Matrix.rank_le_card_height ((jacobian (wirePolynomial P p) a).submatrix
    (fun c : ↥(forward p S ∪ backward p S) => (c : Wire n s)) id)
  have hunion := Finset.card_union_le (forward p S) (backward p S)
  rw [Fintype.card_fin] at hker
  rw [Fintype.card_coe] at hrank
  change finrank L (cutKernel P p S a) = _ at hker
  omega

/-- A direction in the cut kernel and the zero direction give jets with equal boundary keys. -/
theorem boundaryKey_jet_eq {v u : Fin n → L} (hv : v ∈ cutKernel P p S a)
    (hu : u ∈ cutKernel P p S a) :
    boundaryKey p (algebraInterpretation P (DualNumber (DualNumber L))) S (jet a v 0) =
      boundaryKey p (algebraInterpretation P (DualNumber (DualNumber L))) S (jet a 0 u) := by
  refine boundaryKey_eq_of_forall p S fun c hc => ?_
  rw [trace_jet, trace_jet, (mem_cutKernel P p S a).mp hv c hc,
    (mem_cutKernel P p S a).mp hu c hc]
  simp

/-- **The left part of a kernel direction.** Moving only the inputs in `S` along a kernel
direction moves the wires in `S` as the full direction does and fixes the other wires. -/
theorem jacobian_mulVec_mix_left {δ : Fin n → L} (hδ : δ ∈ cutKernel P p S a) (w : Wire n s) :
    (jacobian (wirePolynomial P p) a *ᵥ mix S δ 0) w =
      if w ∈ S then (jacobian (wirePolynomial P p) a *ᵥ δ) w else 0 := by
  have hkey := boundaryKey_jet_eq P p S a hδ (Submodule.zero_mem _)
  have h := trace_mix p _ (agree_forward_of_boundaryKey_eq hkey)
    (agree_backward_of_boundaryKey_eq hkey) w
  rw [mix_jet, mix_self] at h
  have h' := congrArg (fun z : DualNumber (DualNumber L) => z.fst.snd) h
  split_ifs at h' with hw
  · simpa [trace_jet, hw] using h'
  · simpa [trace_jet, hw] using h'

/-- **The right part of a kernel direction.** -/
theorem jacobian_mulVec_mix_right {δ : Fin n → L} (hδ : δ ∈ cutKernel P p S a) (w : Wire n s) :
    (jacobian (wirePolynomial P p) a *ᵥ mix S 0 δ) w =
      if w ∈ S then 0 else (jacobian (wirePolynomial P p) a *ᵥ δ) w := by
  have hkey := boundaryKey_jet_eq P p S a (Submodule.zero_mem _) hδ
  have h := trace_mix p _ (agree_forward_of_boundaryKey_eq hkey)
    (agree_backward_of_boundaryKey_eq hkey) w
  rw [mix_jet, mix_self] at h
  have h' := congrArg (fun z : DualNumber (DualNumber L) => z.snd.fst) h
  split_ifs at h' with hw
  · simpa [trace_jet, hw] using h'
  · simpa [trace_jet, hw] using h'

/-- **The Hessian pairs the two sides to zero.** For kernel directions `v` on the inputs in `S`
and `u` on the other inputs, the second-order cross term of every wire vanishes. -/
theorem dotProduct_hessian_mulVec_eq_zero {v u : Fin n → L} (hv : v ∈ cutKernel P p S a)
    (hu : u ∈ cutKernel P p S a) (hvS : ∀ j, Wire.input j ∉ S → v j = 0)
    (huS : ∀ j, Wire.input j ∈ S → u j = 0) (w : Wire n s) :
    v ⬝ᵥ (hessian (wirePolynomial P p w) a *ᵥ u) = 0 := by
  have hkey := boundaryKey_jet_eq P p S a hv hu
  have h := MultiOutput.Internal.trace_add_trace_eq_trace_mix_add_trace_mix p _ hkey w
  have hv0 : mix S v 0 = v := by
    funext j
    simp only [mix]
    split_ifs with hj
    · rfl
    · exact (hvS j hj).symm
  have hu0 : mix S 0 u = u := by
    funext j
    simp only [mix]
    split_ifs with hj
    · exact (huS j hj).symm
    · rfl
  have h0v : mix S 0 v = 0 := by
    funext j
    simp only [mix]
    split_ifs with hj
    · rfl
    · exact hvS j hj
  have hu0' : mix S u 0 = 0 := by
    funext j
    simp only [mix]
    split_ifs with hj
    · exact huS j hj
    · rfl
  rw [mix_jet, mix_jet, hv0, hu0, h0v, hu0'] at h
  have h' := congrArg (fun z : DualNumber (DualNumber L) => z.snd.snd) h
  simpa [trace_jet] using h'.symm

/-- The linear map keeping the coordinates of the inputs in `S` and zeroing the others. -/
def mixLeft : (Fin n → L) →ₗ[L] (Fin n → L) where
  toFun δ := mix S δ 0
  map_add' δ δ' := by
    funext j
    simp only [mix, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c δ := by
    funext j
    simp only [mix, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- The linear map keeping the coordinates of the inputs outside `S` and zeroing the others. -/
def mixRight : (Fin n → L) →ₗ[L] (Fin n → L) where
  toFun δ := mix S 0 δ
  map_add' δ δ' := by
    funext j
    simp only [mix, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c δ := by
    funext j
    simp only [mix, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- Zero-extension of vectors on `X` to `Fin n → L`. -/
def extendSub (X : Finset (Fin n)) : (↥X → L) →ₗ[L] (Fin n → L) where
  toFun v j := if hj : j ∈ X then v ⟨j, hj⟩ else 0
  map_add' v v' := by
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem extendSub_injective (X : Finset (Fin n)) :
    Function.Injective (extendSub X : (↥X → L) →ₗ[L] (Fin n → L)) := fun v v' h => by
  funext ⟨j, hj⟩
  simpa [extendSub, hj] using congrFun h j

/-- **One-sided forward determination.** A direction supported on `inputsIn S` that fixes the
forward signals to first order fixes every wire outside `S` to first order. -/
theorem jacobian_mulVec_eq_zero_of_forward {v : Fin n → L}
    (hvS : ∀ j, j ∉ inputsIn S → v j = 0)
    (hfwd : ∀ c ∈ forward p S, (jacobian (wirePolynomial P p) a *ᵥ v) c = 0)
    {w : Wire n s} (hw : w ∉ S) :
    (jacobian (wirePolynomial P p) a *ᵥ v) w = 0 := by
  have hin : ∀ j, j ∉ inputsIn S → jet a v 0 j = jet a 0 0 j := fun j hj => by
    simp [jet, hvS j hj]
  have hfw : ∀ c ∈ forward p S,
      p.trace (algebraInterpretation P (DualNumber (DualNumber L))) (jet a v 0) c =
        p.trace (algebraInterpretation P (DualNumber (DualNumber L))) (jet a 0 0) c :=
    fun c hc => by simp [trace_jet, hfwd c hc]
  have h := trace_eq_of_agree_forward p _ hin hfw w hw
  have h' := congrArg (fun z : DualNumber (DualNumber L) => z.fst.snd) h
  simpa [trace_jet] using h'

/-- **One-sided backward determination.** Symmetrically, a direction supported outside
`inputsIn S` that fixes the backward signals to first order fixes every wire in `S` to first
order. -/
theorem jacobian_mulVec_eq_zero_of_backward {u : Fin n → L}
    (huS : ∀ j ∈ inputsIn S, u j = 0)
    (hbwd : ∀ c ∈ backward p S, (jacobian (wirePolynomial P p) a *ᵥ u) c = 0)
    {w : Wire n s} (hw : w ∈ S) :
    (jacobian (wirePolynomial P p) a *ᵥ u) w = 0 := by
  have hin : ∀ j ∈ inputsIn S, jet a 0 u j = jet a 0 0 j := fun j hj => by
    simp [jet, huS j hj]
  have hbw : ∀ c ∈ backward p S,
      p.trace (algebraInterpretation P (DualNumber (DualNumber L))) (jet a 0 u) c =
        p.trace (algebraInterpretation P (DualNumber (DualNumber L))) (jet a 0 0) c :=
    fun c hc => by simp [trace_jet, hbwd c hc]
  have h := trace_eq_of_agree_backward p _ hin hbw w hw
  have h' := congrArg (fun z : DualNumber (DualNumber L) => z.snd.fst) h
  simpa [trace_jet] using h'

omit [CommRing K] [Algebra K L] in
/-- The subspace of directions on `X` annihilated by the rows `C` of `M`, extended by zero
outside `X`. -/
noncomputable def matSubKer {α : Type*} (M : Matrix α (Fin n) L) (X : Finset (Fin n))
    (C : Finset α) : Submodule L (Fin n → L) :=
  (LinearMap.ker (M.submatrix
    (fun c : ↥C => (c : α)) (fun j : ↥X => (j : Fin n))).mulVecLin).map (extendSub X)

omit [CommRing K] [Algebra K L] in
theorem support_of_mem_matSubKer {α : Type*} {M : Matrix α (Fin n) L} {X : Finset (Fin n)}
    {C : Finset α} {v : Fin n → L} (hv : v ∈ matSubKer M X C) {j : Fin n} (hj : j ∉ X) :
    v j = 0 := by
  rcases hv with ⟨v₀, -, rfl⟩
  simp [extendSub, hj]

omit [CommRing K] [Algebra K L] in
theorem mulVec_eq_zero_of_mem_matSubKer {α : Type*} {M : Matrix α (Fin n) L} {X : Finset (Fin n)}
    {C : Finset α} {v : Fin n → L} (hv : v ∈ matSubKer M X C) {c : α} (hc : c ∈ C) :
    (M *ᵥ v) c = 0 := by
  rcases Submodule.mem_map.mp hv with ⟨v₀, hv₀, rfl⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv₀
  have hc0 := congrFun hv₀ ⟨c, hc⟩
  simp only [Pi.zero_apply, mulVec, dotProduct, submatrix_apply] at hc0 ⊢
  have hsum : ∑ j : ↥X, M c j * extendSub X v₀ j = ∑ j, M c j * extendSub X v₀ j := by
    rw [Finset.sum_coe_sort X (fun j => M c j * extendSub X v₀ j)]
    exact Finset.sum_subset (Finset.subset_univ X) fun j _ hj => by simp [extendSub, hj]
  rw [← hsum, ← hc0]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [extendSub, j.2]

omit [CommRing K] [Algebra K L] in
theorem card_le_finrank_matSubKer_add_rank {α : Type*} (M : Matrix α (Fin n) L)
    (X : Finset (Fin n)) (C : Finset α) :
    X.card ≤ finrank L (matSubKer M X C) +
      (M.submatrix (fun c : ↥C => (c : α)) (fun j : ↥X => (j : Fin n))).rank := by
  set B := M.submatrix (fun c : ↥C => (c : α)) (fun j : ↥X => (j : Fin n))
  have hinj : Function.Injective (extendSub X ∘ₗ (LinearMap.ker B.mulVecLin).subtype) :=
    (extendSub_injective X).comp (Submodule.subtype_injective _)
  have hmap : finrank L (matSubKer M X C) = finrank L (LinearMap.ker B.mulVecLin) := by
    rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker := MultiOutput.Internal.finrank_ker_mulVecLin B
  rw [Fintype.card_coe] at hker
  omega

omit [CommRing K] [Algebra K L] in
theorem card_le_finrank_matSubKer_add {α : Type*} (M : Matrix α (Fin n) L)
    (X : Finset (Fin n)) (C : Finset α) :
    X.card ≤ finrank L (matSubKer M X C) + C.card := by
  have h₁ := card_le_finrank_matSubKer_add_rank M X C
  have h₂ := Matrix.rank_le_card_height
    (M.submatrix (fun c : ↥C => (c : α)) (fun j : ↥X => (j : Fin n)))
  rw [Fintype.card_coe] at h₂
  omega

/-- **The directed Taylor cut lemma.** There are subspaces `V` of directions on the inputs in `S`
and `W` of directions on the other inputs, with `|X_S| ≤ dim V + |forward S|` and
`|X_T| ≤ dim W + |backward S|` separately, such that `V` fixes every wire outside `S` and `W`
every wire in `S` to first order, and the Hessian of every wire pairs `V` with `W` to zero. -/
theorem exists_cut_directed : ∃ V W : Submodule L (Fin n → L),
    (∀ v ∈ V, ∀ j, j ∉ inputsIn S → v j = 0) ∧ (∀ u ∈ W, ∀ j ∈ inputsIn S, u j = 0) ∧
    (inputsIn S).card ≤ finrank L V + (forward p S).card ∧
    (inputsIn S)ᶜ.card ≤ finrank L W + (backward p S).card ∧
    (∀ v ∈ V, ∀ w, w ∉ S → (jacobian (wirePolynomial P p) a *ᵥ v) w = 0) ∧
    (∀ u ∈ W, ∀ w ∈ S, (jacobian (wirePolynomial P p) a *ᵥ u) w = 0) ∧
    ∀ v ∈ V, ∀ u ∈ W, ∀ w, v ⬝ᵥ (hessian (wirePolynomial P p w) a *ᵥ u) = 0 := by
  let V := matSubKer (jacobian (wirePolynomial P p) a) (inputsIn S) (forward p S)
  let W := matSubKer (jacobian (wirePolynomial P p) a) (inputsIn S)ᶜ (backward p S)
  have hV_supp : ∀ v ∈ V, ∀ j, j ∉ inputsIn S → v j = 0 :=
    fun _ hv _ hj => support_of_mem_matSubKer hv hj
  have hW_supp : ∀ u ∈ W, ∀ j ∈ inputsIn S, u j = 0 :=
    fun _ hu _ hj => support_of_mem_matSubKer hu (by simpa using hj)
  have hJV : ∀ v ∈ V, ∀ w, w ∉ S → (jacobian (wirePolynomial P p) a *ᵥ v) w = 0 :=
    fun v hv _ hw => jacobian_mulVec_eq_zero_of_forward P p S a (hV_supp v hv)
      (fun _ hc => mulVec_eq_zero_of_mem_matSubKer hv hc) hw
  have hJW : ∀ u ∈ W, ∀ w ∈ S, (jacobian (wirePolynomial P p) a *ᵥ u) w = 0 :=
    fun u hu _ hw => jacobian_mulVec_eq_zero_of_backward P p S a (hW_supp u hu)
      (fun _ hc => mulVec_eq_zero_of_mem_matSubKer hu hc) hw
  refine ⟨V, W, hV_supp, hW_supp, card_le_finrank_matSubKer_add _ (inputsIn S) (forward p S),
    card_le_finrank_matSubKer_add _ (inputsIn S)ᶜ (backward p S), hJV, hJW, ?_⟩
  intro v hv u hu w
  have hv_ker : v ∈ cutKernel P p S a := (mem_cutKernel P p S a).mpr fun c hc => by
    rcases Finset.mem_union.mp hc with hcf | hcb
    · exact mulVec_eq_zero_of_mem_matSubKer hv hcf
    · exact hJV v hv c (mem_backward.mp hcb).1
  have hu_ker : u ∈ cutKernel P p S a := (mem_cutKernel P p S a).mpr fun c hc => by
    rcases Finset.mem_union.mp hc with hcf | hcb
    · exact hJW u hu c (mem_forward.mp hcf).1
    · exact mulVec_eq_zero_of_mem_matSubKer hu hcb
  exact dotProduct_hessian_mulVec_eq_zero P p S a hv_ker hu_ker
    (fun j hj => hV_supp v hv j (mem_inputsIn.not.mpr hj))
    (fun j hj => hW_supp u hu j (mem_inputsIn.mpr hj)) w

/-- **The Taylor cut lemma.** There are subspaces `V` of directions on the inputs in `S` and `W`
of directions on the other inputs, of total dimension at least `n` minus the number of crossing
signals, such that `V` fixes every wire outside `S` and `W` every wire in `S` to first order,
and the Hessian of every wire pairs `V` with `W` to zero. -/
theorem exists_cut : ∃ V W : Submodule L (Fin n → L),
    (∀ v ∈ V, ∀ j, j ∉ inputsIn S → v j = 0) ∧ (∀ u ∈ W, ∀ j ∈ inputsIn S, u j = 0) ∧
    n ≤ finrank L V + finrank L W + ((forward p S).card + (backward p S).card) ∧
    (∀ v ∈ V, ∀ w, w ∉ S → (jacobian (wirePolynomial P p) a *ᵥ v) w = 0) ∧
    (∀ u ∈ W, ∀ w ∈ S, (jacobian (wirePolynomial P p) a *ᵥ u) w = 0) ∧
    ∀ v ∈ V, ∀ u ∈ W, ∀ w, v ⬝ᵥ (hessian (wirePolynomial P p w) a *ᵥ u) = 0 := by
  obtain ⟨V, W, hV, hW, hdimV, hdimW, hJV, hJW, hH⟩ := exists_cut_directed P p S a
  have hcompl : (inputsIn S).card + (inputsIn S)ᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  exact ⟨V, W, hV, hW, by omega, hJV, hJW, hH⟩

end Cut

/-! ## Linear algebra -/

section LinearAlgebra

variable {L : Type*} [Field L]

/-- **Orthogonal subspaces.** If `vᵀ B u = 0` for all `v ∈ V` and `u ∈ W`, then
`dim V + dim W + rank B` is at most the sum of the dimensions of the two spaces. -/
theorem finrank_add_finrank_add_rank_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ L) (V : Submodule L (ι → L)) (W : Submodule L (κ → L))
    (h : ∀ v ∈ V, ∀ u ∈ W, v ⬝ᵥ (B *ᵥ u) = 0) :
    finrank L V + finrank L W + B.rank ≤ Fintype.card ι + Fintype.card κ := by
  classical
  set bV := Module.finBasis L V
  set bW := Module.finBasis L W
  let RV : Matrix (Fin (finrank L V)) ι L := Matrix.of fun k => (bV k : ι → L)
  let CW : Matrix κ (Fin (finrank L W)) L := Matrix.of fun j l => (bW l : κ → L) j
  have hRV : RV.rank = finrank L V := by
    rw [Matrix.rank_eq_finrank_span_row]
    have hli : LinearIndependent L (fun k => (bV k : ι → L)) :=
      bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    rw [show (Set.range RV.row) = Set.range (fun k => (bV k : ι → L)) from rfl,
      finrank_span_eq_card hli, Fintype.card_fin]
  have hCW : CW.rank = finrank L W := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have hli : LinearIndependent L (fun l => (bW l : κ → L)) :=
      bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    rw [show (Set.range CW.col) = Set.range (fun l => (bW l : κ → L)) from rfl,
      finrank_span_eq_card hli, Fintype.card_fin]
  have hzero : RV * B * CW = 0 := by
    rw [Matrix.mul_assoc]
    ext k l
    have := h (bV k) (bV k).2 (bW l) (bW l).2
    simpa [RV, CW, Matrix.mul_apply, dotProduct, mulVec] using this
  have h₁ := MultiOutput.Internal.rank_add_rank_le_rank_mul_add_card RV B
  have h₂ := MultiOutput.Internal.rank_add_rank_le_rank_mul_add_card (RV * B) CW
  rw [hzero, Matrix.rank_zero] at h₂
  omega

/-- **Orthogonal subspaces with side conditions.** If `J₁` annihilates `V`, `J₂` annihilates `W`,
and `V` and `W` are orthogonal through `B`, then
`dim V + dim W + rank (fromBlocks B J₁ᵀ J₂ 0) ≤ |ι| + |κ|`. -/
theorem finrank_add_finrank_add_rank_fromBlocks_le
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (B : Matrix ι κ L) (J₁ : Matrix α ι L) (J₂ : Matrix β κ L)
    (V : Submodule L (ι → L)) (W : Submodule L (κ → L))
    (hV : ∀ v ∈ V, J₁ *ᵥ v = 0) (hW : ∀ u ∈ W, J₂ *ᵥ u = 0)
    (hB : ∀ v ∈ V, ∀ u ∈ W, v ⬝ᵥ (B *ᵥ u) = 0) :
    finrank L V + finrank L W + (Matrix.fromBlocks B J₁.transpose J₂ 0).rank ≤
      Fintype.card ι + Fintype.card κ := by
  let pairL : (↥V × (β → L)) →ₗ[L] (ι ⊕ β → L) :=
    { toFun := fun p => Sum.elim p.1.1 p.2
      map_add' := fun p q => by funext x; cases x <;> rfl
      map_smul' := fun c p => by funext x; cases x <;> rfl }
  let pairR : (↥W × (α → L)) →ₗ[L] (κ ⊕ α → L) :=
    { toFun := fun p => Sum.elim p.1.1 p.2
      map_add' := fun p q => by funext x; cases x <;> rfl
      map_smul' := fun c p => by funext x; cases x <;> rfl }
  have hL_inj : Function.Injective pairL := fun p q h =>
    Prod.ext (Subtype.ext (funext fun i => congrFun h (Sum.inl i)))
      (funext fun b => congrFun h (Sum.inr b))
  have hR_inj : Function.Injective pairR := fun p q h =>
    Prod.ext (Subtype.ext (funext fun j => congrFun h (Sum.inl j)))
      (funext fun a => congrFun h (Sum.inr a))
  set V' := LinearMap.range pairL
  set W' := LinearMap.range pairR
  have hdimV' : finrank L V' = finrank L V + Fintype.card β := by
    rw [LinearMap.finrank_range_of_inj hL_inj, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card]
  have hdimW' : finrank L W' = finrank L W + Fintype.card α := by
    rw [LinearMap.finrank_range_of_inj hR_inj, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card]
  have horth : ∀ v' ∈ V', ∀ u' ∈ W',
      v' ⬝ᵥ (Matrix.fromBlocks B J₁.transpose J₂ 0 *ᵥ u') = 0 := by
    rintro _ ⟨⟨⟨v, hv⟩, y⟩, rfl⟩ _ ⟨⟨⟨u, hu⟩, z⟩, rfl⟩
    simp only [pairL, pairR, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, mulVec,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero]
    have h₁ : ∑ i : ι, v i * (∑ j : κ, B i j * u j + ∑ a : α, J₁ a i * z a) =
        v ⬝ᵥ (B *ᵥ u) + ∑ a : α, z a * (J₁ *ᵥ v) a := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have h₂ : (∑ b : β, y b * ∑ j : κ, J₂ b j * u j) = ∑ b : β, y b * (J₂ *ᵥ u) b := rfl
    rw [h₁, h₂, hB v hv u hu, hV v hv, hW u hu]
    simp
  have h := finrank_add_finrank_add_rank_le (Matrix.fromBlocks B J₁.transpose J₂ 0) V' W' horth
  rw [hdimV', hdimW', Fintype.card_sum, Fintype.card_sum] at h
  omega

end LinearAlgebra

/-! ## Rank consequences -/

section Rank

variable {L : Type*} [Field L]

omit [CommRing K] in
/-- A sum over the members of `X` of a function vanishing outside `X` is its full sum. -/
theorem sum_subtype_of_support {X : Finset (Fin n)} (g : Fin n → L)
    (hg : ∀ j, j ∉ X → g j = 0) : ∑ j : ↥X, g j = ∑ j, g j := by
  rw [Finset.sum_coe_sort X g]
  exact Finset.sum_subset (Finset.subset_univ X) fun j _ hj => hg j hj

omit [CommRing K] in
/-- Restricting a subspace of vectors vanishing outside `X` to the coordinates in `X` keeps its
dimension. -/
theorem finrank_map_funLeft (V : Submodule L (Fin n → L)) (X : Finset (Fin n))
    (hV : ∀ v ∈ V, ∀ j, j ∉ X → v j = 0) :
    finrank L (V.map (LinearMap.funLeft L L (Subtype.val : ↥X → Fin n))) = finrank L V := by
  have hinj :
      Function.Injective (LinearMap.funLeft L L (Subtype.val : ↥X → Fin n) ∘ₗ V.subtype) := by
    intro v v' h
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ X
    · exact congrFun h ⟨j, hj⟩
    · rw [hV v v.2 j hj, hV v' v'.2 j hj]
  rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, Submodule.range_subtype]

omit [CommRing K] in
/-- **Kernel dimension.** A subspace of vectors vanishing outside `X` that the rows `Y` of `M`
annihilate has dimension at most `|X| - rank M[Y, X]`. -/
theorem finrank_add_blockRank_le (M : Matrix (Fin m) (Fin n) L) (Y : Finset (Fin m))
    (X : Finset (Fin n)) (V : Submodule L (Fin n → L)) (hV : ∀ v ∈ V, ∀ j, j ∉ X → v j = 0)
    (hM : ∀ v ∈ V, ∀ o ∈ Y, (M *ᵥ v) o = 0) :
    finrank L V + blockRank M Y X ≤ X.card := by
  set B := M.submatrix (fun i : ↥Y => (i : Fin m)) (fun j : ↥X => (j : Fin n))
  have hle : V.map (LinearMap.funLeft L L (Subtype.val : ↥X → Fin n)) ≤
      LinearMap.ker B.mulVecLin := by
    rintro _ ⟨v, hv, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext o
    have hsum := sum_subtype_of_support (X := X) (fun j => M o j * v j)
      fun j hj => by rw [hV v hv j hj, mul_zero]
    rw [Pi.zero_apply, ← hM v hv o o.2]
    simpa [B, mulVec, dotProduct, LinearMap.funLeft_apply] using hsum
  have h₁ := Submodule.finrank_mono hle
  rw [finrank_map_funLeft V X hV, MultiOutput.Internal.finrank_ker_mulVecLin,
    Fintype.card_coe] at h₁
  have h₂ : B.rank ≤ X.card := (Matrix.rank_le_card_width B).trans (by simp)
  change finrank L V + B.rank ≤ X.card
  omega

variable [Algebra K L] (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K)
  (p : Program σ n s) (S : Finset (Wire n s)) (a : Fin n → L)

theorem card_inputsIn_add_card_compl : (inputsIn S).card + (inputsIn S)ᶜ.card = n := by
  rw [Finset.card_add_card_compl, Fintype.card_fin]

/-- **The forward Jacobian consequence.** At every point, the block of the Jacobian of the outputs
from the inputs in `S` to the outputs outside `S` has rank at most `|forward p S|`. -/
theorem blockRank_jacobian_le_forward (out : Fin m → Wire n s) :
    blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)ᶜ
      (inputsIn S) ≤ (forward p S).card := by
  obtain ⟨V, _, hV, -, hdimV, -, hJV, -, -⟩ := exists_cut_directed P p S a
  have h₁ := finrank_add_blockRank_le (jacobian (fun o => wirePolynomial P p (out o)) a)
    (outputsIn out S)ᶜ (inputsIn S) V hV fun v hv o ho => by
      have hout : out o ∉ S := by simpa [outputsIn] using ho
      exact hJV v hv (out o) hout
  omega

/-- **The backward Jacobian consequence.** Symmetrically, the block of the Jacobian of the outputs
from the inputs outside `S` to the outputs in `S` has rank at most `|backward p S|`. -/
theorem blockRank_jacobian_le_backward (out : Fin m → Wire n s) :
    blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)
      (inputsIn S)ᶜ ≤ (backward p S).card := by
  obtain ⟨_, W, -, hW, -, hdimW, -, hJW, -⟩ := exists_cut_directed P p S a
  have h₂ := finrank_add_blockRank_le (jacobian (fun o => wirePolynomial P p (out o)) a)
    (outputsIn out S) (inputsIn S)ᶜ W (fun u hu j hj => hW u hu j (by simpa using hj))
    fun u hu o ho => by
      have hout : out o ∈ S := by simpa [outputsIn] using ho
      exact hJW u hu (out o) hout
  omega

/-- **The Jacobian consequence.** At every point, the blocks of the Jacobian of the outputs
from the inputs in `S` to the outputs outside `S`, and from the other inputs to the outputs in
`S`, have ranks summing to at most the number of crossing signals. -/
theorem blockRank_jacobian_add_blockRank_le (out : Fin m → Wire n s) :
    blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)ᶜ
        (inputsIn S) +
      blockRank (jacobian (fun o => wirePolynomial P p (out o)) a) (outputsIn out S)
        (inputsIn S)ᶜ ≤
        (forward p S).card + (backward p S).card :=
  Nat.add_le_add (blockRank_jacobian_le_forward P p S a out)
    (blockRank_jacobian_le_backward P p S a out)

theorem blockRank_le_of_orthogonal (H : Matrix (Fin n) (Fin n) L)
    (hH_orth : ∀ v u, (∀ w, v ⬝ᵥ (hessian (wirePolynomial P p w) a *ᵥ u) = 0) →
      v ⬝ᵥ (H *ᵥ u) = 0) :
    blockRank H (inputsIn S) (inputsIn S)ᶜ ≤ (forward p S).card + (backward p S).card := by
  obtain ⟨V, W, hV, hW, hdim, -, -, hH⟩ := exists_cut P p S a
  set X := inputsIn S
  set B := H.submatrix (fun i : ↥X => (i : Fin n)) (fun j : ↥Xᶜ => (j : Fin n))
  have hW' : ∀ u ∈ W, ∀ j, j ∉ Xᶜ → u j = 0 := fun u hu j hj => hW u hu j (by simpa using hj)
  have horth : ∀ v ∈ V.map (LinearMap.funLeft L L (Subtype.val : ↥X → Fin n)),
      ∀ u ∈ W.map (LinearMap.funLeft L L (Subtype.val : ↥Xᶜ → Fin n)), v ⬝ᵥ (B *ᵥ u) = 0 := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [← hH_orth v u (hH v hv u hu)]
    simp only [B, dotProduct, mulVec, LinearMap.funLeft_apply, Matrix.submatrix_apply]
    rw [sum_subtype_of_support (X := X) (fun i => v i * ∑ j : ↥Xᶜ, H i j * u j)
      fun i hi => by rw [hV v hv i hi, zero_mul]]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_subtype_of_support (X := Xᶜ) (fun j => H i j * u j)
      fun j hj => by rw [hW' u hu j hj, mul_zero]]
  have h₁ := finrank_add_finrank_add_rank_le B _ _ horth
  rw [finrank_map_funLeft V X hV, finrank_map_funLeft W Xᶜ hW', Fintype.card_coe,
    Fintype.card_coe, card_inputsIn_add_card_compl S] at h₁
  change B.rank ≤ _
  omega

/-- **The Hessian consequence.** At every point and for every combination `∑ₒ cₒ fₒ` of the
outputs, the block of its Hessian between the inputs in `S` and the other inputs has rank at
most the number of crossing signals. -/
theorem blockRank_hessian_le (out : Fin m → Wire n s) (c : Fin m → L) :
    blockRank (∑ o, c o • hessian (wirePolynomial P p (out o)) a) (inputsIn S) (inputsIn S)ᶜ ≤
      (forward p S).card + (backward p S).card :=
  blockRank_le_of_orthogonal P p S a _ fun v u h => by
    simp [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, h]

/-- **The unified first-and-second-order jet cut bound.** At every point `a` and for every
combination `H = ∑ₒ cₒ ∇² fₒ(a)` of the output Hessians, the combined block matrix formed by
`H[X_S, X_T]`, `J[O_T, X_S]ᵀ`, and `J[O_S, X_T]` has rank at most `|forward p S| + |backward p S|`. -/
theorem rank_fromBlocks_hessian_jacobian_le (out : Fin m → Wire n s) (c : Fin m → L) :
    (Matrix.fromBlocks
      ((∑ o, c o • hessian (wirePolynomial P p (out o)) a).submatrix
        (fun i : ↥(inputsIn S) => (i : Fin n)) (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)))
      ((jacobian (fun o => wirePolynomial P p (out o)) a).submatrix
        (fun o : ↥(outputsIn out S)ᶜ => (o : Fin m))
        (fun i : ↥(inputsIn S) => (i : Fin n))).transpose
      ((jacobian (fun o => wirePolynomial P p (out o)) a).submatrix
        (fun o : ↥(outputsIn out S) => (o : Fin m))
        (fun j : ↥(inputsIn S)ᶜ => (j : Fin n)))
      0).rank ≤ (forward p S).card + (backward p S).card := by
  obtain ⟨V, W, hV, hW, hdim, hJV, hJW, hH⟩ := exists_cut P p S a
  set H := ∑ o, c o • hessian (wirePolynomial P p (out o)) a
  set J := jacobian (fun o => wirePolynomial P p (out o)) a
  set X := inputsIn S
  set Y := outputsIn out S
  set B := H.submatrix (fun i : ↥X => (i : Fin n)) (fun j : ↥Xᶜ => (j : Fin n))
  set J₁ := J.submatrix (fun o : ↥Yᶜ => (o : Fin m)) (fun i : ↥X => (i : Fin n))
  set J₂ := J.submatrix (fun o : ↥Y => (o : Fin m)) (fun j : ↥Xᶜ => (j : Fin n))
  have hW' : ∀ u ∈ W, ∀ j, j ∉ Xᶜ → u j = 0 := fun u hu j hj => hW u hu j (by simpa using hj)
  have hV_J₁ : ∀ v' ∈ V.map (LinearMap.funLeft L L (Subtype.val : ↥X → Fin n)), J₁ *ᵥ v' = 0 := by
    rintro _ ⟨v, hv, rfl⟩
    funext o
    have hout : out o.1 ∉ S := by simpa [Y, outputsIn] using Finset.mem_compl.mp o.2
    have hJo : (J *ᵥ v) o.1 = 0 := hJV v hv (out o.1) hout
    have hsum := sum_subtype_of_support (X := X) (fun j => J o.1 j * v j)
      fun j hj => by rw [hV v hv j hj, mul_zero]
    rw [Pi.zero_apply, ← hJo]
    simpa [J₁, mulVec, dotProduct, LinearMap.funLeft_apply] using hsum
  have hW_J₂ : ∀ u' ∈ W.map (LinearMap.funLeft L L (Subtype.val : ↥Xᶜ → Fin n)), J₂ *ᵥ u' = 0 := by
    rintro _ ⟨u, hu, rfl⟩
    funext o
    have hout : out o.1 ∈ S := by simpa [Y, outputsIn] using o.2
    have hJo : (J *ᵥ u) o.1 = 0 := hJW u hu (out o.1) hout
    have hsum := sum_subtype_of_support (X := Xᶜ) (fun j => J o.1 j * u j)
      fun j hj => by rw [hW' u hu j hj, mul_zero]
    rw [Pi.zero_apply, ← hJo]
    simpa [J₂, mulVec, dotProduct, LinearMap.funLeft_apply] using hsum
  have horth : ∀ v ∈ V.map (LinearMap.funLeft L L (Subtype.val : ↥X → Fin n)),
      ∀ u ∈ W.map (LinearMap.funLeft L L (Subtype.val : ↥Xᶜ → Fin n)), v ⬝ᵥ (B *ᵥ u) = 0 := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨u, hu, rfl⟩
    have hHvu : v ⬝ᵥ (H *ᵥ u) = 0 := by
      simp only [H, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
        hH v hv u hu, smul_zero, Finset.sum_const_zero]
    rw [← hHvu]
    simp only [B, dotProduct, mulVec, LinearMap.funLeft_apply,
      Matrix.submatrix_apply]
    rw [sum_subtype_of_support (X := X) (fun i => v i * ∑ j : ↥Xᶜ, H i j * u j)
      fun i hi => by rw [hV v hv i hi, zero_mul]]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_subtype_of_support (X := Xᶜ) (fun j => H i j * u j)
      fun j hj => by rw [hW' u hu j hj, mul_zero]]
  have h₁ := finrank_add_finrank_add_rank_fromBlocks_le B J₁ J₂ _ _ hV_J₁ hW_J₂ horth
  rw [finrank_map_funLeft V X hV, finrank_map_funLeft W Xᶜ hW', Fintype.card_coe,
    Fintype.card_coe, card_inputsIn_add_card_compl S] at h₁
  omega

end Rank

end Algebraic.Cutwidth.MultiOutput.Taylor.Internal

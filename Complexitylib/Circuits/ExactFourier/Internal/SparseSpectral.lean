/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.RationalClearing
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Exact Fourier circuits: sparse spectral

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/SparseSpectral.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
noncomputable section
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Algebraic certificate for the real orthogonal reflection in the kernel, together
with its uniform sparse price.  Both annihilator equations are retained. -/
theorem spectral_price (p : MatrixPrice) (A : Matrix α α ℝ) (hA : A.IsSymm)
    (d : α → ℂ) (L : List (PairTerm α))
    (hL : RealMatrix.complex A=Matrix.diagonal d+(L.map PairTerm.direction).sum) :
    ∃ R T : Matrix α α ℂ,R*R=1 ∧ R.IsSymm ∧
      RealMatrix.complex A*(1+R)=0 ∧ 1-R=RealMatrix.complex A*T ∧
      p.value R≤(3:ℝ)/2*L.length+2*Fintype.card α := by
  obtain ⟨U,a,hU,hi,he⟩ := RealMatrix.diagonalization A hA
  let V := RealMatrix.complex U
  let b : α → ℂ := fun i => (a i : ℂ)
  have hV : IsUnit V := RealMatrix.unit U hU
  have hec : RealMatrix.complex A=Similarity.conj V (Matrix.diagonal b) := by
    rw [he,RealMatrix.map_mul,RealMatrix.map_mul,RealMatrix.map_diagonal,RealMatrix.inv U hU]
    rfl
  have hiv : V⁻¹=V.transpose := by rw [← RealMatrix.inv U hU,hi,RealMatrix.map_transpose]
  let R := Similarity.conj V (Matrix.diagonal (CayleyLimit.sign b))
  refine ⟨R,Similarity.conj V (Matrix.diagonal (CayleyLimit.reciprocal b)),
    CayleyLimit.reflection_square V hV b,CayleyLimit.reflection_symm V hiv b,?_,?_,?_⟩
  · rw [hec]; exact CayleyLimit.killed_sum V hV b
  · rw [hec]; exact CayleyLimit.difference_factor V hV b
  · apply CayleyLimit.price p V hV b
    intro t hp hm
    obtain ⟨Q,E,hQ0,hQ⟩ := exists_tangent p d L
    have heQ : Q.map (Polynomial.eval 0)=Similarity.conj V (Matrix.diagonal b) := by
      rw [← hec,hL]; exact hQ0
    rw [← heQ] at hp hm ⊢
    exact p.cayley_tangent Q E ((3:ℝ)/2*L.length) hQ t hp hm

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [LinearOrder α]

/-- Strictly upper-triangular positions carrying nonzero entries. -/
def pairs (A : Matrix α α ℂ) : Finset (α×α) := Finset.univ.filter (fun ij=>ij.1 < ij.2 ∧ A ij.1
    ij.2≠0)

@[simp] theorem mem_pairs (A : Matrix α α ℂ) (ij : α×α) : ij∈pairs A ↔ ij.1 < ij.2 ∧ A ij.1
    ij.2≠0 := by
  simp [pairs]

/-- The pair term associated with one nonzero off-diagonal entry of a symmetric matrix. -/
def term (A : Matrix α α ℂ) (hA : A.IsSymm) (ij : {ij // ij∈pairs A}) : PairTerm α :=
  ⟨ij.1.1,ij.1.2,ne_of_lt ((mem_pairs A ij).mp ij.2).1,A ij.1.1 ij.1.2,A ij.1.2 ij.1.1,
   ((mem_pairs A ij).mp ij.2).2,by
     have hh : A ij.1.2 ij.1.1=A ij.1.1 ij.1.2 := congrFun (congrFun hA ij.1.1) ij.1.2
     rw [hh]; exact ((mem_pairs A ij).mp ij.2).2⟩

/-- List the pair terms corresponding to all nonzero upper-triangular entries. -/
def terms (A : Matrix α α ℂ) (hA : A.IsSymm) : List (PairTerm α) :=
  (pairs A).attach.toList.map (term A hA)

@[simp] theorem terms_length (A : Matrix α α ℂ) (hA : A.IsSymm) : (terms A hA).length=(pairs
    A).card := by
  simp [terms]

theorem terms_sum (A : Matrix α α ℂ) (hA : A.IsSymm) :
    ((terms A hA).map PairTerm.direction).sum=
      ∑ ij∈pairs A,(Matrix.single ij.1 ij.2 (A ij.1 ij.2)+Matrix.single ij.2 ij.1 (A ij.2 ij.1))
        := by
  simp only [terms,List.map_map,Finset.sum_map_toList,Function.comp_def,term,PairTerm.direction]
  exact Finset.sum_attach (pairs A) (fun ij => (Matrix.single ij.1 ij.2 (A ij.1
    ij.2)+Matrix.single ij.2 ij.1 (A ij.2 ij.1)))

theorem decomposition (A : Matrix α α ℂ) (hA : A.IsSymm) :
    A=Matrix.diagonal (fun i=>A i i)+((terms A hA).map PairTerm.direction).sum := by
  rw [terms_sum,Finset.sum_add_distrib]
  ext i j
  have hl : (∑ ij∈pairs A,Matrix.single ij.1 ij.2 (A ij.1 ij.2)) i j=
      if (i,j)∈pairs A then A i j else 0 := by
    simp only [Matrix.sum_apply,Matrix.single_apply,← Prod.mk.injEq,Prod.mk.eta]
    simp
  have hr : (∑ ij∈pairs A,Matrix.single ij.2 ij.1 (A ij.2 ij.1)) i j=
      if (j,i)∈pairs A then A i j else 0 := by
    simp only [Matrix.sum_apply,Matrix.single_apply,and_comm (b := _=j),← Prod.mk.injEq,Prod.mk.eta]
    simp
  simp only [Matrix.add_apply,hl,hr,mem_pairs]
  by_cases hij : i=j
  · subst j; simp
  · rcases lt_or_gt_of_ne hij with hlt|hlt
    · simp [hij,hlt,not_lt_of_ge hlt.le]
    · simp [hij,hlt,not_lt_of_ge hlt.le,hA.apply i j]

theorem twice_pairs_le (A : Matrix α α ℂ) (hA : A.IsSymm) : 2*(pairs A).card≤nnz A := by
  classical
  let e : (α×α) ≃ (α×α) := Equiv.prodComm α α
  have hd : Disjoint (pairs A) ((pairs A).map e.toEmbedding) := by
    apply Finset.disjoint_left.mpr
    intro ij hi hj
    obtain ⟨ji,hji,he⟩ := Finset.mem_map.mp hj
    subst ij
    have h1 := ((mem_pairs A _).mp hi).1
    have h2 := ((mem_pairs A _).mp hji).1
    exact not_lt_of_ge h2.le h1
  have hs : pairs A∪(pairs A).map e.toEmbedding⊆support A := by
    intro ij hij
    rcases Finset.mem_union.mp hij with h|h
    · exact (mem_support A ij).mpr ((mem_pairs A ij).mp h).2
    · obtain ⟨ji,hji,rfl⟩ := Finset.mem_map.mp h
      apply (mem_support A _).mpr
      change A ji.2 ji.1≠0
      rw [show A ji.2 ji.1=A ji.1 ji.2 from congrFun (congrFun hA ji.1) ji.2]
      exact ((mem_pairs A _).mp hji).2
  have hh := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd,Finset.card_map] at hh
  simpa [two_mul,nnz] using hh

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [LinearOrder α]

/-- Uniform sparse reflection certificate, with supported unordered pairs counted exactly.
The annihilator identities characterize the reflection when A is real symmetric. -/
theorem exists_reflection (p : MatrixPrice) (A : Matrix α α ℂ) (hA : A.IsSymm)
    (hreal : ∀ i j,star (A i j)=A i j) :
    ∃ R T : Matrix α α ℂ,R*R=1 ∧ R.IsSymm ∧ A*(1+R)=0 ∧ 1-R=A*T ∧
      p.value R≤(3:ℝ)/2*(pairs A).card+2*Fintype.card α := by
  have hre := RealMatrix.complex_re A hreal
  obtain ⟨R,T,hR,hs,hp,hm,hc⟩ := spectral_price p (A.map Complex.re) (RealMatrix.re_symm A hA)
    (fun i=>A i i) (terms A hA) (by rw [hre]; exact decomposition A hA)
  rw [hre] at hp hm
  exact ⟨R,T,hR,hs,hp,hm,by simpa using hc⟩

theorem exists_reflection_nnz (p : MatrixPrice) (A : Matrix α α ℂ) (hA : A.IsSymm)
    (hreal : ∀ i j,star (A i j)=A i j) :
    ∃ R T : Matrix α α ℂ,R*R=1 ∧ R.IsSymm ∧ A*(1+R)=0 ∧ 1-R=A*T ∧
      p.value R≤(3:ℝ)/4*nnz A+2*Fintype.card α := by
  obtain ⟨R,T,hR,hs,hp,hm,hc⟩ := exists_reflection p A hA hreal
  refine ⟨R,T,hR,hs,hp,hm,?_⟩
  have hh : (2:ℝ)*(pairs A).card≤nnz A := by exact_mod_cast twice_pairs_le A hA
  linarith

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.SymLap
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

theorem relations (G J R T : Matrix α α ℂ) (M A : Matrix α α ℂ)
    (hJ : IsUnit J) (hG : IsUnit G) (hA : A=J*G*(1-M))
    (hs : A.IsSymm) (hk : A*(1+M)=0) (hp : A*(1+R)=0) (hm : 1-R=A*T) :
    M*(1+R)=1+R ∧ M.transpose*(1-R)=-(1-R) := by
  have hl : (1-M)*(1+R)=0 := by
    apply (hJ.mul hG).mul_left_cancel
    rw [← mul_assoc,← hA,hp,mul_zero]
  have hrt : (1+M.transpose)*A=0 := by
    have ht := congrArg Matrix.transpose hk
    simpa [Matrix.transpose_mul,Matrix.transpose_add,hs.eq] using ht
  constructor
  · rw [sub_mul,one_mul,sub_eq_zero] at hl
    exact hl.symm
  · have ht : (1+M.transpose)*(1-R)=0 := by rw [hm,← mul_assoc,hrt,zero_mul]
    rw [add_mul,one_mul] at ht
    exact eq_neg_of_add_eq_zero_right ht

theorem exists_tensor_reflection (p : MatrixPrice) (G J : Matrix α α ℂ)
    (hG : G*G=1) (hJ : MonomialMatrix J)
    (s : ℂ) (hs : s*s=1) (ht : J.transpose=s•J) (hc : J*G=G.transpose*J)
    (hrG : ∀ i j,star (G i j)=G i j) (hrJ : ∀ i j,star (J i j)=J i j) :
    ∃ R : Matrix (α×α) (α×α) ℂ, R*R=1 ∧ R.IsSymm ∧
      tensor G*(1+R)=1+R ∧ (tensor G).transpose*(1-R)=-(1-R) ∧
      p.value R≤(3:ℝ)/4*(2*nnz G*Fintype.card α)+2*(Fintype.card α)^2 := by
  let ord := LinearOrder.lift' (Fintype.equivFin (α×α)) (Fintype.equivFin (α×α)).injective
  let deq : DecidableEq (α×α) := inferInstance
  let : LinearOrder (α×α) := { ord with
    toDecidableEq := deq
    compare := fun a b => @compareOfLessAndEq _ a b ord.toLT (ord.toDecidableLT a b) deq
    compare_eq_compareOfLessAndEq := by intro a b; rfl }
  let A := symmetrized G J
  have hAs : A.IsSymm := symmetric G J s hs ht hc
  obtain ⟨R,T,hR,hrs,hp,hm,hpr⟩ := SparseReflection.exists_reflection_nnz p A hAs
    (real_entries G J hrG hrJ)
  have huG : IsUnit G := isUnit_iff_exists_inv'.mpr ⟨G,hG⟩
  have huJ := MonomialMatrix.unit J hJ
  have hfactor : A=(J⊗ₖJ)*(G⊗ₖ(1 : Matrix α α ℂ))*(1-tensor G) := by
    dsimp only [A,symmetrized]
    rw [lap_factor G hG,mul_assoc]
  have hk : A*(1+tensor G)=0 := by
    dsimp only [A,symmetrized]
    rw [mul_assoc,lap_kill G hG,mul_zero]
  obtain ⟨hrp,hrm⟩ := relations (G⊗ₖ(1 : Matrix α α ℂ)) (J⊗ₖJ) R T (tensor G) A
    (TensorTools.unit_tensor _ _ huJ huJ) (TensorTools.unit_tensor _ _ huG isUnit_one)
    hfactor hAs hk hp hm
  refine ⟨R,hR,hrs,hrp,hrm,?_⟩
  have hb : (nnz A : ℝ)≤2*nnz G*Fintype.card α := by exact_mod_cast support_bound G J hJ
  simp only [Fintype.card_prod,Nat.cast_mul] at hpr
  nlinarith

end ExactFourier.SymLap

end
end

section
noncomputable section
namespace ExactFourier.SignedBits

/-- The parity of a recursively represented bit string. -/
def parity : (m : ℕ) → Bits m → Bool
  | 0, _ => false
  | m+1, .inl i => parity m i
  | m+1, .inr i => !(parity m i)

theorem D_parity (m : ℕ) : ∀ i j,parity m i=parity m j → D m i j=0 := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    intro i j hij
    rcases i with i|i <;> rcases j with j|j
    · exact ih i j hij
    · rfl
    · have hn : i≠j := by intro he; subst j; simp [parity] at hij
      simp [D,hn]
    · change -(D m i j)=0
      have he : parity m i=parity m j := by simpa [parity] using hij
      rw [ih i j he,neg_zero]

theorem Gamma_parity (m : ℕ) : ∀ i j,parity (m+1) i=parity (m+1) j → Gamma m i j=0 := by
  intro i j hij
  rcases i with i|i <;> rcases j with j|j
  · exact D_parity m i j hij
  · have hn : i≠j := by intro he; subst j; simp [parity] at hij
    simp [Gamma,hn]
  · have hn : i≠j := by intro he; subst j; simp [parity] at hij
    simp [Gamma,hn]
  · change -(D m i j)=0
    have he : parity m i=parity m j := by simpa [parity] using hij
    rw [D_parity m i j he,neg_zero]

/-- Exchange the two halves precisely when the shorter bit string has odd parity. -/
def paritySwitch (m : ℕ) : Bits (m+1) → Bits (m+1)
  | .inl i => if parity m i then .inr i else .inl i
  | .inr i => if parity m i then .inl i else .inr i

theorem paritySwitch_involutive (m : ℕ) : Function.Involutive (paritySwitch m) := by
  intro i; rcases i with i|i <;> cases he : parity m i <;> simp [paritySwitch,he]

/-- Reorder bit strings so that the two halves separate even and odd parity. -/
def parityEquiv (m : ℕ) : (Bits m⊕Bits m) ≃ Bits (m+1) :=
  (paritySwitch_involutive m).toPerm

theorem parityEquiv_left (m : ℕ) (i : Bits m) : parity (m+1) (parityEquiv m (.inl i))=false := by
  change parity (m+1) (paritySwitch m (.inl i))=false
  cases he : parity m i <;> simp [paritySwitch,parity,he]

theorem parityEquiv_right (m : ℕ) (i : Bits m) : parity (m+1) (parityEquiv m (.inr i))=true := by
  change parity (m+1) (paritySwitch m (.inr i))=true
  cases he : parity m i <;> simp [paritySwitch,parity,he]

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier.GraphReflection
open scoped ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Exchange the two equal-sized coordinate blocks. -/
def swap : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 0 1 1 0

theorem swap_monomial
    {α : Type}  [DecidableEq α] : MonomialMatrix (swap (α := α)) := by
  refine ⟨Equiv.sumComm α α,fun _=>1,by simp,?_⟩
  intro i j; rcases i with i|i <;> rcases j with j|j <;> simp [swap,Matrix.one_apply]

theorem swap_square : swap (α := α)*swap=1 := by
  simp [swap,Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one]

/-- Apply a two-coordinate Hadamard transform to each pair of corresponding coordinates. -/
def hadamard : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 1 1 1 (-1)

theorem hadamard_square : hadamard (α := α)*hadamard=(2:ℂ)•1 := by
  simp [hadamard,Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one,← two_smul ℂ (1 : Matrix α α
    ℂ),Matrix.fromBlocks_smul]

theorem hadamard_unit : IsUnit (hadamard (α := α)) := by
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨(1/2:ℂ)•hadamard,?_⟩
  rw [Matrix.smul_mul,hadamard_square,smul_smul]
  norm_num

theorem hadamard_price (p : MatrixPrice) : p.value (hadamard (α := α))≤2*Fintype.card α := by
  let F : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;1,-1]
  have hF : IsUnit F := by rw [Matrix.isUnit_iff_isUnit_det,Matrix.det_fin_two]; norm_num [F]
  have he : hadamard (α := α)=pairLayer F := by rw [pairLayer_eq]; simp [hadamard,F]
  rw [he]; exact p.pair_layer F hF

/-- The block involution with off-diagonal blocks `B` and `B⁻¹`. -/
noncomputable def graph (B : Matrix α α ℂ) : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 0 B B⁻¹ 0

theorem graph_square (B : Matrix α α ℂ) (hB : IsUnit B) : graph B*graph B=1 := by
  have hi := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det _).mp hB)
  have hj := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det _).mp hB)
  simp [graph,Matrix.fromBlocks_multiply,hi,hj,← Matrix.fromBlocks_one]

theorem graph_price (p : MatrixPrice) (B : Matrix α α ℂ) (hB : IsUnit B) : p.value (graph
    B)=2*p.value B := by
  have hG : IsUnit (graph B) := isUnit_iff_exists_inv'.mpr ⟨graph B,graph_square B hB⟩
  have hh := p.monomial (graph B) 1 swap hG MonomialMatrix.one swap_monomial
  rw [one_mul] at hh
  have he : graph B*swap=Matrix.fromBlocks B 0 0 B⁻¹ := by
    simp [graph,swap,Matrix.fromBlocks_multiply]
  rw [he,p.directSum _ _ hB (Matrix.isUnit_nonsing_inv_iff.mpr hB),p.inverse _ hB] at hh
  linarith

theorem gram_unit (B : Matrix α α ℂ) (hB : ∀ i j,star (B i j)=B i j) : IsUnit (1+B.transpose*B)
    := by
  have he : B.conjTranspose=B.transpose := by ext i j; exact hB j i
  rw [← he]
  exact (Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self B)).isUnit

end ExactFourier.GraphReflection

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Kronecker

/-- One parity half of the tensor-square bit-string coordinate space. -/
abbrev Half (m : ℕ) := Bits m × Bits (m+1)
/-- Regroup tensor-square coordinates by the parity of the first factor. -/
def tensorParityEquiv (m : ℕ) : (Half m⊕Half m) ≃ Bits (m+1)×Bits (m+1) :=
  (Equiv.sumProdDistrib (Bits m) (Bits m) (Bits (m+1))).symm.trans
    (Equiv.prodCongr (parityEquiv m) (Equiv.refl _))

/-- The signed tensor involution written in coordinates grouped by parity. -/
def parityTensor (m : ℕ) : Matrix (Half m⊕Half m) (Half m⊕Half m) ℂ :=
  (SymLap.tensor (Gamma m)).submatrix (tensorParityEquiv m) (tensorParityEquiv m)

theorem parityTensor_square (m : ℕ) : parityTensor m*parityTensor m=1 := by
  rw [parityTensor,Matrix.submatrix_mul_equiv,SymLap.tensor_square _ (Gamma_square m)]
  simp

theorem parityTensor_diag_left (m : ℕ) : (parityTensor m).toBlocks₁₁=0 := by
  ext i j
  change Gamma m (parityEquiv m (.inl i.1)) (parityEquiv m (.inl j.1))*Gamma m i.2 j.2=0
  rw [Gamma_parity m _ _ (by rw [parityEquiv_left,parityEquiv_left]),zero_mul]

theorem parityTensor_diag_right (m : ℕ) : (parityTensor m).toBlocks₂₂=0 := by
  ext i j
  change Gamma m (parityEquiv m (.inr i.1)) (parityEquiv m (.inr j.1))*Gamma m i.2 j.2=0
  rw [Gamma_parity m _ _ (by rw [parityEquiv_right,parityEquiv_right]),zero_mul]

/-- The upper-right block of the parity decomposition of the signed tensor involution. -/
def graphB (m : ℕ) : Matrix (Half m) (Half m) ℂ := (parityTensor m).toBlocks₁₂

theorem graphB_unit (m : ℕ) : IsUnit (graphB m) := by
  have h := congrArg Matrix.toBlocks₁₁ (parityTensor_square m)
  rw [← Matrix.fromBlocks_toBlocks (parityTensor m),parityTensor_diag_left,
    parityTensor_diag_right] at h
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,zero_add,add_zero,
    Matrix.toBlocks_fromBlocks₁₁] at h
  rw [← Matrix.fromBlocks_one,Matrix.toBlocks_fromBlocks₁₁] at h
  exact isUnit_iff_exists_inv.mpr ⟨(parityTensor m).toBlocks₂₁,h⟩

theorem parityTensor_graph (m : ℕ) : parityTensor m=GraphReflection.graph (graphB m) := by
  have h := congrArg Matrix.toBlocks₂₂ (parityTensor_square m)
  rw [← Matrix.fromBlocks_toBlocks (parityTensor m),parityTensor_diag_left,
    parityTensor_diag_right] at h
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,zero_add,add_zero,
    Matrix.toBlocks_fromBlocks₂₂] at h
  rw [← Matrix.fromBlocks_one,Matrix.toBlocks_fromBlocks₂₂] at h
  have hi : (parityTensor m).toBlocks₂₁=(graphB m)⁻¹ := (Matrix.inv_eq_left_inv h).symm
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (parityTensor m)]
  rw [parityTensor_diag_left,parityTensor_diag_right,hi]
  rfl

theorem graphB_real (m : ℕ) : ∀ i j,star (graphB m i j)=graphB m i j := by
  intro i j
  change star (Gamma m (parityEquiv m (.inl i.1)) (parityEquiv m (.inr j.1))*Gamma m i.2 j.2)=_
  rw [star_mul,Gamma_star,Gamma_star]
  exact mul_comm _ _

end ExactFourier.SignedBits

end
end

end Complexity

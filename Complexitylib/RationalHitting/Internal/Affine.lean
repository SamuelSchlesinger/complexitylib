/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Evaluation
public import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Rational hitting lists: affine

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Affine.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity


namespace RationalHitting
open Matrix
namespace Affine
variable {n : ℕ}
/-- A constant coefficient and one rational coefficient per variable. -/
abbrev Form (n : ℕ) := ℚ × (Fin n → ℚ)
/-- The affine form with the given constant and zero variable coefficients. -/
def constant (a : ℚ) : Form n := (a,0)
/-- The affine coordinate form for one variable. -/
def varForm (i : Fin n) : Form n := (0,Pi.single i 1)
variable {R : Type*} [Ring R]
/-- Evaluate an affine form in a rational algebra, with coefficients on the left. -/
def eval (c : ℚ →+* R) (X : Fin n → R) : Form n →+ R where
  toFun := fun a => c a.1 + ∑ i, c (a.2 i) * X i
  map_zero' := by simp
  map_add' := by
    intro a b
    simp [map_add, add_mul, Finset.sum_add_distrib]
    abel
@[simp] lemma eval_constant (c : ℚ →+* R) (X : Fin n → R) (a : ℚ) :
    eval c X (constant a) = c a := by simp [eval,constant]
@[simp] lemma eval_variable (c : ℚ →+* R) (X : Fin n → R) (i : Fin n) :
    eval c X (varForm i) = X i := by
  simp [eval,varForm,Pi.single_apply, apply_ite]
/-- Regard a rational matrix as a matrix of constant affine forms. -/
def constMatrix {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ (Form n) := A.map constant
@[simp] lemma eval_constMatrix {ι κ : Type*} (c : ℚ →+* R) (X : Fin n → R)
    (A : Matrix ι κ ℚ) : (constMatrix A).map (eval c X) = A.map c := by
  ext i j
  exact eval_constant c X (A i j)
end Affine

namespace Formula
noncomputable section
variable {n : ℕ}

/-- The finite row and column index type of the formula's linear realization. -/
@[reducible] def Index : Formula n → Type
  | .var _ | .const _ => Unit ⊕ Unit
  | .add f g | .mul f g => Index f ⊕ Index g
  | .inv f => Index f ⊕ Unit

@[reducible] instance indexFintype : (h : Formula n) → Fintype (Index h)
  | .var _ | .const _ => inferInstanceAs (Fintype (Unit ⊕ Unit))
  | .add f g | .mul f g => letI := indexFintype f; letI := indexFintype g; inferInstanceAs
    (Fintype (Index f ⊕ Index g))
  | .inv f => letI := indexFintype f; inferInstanceAs (Fintype (Index f ⊕ Unit))

@[reducible] instance indexDecidableEq : (h : Formula n) → DecidableEq (Index h)
  | .var _ | .const _ => inferInstanceAs (DecidableEq (Unit ⊕ Unit))
  | .add f g | .mul f g => letI := indexDecidableEq f; letI := indexDecidableEq g;
    inferInstanceAs (DecidableEq (Index f ⊕ Index g))
  | .inv f => letI := indexDecidableEq f; inferInstanceAs (DecidableEq (Index f ⊕ Unit))

lemma card_index (f : Formula n) : Fintype.card f.Index = f.size + 1 := by
  induction f with
  | var i =>
    change Fintype.card (Unit ⊕ Unit) = 2
    exact (Fintype.card_sum (α := Unit) (β := Unit)).trans rfl
  | const a =>
    change Fintype.card (Unit ⊕ Unit) = 2
    exact (Fintype.card_sum (α := Unit) (β := Unit)).trans rfl
  | add f g ihf ihg =>
    change Fintype.card (Index f ⊕ Index g) = f.size + g.size + 1 + 1
    rw [Fintype.card_sum,ihf,ihg]
    omega
  | mul f g ihf ihg =>
    change Fintype.card (Index f ⊕ Index g) = f.size + g.size + 1 + 1
    rw [Fintype.card_sum,ihf,ihg]
    omega
  | inv f ih =>
    change Fintype.card (Index f ⊕ Unit) = f.size + 1 + 1
    rw [Fintype.card_sum,ih,Fintype.card_unique]

/-- The left row of the formula's linear realization. -/
def row : (f : Formula n) → Matrix Unit f.Index ℚ
  | .var _ | .const _ => fromCols 1 0
  | .add f g => fromCols (row f) (row g)
  | .mul f _g => fromCols (row f) 0
  | .inv _f => fromCols 0 (-1)
/-- The right column of the formula's linear realization. -/
def col : (f : Formula n) → Matrix f.Index Unit ℚ
  | .var _ | .const _ => fromRows 0 1
  | .add f g => fromRows (col f) (col g)
  | .mul _f g => fromRows 0 (col g)
  | .inv _f => fromRows 0 1

/-- The affine matrix pencil built recursively from a rational formula. -/
def pencil : (f : Formula n) → Matrix f.Index f.Index (Affine.Form n)
  | .var i => fromBlocks (Affine.constMatrix 1) (Matrix.of (fun _ _ => -Affine.varForm i)) 0
    (Affine.constMatrix 1)
  | .const a => fromBlocks (Affine.constMatrix 1) (Matrix.of (fun _ _ => -Affine.constant a)) 0
    (Affine.constMatrix 1)
  | .add f g => fromBlocks (pencil f) 0 0 (pencil g)
  | .mul f g => fromBlocks (pencil f) (-Affine.constMatrix (col f * row g)) 0 (pencil g)
  | .inv f => fromBlocks (pencil f) (Affine.constMatrix (col f)) (Affine.constMatrix (row f)) 0

variable {R : Type*} [Ring R] (c : ℚ →+* R) (X : Fin n → R)
/-- Evaluate all entries of the formula's affine pencil. -/
abbrev realized (f : Formula n) := (pencil f).map (Affine.eval c X)
/-- Map the realization's rational row into the target ring. -/
abbrev rowR (f : Formula n) := (row f).map c
/-- Map the realization's rational column into the target ring. -/
abbrev colR (f : Formula n) := (col f).map c
/-- Represent a scalar as a one-by-one matrix. -/
abbrev scalar (a : R) : Matrix Unit Unit R := (Matrix.uniqueRingEquiv (m := Unit)).symm a

lemma realized_add (f g : Formula n) : realized c X (.add f g) =
    fromBlocks (realized c X f) 0 0 (realized c X g) := by
  change (fromBlocks (pencil f) 0 0 (pencil g)).map (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp
lemma realized_mul (f g : Formula n) : realized c X (.mul f g) =
    fromBlocks (realized c X f) (-colR c f * rowR c g) 0 (realized c X g) := by
  change (fromBlocks (pencil f) (-Affine.constMatrix (col f * row g)) 0 (pencil g)).map
    (Affine.eval c X) = _
  rw [fromBlocks_map]
  rw [Matrix.map_neg _ (map_neg _)]
  simp [Matrix.map_mul,Matrix.neg_mul,rowR,colR]
lemma realized_inv (f : Formula n) : realized c X (.inv f) =
    fromBlocks (realized c X f) (colR c f) (rowR c f) 0 := by
  change (fromBlocks (pencil f) (Affine.constMatrix (col f)) (Affine.constMatrix (row f)) 0).map
    (Affine.eval c X) = _
  rw [fromBlocks_map]
  simp [rowR,colR]

lemma rowR_add (f g : Formula n) : rowR c (.add f g) = fromCols (rowR c f) (rowR c g) := by
  change (fromCols (row f) (row g)).map c = _
  exact fromCols_map _ _ _
lemma colR_add (f g : Formula n) : colR c (.add f g) = fromRows (colR c f) (colR c g) := by
  change (fromRows (col f) (col g)).map c = _
  exact fromRows_map _ _ _
lemma rowR_mul (f g : Formula n) : rowR c (.mul f g) = fromCols (rowR c f) 0 := by
  change (fromCols (row f) 0).map c = _
  rw [fromCols_map]
  simp
lemma colR_mul (f g : Formula n) : colR c (.mul f g) = fromRows 0 (colR c g) := by
  change (fromRows 0 (col g)).map c = _
  rw [fromRows_map]
  simp
lemma rowR_inv (f : Formula n) : rowR c (.inv f) = fromCols 0 (-1) := by
  change (fromCols (0 : Matrix Unit (Index f) ℚ) (-1)).map c = _
  rw [fromCols_map, Matrix.map_neg _ (map_neg _)]
  simp
lemma colR_inv (f : Formula n) : colR c (.inv f) = fromRows 0 1 := by
  change (fromRows (0 : Matrix (Index f) Unit ℚ) 1).map c = _
  rw [fromRows_map]
  simp

lemma leaf_realization (a : R) :
    ∃ M : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) R,
      fromBlocks 1 (-scalar a) 0 1 * M = 1 ∧
      M * fromBlocks 1 (-scalar a) 0 1 = 1 ∧
      NoncommBlocks.matMul (NoncommBlocks.matMul (fromCols (1 : Matrix Unit Unit R) 0) M)
        (fromRows (0 : Matrix Unit Unit R) (1 : Matrix Unit Unit R)) = scalar a := by
  refine ⟨fromBlocks 1 (scalar a) 0 1, ?_, ?_, ?_⟩
  · simp [fromBlocks_multiply]
  · simp [fromBlocks_multiply]
  · dsimp only [NoncommBlocks.matMul]
    rw [fromCols_mul_fromBlocks,fromCols_mul_fromRows]
    simp

/-- Exact affine realization of every defined original subtree. -/
theorem Eval.realization {f : Formula n} {a : R} (ha : Eval c X f a) :
    ∃ M : Matrix f.Index f.Index R,
      realized c X f * M = 1 ∧ M * realized c X f = 1 ∧
      rowR c f * M * colR c f = scalar a := by
  induction ha with
  | var i =>
    have hL : realized c X (.var i) = fromBlocks 1 (-scalar (X i)) 0 1 := by
      change (fromBlocks (Affine.constMatrix (1 : Matrix Unit Unit ℚ))
        (Matrix.of (fun _ _ => -Affine.varForm i)) 0 (Affine.constMatrix 1)).map (Affine.eval c
          X) = _
      rw [fromBlocks_map]
      simp only [Affine.eval_constMatrix, Matrix.map_one c (map_zero c) (map_one c),
        Matrix.map_zero, map_zero]
      congr 1 ; ext i j ; simp [scalar,Matrix.map,Matrix.of_apply]
    have hu : rowR c (.var i) = fromCols 1 0 := by
      change (fromCols (1 : Matrix Unit Unit ℚ) 0).map c = _
      rw [fromCols_map]; simp
    have hv : colR c (.var i) = fromRows 0 1 := by
      change (fromRows 0 (1 : Matrix Unit Unit ℚ)).map c = _
      rw [fromRows_map]; simp
    rw [hL,hu,hv]
    exact leaf_realization (X i)
  | const a =>
    have hL : realized c X (.const a) = fromBlocks 1 (-scalar (c a)) 0 1 := by
      change (fromBlocks (Affine.constMatrix (1 : Matrix Unit Unit ℚ))
        (Matrix.of (fun _ _ => -Affine.constant a)) 0 (Affine.constMatrix 1)).map (Affine.eval c
          X) = _
      rw [fromBlocks_map]
      simp only [Affine.eval_constMatrix, Matrix.map_one c (map_zero c) (map_one c),
        Matrix.map_zero, map_zero]
      congr 1 ; ext i j ; simp [scalar,Matrix.map,Matrix.of_apply]
    have hu : rowR (n := n) c (.const a) = fromCols 1 0 := by
      change (fromCols (1 : Matrix Unit Unit ℚ) 0).map c = _
      rw [fromCols_map]; simp
    have hv : colR (n := n) c (.const a) = fromRows 0 1 := by
      change (fromRows 0 (1 : Matrix Unit Unit ℚ)).map c = _
      rw [fromRows_map]; simp
    rw [hL,hu,hv]
    exact leaf_realization (c a)
  | @add f g a b hf hg ihf ihg =>
    obtain ⟨Mf,hf1,hf2,hfr⟩ := ihf
    obtain ⟨Mg,hg1,hg2,hgr⟩ := ihg
    refine ⟨fromBlocks Mf 0 0 Mg, ?_, ?_, ?_⟩
    · rw [realized_add,fromBlocks_multiply]
      simp [hf1,hg1,Matrix.mul_zero,Matrix.zero_mul]
    · rw [realized_add,fromBlocks_multiply]
      simp [hf2,hg2,Matrix.mul_zero,Matrix.zero_mul]
    · rw [rowR_add,colR_add,fromCols_mul_fromBlocks,fromCols_mul_fromRows]
      simp only [Matrix.mul_zero,add_zero,zero_add,hfr,hgr]
      exact (map_add (Matrix.uniqueRingEquiv (m := Unit)).symm a b).symm
  | @mul f g a b hf hg ihf ihg =>
    obtain ⟨Mf,hf1,hf2,hfr⟩ := ihf
    obtain ⟨Mg,hg1,hg2,hgr⟩ := ihg
    let B := Mf * colR c f * rowR c g * Mg
    have hB1 : realized c X f * B = colR c f * rowR c g * Mg := by
      simp [B,← Matrix.mul_assoc,hf1,Matrix.one_mul]
    have hB2 : B * realized c X g = Mf * colR c f * rowR c g := by
      simp [B,Matrix.mul_assoc,hg2,Matrix.mul_one]
    refine ⟨fromBlocks Mf B 0 Mg, ?_, ?_, ?_⟩
    · rw [realized_mul,fromBlocks_multiply]
      simp [hf1,hg1,hB1,Matrix.mul_zero,Matrix.zero_mul,Matrix.neg_mul]
    · rw [realized_mul,fromBlocks_multiply]
      simp [hf2,hg2,hB2,Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_neg,Matrix.neg_mul,←
        Matrix.mul_assoc]
    · rw [rowR_mul,colR_mul,fromCols_mul_fromBlocks,fromCols_mul_fromRows]
      simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
      simp only [B]
      have hh : rowR c f * (Mf * colR c f * rowR c g * Mg) * colR c g =
          (rowR c f * Mf * colR c f) * (rowR c g * Mg * colR c g) := by
        simp only [Matrix.mul_assoc]
      rw [hh,hfr,hgr]
      exact (map_mul (Matrix.uniqueRingEquiv (m := Unit)).symm a b).symm
  | @inv f a b hf hab hba ih =>
    obtain ⟨Mf,hf1,hf2,hfr⟩ := ih
    rw [realized_inv,rowR_inv,colR_inv]
    exact NoncommBlocks.schur_inverse _ _ _ _ (scalar a) (scalar b)
      hf1 hf2 hfr (by rw [← map_mul,hab,map_one]) (by rw [← map_mul,hba,map_one])

end
end Formula
end RationalHitting

namespace RationalHitting.Formula
open Matrix
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]
variable (c : ℚ →+* R) (X : Fin n → R)

/-- The list retains occurrences, not just distinct subexpressions. -/
def inverseNodes : Formula n → List (Formula n)
  | .var _ | .const _ => []
  | .add f g | .mul f g => inverseNodes f ++ inverseNodes g
  | .inv f => .inv f :: inverseNodes f

/-- `.inv f` here denotes the root augmentation pencil, not a new counted gate. -/
def certificates (f : Formula n) := inverseNodes f ++ [.inv f]

lemma Eval.pencil_isUnit {f : Formula n} {a : R} (ha : Eval c X f a) :
    IsUnit (realized c X f) := by
  obtain ⟨M,hM,hM',_⟩ := ha.realization
  exact isUnit_iff_exists.mpr ⟨M,hM,hM'⟩

lemma Eval.augmented_isUnit_iff {f : Formula n} {a : R} (ha : Eval c X f a) :
    IsUnit (realized c X (.inv f)) ↔ IsUnit a := by
  obtain ⟨M,hM,hM',hr⟩ := ha.realization
  rw [realized_inv,NoncommBlocks.schur_unit_iff _ _ _ _ hM hM',hr]
  constructor
  · intro h; simpa using h.map (Matrix.uniqueRingEquiv (m := Unit))
  · intro h; exact h.map (Matrix.uniqueRingEquiv (m := Unit)).symm

lemma Eval.inverseNodes_units {f : Formula n} {a : R} (ha : Eval c X f a) :
    ∀ h ∈ inverseNodes f, IsUnit (realized c X h) := by
  induction ha with
  | var i => simp [inverseNodes]
  | const a => simp [inverseNodes]
  | add hf hg ihf ihg =>
    simpa only [inverseNodes,List.mem_append,or_imp,forall_and] using And.intro ihf ihg
  | mul hf hg ihf ihg =>
    simpa only [inverseNodes,List.mem_append,or_imp,forall_and] using And.intro ihf ihg
  | @inv f a b hf hab hba ih =>
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact (Eval.inv hf hab hba).pencil_isUnit
    · exact ih h hh

lemma eval_of_inverseNodes_units (f : Formula n)
    (hu : ∀ h ∈ inverseNodes f, IsUnit (realized c X h)) :
    ∃ a, Eval c X f a := by
  induction f with
  | var i => exact ⟨X i,.var i⟩
  | const a => exact ⟨c a,.const a⟩
  | add f g ihf ihg =>
    obtain ⟨a,ha⟩ := ihf (fun h hh => hu h (List.mem_append_left _ hh))
    obtain ⟨b,hb⟩ := ihg (fun h hh => hu h (List.mem_append_right _ hh))
    exact ⟨a+b,.add ha hb⟩
  | mul f g ihf ihg =>
    obtain ⟨a,ha⟩ := ihf (fun h hh => hu h (List.mem_append_left _ hh))
    obtain ⟨b,hb⟩ := ihg (fun h hh => hu h (List.mem_append_right _ hh))
    exact ⟨a*b,.mul ha hb⟩
  | inv f ih =>
    obtain ⟨a,ha⟩ := ih (fun h hh => hu h (List.mem_cons_of_mem _ hh))
    have hua := ha.augmented_isUnit_iff.mp (hu (.inv f) (List.mem_cons_self ..))
    obtain ⟨b,hab,hba⟩ := isUnit_iff_exists.mp hua
    exact ⟨b,.inv ha hab hba⟩

/-- Full original-tree definedness and invertible final value are equivalent to
all affine-pencil certificates. No rational cancellation is performed. -/
theorem certificates_iff (f : Formula n) :
    (∀ h ∈ certificates f, IsUnit (realized c X h)) ↔
      ∃ a, Eval c X f a ∧ IsUnit a := by
  constructor
  · intro hu
    obtain ⟨a,ha⟩ := eval_of_inverseNodes_units c X f
      (fun h hh => hu h (List.mem_append_left _ hh))
    exact ⟨a,ha,ha.augmented_isUnit_iff.mp (hu (.inv f) (by simp [certificates]))⟩
  · rintro ⟨a,ha,hua⟩ h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact Eval.inverseNodes_units c X ha h hh
    · have heq : h = .inv f := by simpa using hh
      subst h
      exact ha.augmented_isUnit_iff.mpr hua

lemma inverseNodes_length (f : Formula n) : (inverseNodes f).length ≤ f.size := by
  induction f <;> simp_all [inverseNodes,size] <;> omega

lemma size_le_of_mem_inverseNodes {f h : Formula n} (hh : h ∈ inverseNodes f) :
    h.size ≤ f.size := by
  induction f with
  | var i => simp [inverseNodes] at hh
  | const a => simp [inverseNodes] at hh
  | add f g ihf ihg =>
    rcases List.mem_append.mp hh with hh | hh
    · have := ihf hh; simp only [size]; omega
    · have := ihg hh; simp only [size]; omega
  | mul f g ihf ihg =>
    rcases List.mem_append.mp hh with hh | hh
    · have := ihf hh; simp only [size]; omega
    · have := ihg hh; simp only [size]; omega
  | inv f ih =>
    rcases List.mem_cons.mp hh with rfl | hh
    · rfl
    · have := ih hh; simp only [size]; omega

lemma certificate_bounds (f : Formula n) (s : ℕ) (hs : 1 ≤ s) (hf : f.size ≤ s) :
    (certificates f).length ≤ s+1 ∧
      ∀ h ∈ certificates f, 0 < Fintype.card h.Index ∧ Fintype.card h.Index ≤ 2*s+1 := by
  refine ⟨?_,?_⟩
  · simp only [certificates,List.length_append,List.length_singleton]
    have := inverseNodes_length f
    omega
  · intro h hh
    rw [card_index]
    refine ⟨by omega,?_⟩
    rcases List.mem_append.mp hh with hh | hh
    · have := size_le_of_mem_inverseNodes hh
      omega
    · have heq : h = .inv f := by simpa using hh
      rw [heq,size]
      omega

end
end RationalHitting.Formula

namespace RationalHitting.Affine
open Matrix
open scoped BigOperators
noncomputable section
variable {n : ℕ} {R : Type*} [Ring R]

/-- The homogeneous coefficient, with index zero reserved for the constant term. -/
def coeff (a : Form n) : Fin (n+1) → ℚ := Fin.cases a.1 a.2

/-- Evaluate the homogeneous form on an extra constant coordinate. -/
def homogeneous (c : ℚ →+* R) (Z : Fin (n+1) → R) (a : Form n) : R :=
  ∑ i, c (coeff a i) * Z i

lemma homogeneous_one (c : ℚ →+* R) (X : Fin n → R) (a : Form n) :
    homogeneous c (Fin.cases 1 X) a = eval c X a := by
  simp [homogeneous,coeff,Fin.sum_univ_succ,eval]

lemma normalized [Algebra ℚ R] (Z : Fin (n+1) → R) (u : R) (hu : Z 0*u=1)
    (a : Form n) :
    homogeneous (algebraMap ℚ R) Z a =
      Z 0 * eval (algebraMap ℚ R) (fun i => u * Z i.succ) a := by
  change (∑ i, (algebraMap ℚ R) (coeff a i) * Z i) =
    Z 0 * ((algebraMap ℚ R) a.1 + ∑ i, (algebraMap ℚ R) (a.2 i) * (u*Z i.succ))
  rw [Fin.sum_univ_succ]
  simp only [coeff,Fin.cases_zero,Fin.cases_succ,mul_add,Finset.mul_sum]
  congr 1
  · exact (Algebra.commutes a.1 (Z 0))
  · apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc,← (Algebra.commutes (a.2 i) (Z 0)),mul_assoc,
      ← mul_assoc (Z 0) u,hu,one_mul]

lemma normalized_pencil {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ R]
    (L : Matrix ι ι (Form n)) (Z : Fin (n+1) → R) (u : R) (hu : Z 0*u=1) :
    L.map (homogeneous (algebraMap ℚ R) Z) =
      Matrix.scalar ι (Z 0) * L.map (eval (algebraMap ℚ R) (fun i => u*Z i.succ)) := by
  funext i j
  change homogeneous (algebraMap ℚ R) Z (L i j) =
    (Matrix.diagonal (fun _ : ι => Z 0) * L.map (eval (algebraMap ℚ R) (fun i => u*Z i.succ)) :
      Matrix ι ι R) i j
  rw [Matrix.diagonal_mul]
  exact normalized Z u hu (L i j)

lemma normalized_pencil_unit {ι : Type*} [Fintype ι] [DecidableEq ι] [Algebra ℚ R]
    (L : Matrix ι ι (Form n)) (Z : Fin (n+1) → R) (z : Rˣ) (hz : (z : R)=Z 0)
    (hL : IsUnit (L.map (homogeneous (algebraMap ℚ R) Z))) :
    IsUnit (L.map (eval (algebraMap ℚ R) (fun i => (↑z⁻¹ : R)*Z i.succ))) := by
  have hu : Z 0*(↑z⁻¹ : R)=1 := by rw [← hz]; exact z.val_inv
  rw [normalized_pencil L Z (↑z⁻¹ : R) hu] at hL
  exact (z.isUnit.map (Matrix.scalar ι) |>.mul_left_iff).mp (by simpa [hz] using hL)

variable {K : Type*} [Field K] [CharZero K] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Reindexing a pencil's coefficients does not alter its matrix evaluation. -/
lemma eval_reindex.{v_2, v_3, v_4, v_5} {n : ℕ} {K : Type v_2} [Field K]
  [CharZero K] {ι : Type v_3} {κ : Type v_4}   [Fintype κ]
  [DecidableEq κ] (L : Matrix ι ι (RationalHitting.Affine.Form n)) (X : Fin n → Matrix κ κ K)
  {ι' : Type v_5} (e : ι ≃ ι') :
  ((Matrix.reindex e e) L).map ⇑(RationalHitting.Affine.eval (algebraMap ℚ (Matrix κ κ K)) X) =
    (Matrix.reindex e e) (L.map ⇑(RationalHitting.Affine.eval (algebraMap ℚ (Matrix κ κ K)) X))
      := rfl

/-- Homogeneous affine coefficients give exactly the ordinary Kronecker pencil. -/
lemma homogeneous_flat.{v_2, v_3, v_4} {n : ℕ} {K : Type v_2} [Field K]
  [CharZero K] {ι : Type v_3} {κ : Type v_4} [Fintype ι]  [Fintype κ]
  [DecidableEq κ] (L : Matrix ι ι (RationalHitting.Affine.Form n))
  (Z : Fin (n + 1) → Matrix κ κ K) :
  (Matrix.compRingEquiv ι κ K)
      (L.map (RationalHitting.Affine.homogeneous (algebraMap ℚ (Matrix κ κ K)) Z)) =
    fun a b => ∑ r, (algebraMap ℚ K) (RationalHitting.Affine.coeff (L a.1 b.1) r) * Z r a.2 b.2
      := by
  funext ⟨i,a⟩ ⟨j,b⟩
  change (∑ r, (algebraMap ℚ (Matrix κ κ K)) (coeff (L i j) r) * Z r) a b = _
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  change (Matrix.diagonal (fun _ : κ => (algebraMap ℚ K) (coeff (L i j) r)) * Z r : Matrix κ κ
    K) a b = _
  rw [Matrix.diagonal_mul]

end
end RationalHitting.Affine

end Complexity

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Certificates

/-!
# Rational hitting lists: generator

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Generator.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

/-- Dimension after expanding the cyclotomic matrix representation over the rationals. -/
def matrixDimension (e : ℕ) : ℕ := CyclotomicRing.dimension e * CyclotomicRing.degree e

/-- Entrywise regular representation, flattening and fixed row-major reindexing. -/
def regular (e : ℕ) : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
    (CyclotomicRing.R e) →+* Mat (matrixDimension e) :=
  (Matrix.reindexRingEquiv ℚ ((Equiv.prodCongr (ZMod.finEquiv (CyclotomicRing.dimension
    e)).symm.toEquiv
    (Equiv.refl (Fin (CyclotomicRing.degree e)))).trans finProdFinEquiv)).toRingHom.comp
    ((Matrix.compRingEquiv _ _ ℚ).toRingHom.comp (CyclotomicRing.rho e).toRingHom.mapMatrix)

/-- The fixed lexicographic three-dimensional integer grid, encoded by Fin H. -/
def grid (H : ℕ) : List (Fin 3 → Fin H) :=
  (List.finRange H).flatMap fun t => (List.finRange H).flatMap fun p =>
    (List.finRange H).map fun r => ![t,p,r]

lemma mem_grid (H : ℕ) (x : Fin 3 → Fin H) : x ∈ grid H := by
  simp only [grid,List.mem_flatMap,List.mem_map]
  refine ⟨x 0,by simp, x 1,by simp,x 2,by simp,?_⟩
  funext i
  fin_cases i <;> rfl

lemma grid_length (H : ℕ) : (grid H).length = H^3 := by
  simp [grid,List.length_flatMap,pow_succ,Nat.mul_assoc]

/-- The polynomial lift is evaluated over the exact rational quotient. -/
def specializedLift (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n+1)) :
    Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e) :=
  (eval₂Hom (RingHom.id _) (fun j => (x j : CyclotomicRing.R e))).mapMatrix
    (PencilCertificates.lifts (CyclotomicRing.character e) N n i)

/-- Expand a specialized lift as a rational matrix. -/
def rationalLift (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n+1)) : Mat (matrixDimension e) :=
    regular e (specializedLift n N e x i)

/-- Normalize all variable matrices by the zeroth matrix. -/
def tupleAt (n N e : ℕ) (x : Fin 3 → ℕ) : Tuple n (matrixDimension e) :=
  fun i => (rationalLift n N e x 0)⁻¹ * rationalLift n N e x i.succ

/-- The filtering step tests only Z_0, and receives no formula. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (matrixDimension e)) :=
  if (rationalLift n N e x 0).det = 0 then none else some (tupleAt n N e x)

/-- Collect the normalized tuples emitted at all grid points. -/
def output (n N e H : ℕ) : Output n where
  dimension := matrixDimension e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (grid H).filterMap (fun x => atPoint n N e (fun i => (x i).val+1))

lemma length_output_le (n N e H : ℕ) : (output n N e H).tuples.length ≤ H^3 :=
  (List.length_filterMap_le _ _).trans_eq (grid_length H)

/-- The actual emitted rational normalization is the homomorphic image of the
quotient normalization. Consequently every original inverse occurrence is kept. -/
lemma transfer {n N e : ℕ} (x : Fin 3 → ℕ) (f : Formula n)
    (z : (Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e))ˣ)
    (hz : (z : Matrix _ _ _) = specializedLift n N e x 0)
    (v : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e))
    (hf : f.Eval (algebraMap ℚ _) (fun i => (↑z⁻¹ : Matrix _ _ _) * specializedLift n N e x
      i.succ) v)
    (hu : IsUnit v) :
    ∃ a, Evaluates f (tupleAt n N e x) a ∧ IsUnit a := by
  have hzinv : regular e (↑z⁻¹ : Matrix _ _ _) = (rationalLift n N e x 0)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    change regular e (↑z⁻¹ : Matrix _ _ _) * regular e (specializedLift n N e x 0) = 1
    simp only [← map_mul,← hz,Units.inv_mul,map_one]
  refine ⟨regular e v,?_,hu.map (regular e)⟩
  have hh := hf.map (regular e)
  rw [RingHom.ext_rat ((regular e).comp (algebraMap ℚ _)) (algebraMap ℚ _)] at hh
  change f.Eval (algebraMap ℚ _) (tupleAt n N e x) (regular e v)
  change f.Eval (algebraMap ℚ _) (fun i => (regular e (specializedLift n N e x 0))⁻¹ * regular e
    (specializedLift n N e x i.succ)) (regular e v)
  simpa only [map_mul,hzinv,rationalLift] using hh

lemma emitted {n N e H : ℕ} (x : Fin 3 → Fin H)
    (hz : IsUnit (specializedLift n N e (fun i => (x i).val+1) 0)) :
    tupleAt n N e (fun i => (x i).val+1) ∈ (output n N e H).tuples := by
  apply List.mem_filterMap.mpr
  refine ⟨x,mem_grid H x,?_⟩
  have hq := (Matrix.isUnit_iff_isUnit_det _).mp (hz.map (regular e))
  have hne : (rationalLift n N e (fun i => (x i).val+1) 0).det ≠ 0 := hq.ne_zero
  simp [atPoint,hne]

end
end RationalHitting.Generator

namespace RationalHitting.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

/-- The Hahn field containing the algebraic witnesses for the generator. -/
abbrev WitnessField := HahnSeries QuantumLift.Exponents ℂ
instance witnessCharZero : CharZero WitnessField :=
  CharZero.of_addMonoidHom (HahnSeries.C : ℂ →+* WitnessField).toAddMonoidHom
    (map_one (HahnSeries.C : ℂ →+* WitnessField)) HahnSeries.C_injective

/-- Embed the cyclotomic field into the Hahn witness field. -/
def witnessEmbedding (e : ℕ) : CyclotomicRing.R e →+* WitnessField :=
  (HahnSeries.C : ℂ →+* WitnessField).comp (CyclotomicRing.intoComplex e).toRingHom

/-- Reindex the formula's pencil by its explicit finite dimension. -/
def finPencil {n : ℕ} (f : Formula n) :
    Matrix (Fin (Fintype.card f.Index)) (Fin (Fintype.card f.Index)) (Affine.Form n) :=
  (Formula.pencil f).reindex (Fintype.equivFin f.Index) (Fintype.equivFin f.Index)

lemma finPencil_unit {n : ℕ} {R : Type*} [Ring R] (c : ℚ →+* R)
    (X : Fin n → R) (f : Formula n) :
    IsUnit ((finPencil f).map (Affine.eval c X)) ↔ IsUnit (Formula.realized c X f) := by
  let E := Matrix.reindexRingEquiv R (Fintype.equivFin f.Index)
  change IsUnit (E (Formula.realized c X f)) ↔ IsUnit (Formula.realized c X f)
  constructor
  · intro h; simpa using h.map E.symm
  · exact fun h => h.map E

/-- A one-by-one constant pencil used to enforce normalization. -/
def onePencil (n : ℕ) : Matrix (Fin 1) (Fin 1) (Affine.Form n) := fun _ _ => Affine.constant 1

/-- Determinant polynomials whose simultaneous nonvanishing certifies a hit. -/
def conditions {n : ℕ} (N e : ℕ) (f : Formula n) : List (MvPolynomial (Fin 3) (CyclotomicRing.R
    e)) :=
  PencilCertificates.determinant (CyclotomicRing.character e) N (onePencil n) ::
    f.certificates.map (fun h => PencilCertificates.determinant (CyclotomicRing.character e) N
      (finPencil h))

lemma condition_nonzero {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.size ≤ s)
    (hnz : Nonzero f)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N+2*(n+1)^3*(2*s+1))
    (hM : (2*s+1)*(2*(n+1)^3*(2*s+1)) < CyclotomicRing.dimension e) :
    ∀ p ∈ conditions N e f, p ≠ 0 := by
  obtain ⟨d,hd,W,a,ha,ha0⟩ := hnz
  obtain ⟨X,v,hv,hvu⟩ := formula_invertible_witness hd f W a ha ha0
  let C : WitnessField →+* LaurentReduction.F WitnessField := HahnSeries.C
  let Y : Fin n → Matrix (Fin d) (Fin d) (LaurentReduction.F WitnessField) := fun i =>
    C.mapMatrix (X i)
  have hv' : Formula.Eval (algebraMap ℚ (Matrix (Fin d) (Fin d) (LaurentReduction.F WitnessField)))
      Y f (C.mapMatrix v) := by
    convert hv.map C.mapMatrix using 1
    exact RingHom.ext_rat _ _
  have hcert : ∀ h ∈ f.certificates, IsUnit (Formula.realized (algebraMap ℚ _) Y h) :=
    (Formula.certificates_iff (algebraMap ℚ _) Y f).mpr ⟨_,hv',hvu.map C.mapMatrix⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (onePencil n)
      (2*s+1) 1 (by omega) (by omega) hN hMN hM (by omega) (fun _ => 0)
    have heq : (onePencil n).map (Affine.eval (algebraMap ℚ (Matrix (Fin 1) (Fin 1)
        (LaurentReduction.F WitnessField))) (fun _ => 0)) = 1 := by
      ext i j
      simp [onePencil,Affine.eval_constant,Matrix.one_apply,Subsingleton.elim i j]
    rw [heq]
    exact isUnit_one
  · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
    have hb := (Formula.certificate_bounds f s hs hf).2 h hh
    apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (finPencil h)
      (2*s+1) d hb.1 hb.2 hN hMN hM hd Y
    exact (finPencil_unit _ _ h).mpr (hcert h hh)

lemma condition_degree {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.size ≤ s) :
    (conditions N e f).length ≤ s+2 ∧
    ∀ p ∈ conditions N e f, p.totalDegree ≤ 3*(2*s+1)*(CyclotomicRing.dimension e)^2 := by
  refine ⟨?_,?_⟩
  · have hh := (Formula.certificate_bounds f s hs hf).1
    simpa only [conditions,List.length_cons,List.length_map] using Nat.succ_le_succ hh
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (PencilCertificates.degree_le _ _).trans (by gcongr; omega)
    · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hp
      exact (PencilCertificates.degree_le _ _).trans (by
        gcongr
        exact ((Formula.certificate_bounds f s hs hf).2 h hh).2)

lemma integer_grid {K : Type*} [Field K] [CharZero K] (P : List (MvPolynomial (Fin 3) K))
    (hP : ∀ p ∈ P, p ≠ 0) (d H : ℕ) (hd : ∀ p ∈ P, p.totalDegree ≤ d)
    (hH : P.length*d < H) :
    ∃ x : Fin 3 → Fin H, ∀ p ∈ P, eval (fun i => (((x i).val+1 : ℕ) : K)) p ≠ 0 := by
  classical
  let S : Finset K := (Finset.range H).image (fun i => ((i+1 : ℕ) : K))
  have hS : S.card = H := by
    rw [Finset.card_image_of_injective,Finset.card_range]
    intro i j h
    have hh : i+1=j+1 := Nat.cast_injective h
    omega
  obtain ⟨x,hx,hxp⟩ := FiniteGrid.simultaneous P hP d hd S (by rwa [hS])
  have hm (i : Fin 3) : ∃ k : Fin H, ((k.val+1 : ℕ) : K) = x i := by
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (hx i)
    exact ⟨⟨k,Finset.mem_range.mp hk⟩,he⟩
  choose y hy using hm
  refine ⟨y,?_⟩
  intro p hp
  have heq : (fun i => (((y i).val+1 : ℕ) : K)) = x := funext hy
  simpa only [heq] using hxp p hp

lemma specialized_unit {K : Type*} [Field K] [CharZero K] {n q M N : ℕ} [NeZero M]
    (χ : AddChar (ZMod M) K) (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (x : Fin 3 → K)
    (hx : eval x (PencilCertificates.determinant χ N L) ≠ 0) :
    IsUnit (L.map (Affine.homogeneous (algebraMap ℚ _) (fun i =>
      (eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.lifts χ N n i)))) := by
  have hd : IsUnit ((eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.polynomial χ N L))
    := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.map_det]
    exact hx
  rw [PencilCertificates.specialized] at hd
  simpa using hd.map (Matrix.compRingEquiv (Fin q) (ZMod M) K).symm

lemma onePencil_unit {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (rationalLift : Fin (n+1) → Matrix ι ι K)
    (h : IsUnit ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) rationalLift))) : IsUnit
      (rationalLift 0) := by
  have hh := h.map (Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K)).toRingHom
  have heq : (Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K))
      ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) rationalLift)) = rationalLift 0 := by
    change Affine.homogeneous (algebraMap ℚ _) rationalLift (Affine.constant 1) = rationalLift 0
    simp [Affine.homogeneous,Affine.coeff,Affine.constant,Fin.sum_univ_succ]
  change IsUnit ((Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K))
      ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) rationalLift))) at hh
  rwa [heq] at hh

/-- The finite formula-independent list hits every admissible nonzero formula
at a defined and invertible original-tree value. -/

theorem output_hits {n s N e H : ℕ} (hs : 1 ≤ s)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N+2*(n+1)^3*(2*s+1))
    (hM : (2*s+1)*(2*(n+1)^3*(2*s+1)) < CyclotomicRing.dimension e)
    (hH : (s+2)*(3*(2*s+1)*(CyclotomicRing.dimension e)^2) < H) :
    Hits s (output n N e H) := by
  intro f hf _ha hnz
  have hb := condition_degree hs f hf (N := N) (e := e)
  obtain ⟨x,hx⟩ := integer_grid (conditions N e f)
    (condition_nonzero hs f hf hnz hN hMN hM) _ H hb.2 (lt_of_le_of_lt (Nat.mul_le_mul_right _
      hb.1) hH)
  let t : Fin 3 → ℕ := fun i => (x i).val+1
  let Zr := specializedLift n N e t
  have hz : IsUnit (Zr 0) := by
    apply onePencil_unit Zr
    exact specialized_unit _ _ _ (hx _ (List.mem_cons_self ..))
  obtain ⟨z,hz'⟩ := hz
  have hcert : ∀ h ∈ f.certificates,
      IsUnit (Formula.realized (algebraMap ℚ _) (fun i => (↑z⁻¹ : Matrix _ _ _)*Zr i.succ) h) := by
    intro h hh
    apply (finPencil_unit _ _ h).mp
    apply Affine.normalized_pencil_unit (finPencil h) Zr z hz'
    apply specialized_unit
    exact hx _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨h,hh,rfl⟩))
  obtain ⟨v,hv,hu⟩ := (Formula.certificates_iff _ _ f).mp hcert
  obtain ⟨a,ha,hua⟩ := transfer t f z hz' v hv hu
  exact ⟨tupleAt n N e t,emitted x ⟨z,hz'⟩,a,ha,hua⟩

end
end RationalHitting.Generator

namespace RationalHitting.Parameters

/-- The parameters, with ambientDimension the least power of two strictly above BΔ. -/
def w (n : ℕ) := n+1
/-- Rank parameter for formulas of the given size. -/
def rankBound (s : ℕ) := 2*s+1
/-- Dimension allowance in the rank expansion argument. -/
def delta (n s : ℕ) := 2*(w n)^3*rankBound s
/-- Binary logarithm used to choose the next cyclotomic dimension. -/
def exponent (n s : ℕ) := Nat.log 2 (rankBound s * delta n s)
/-- The least power of two strictly above the rank expansion threshold. -/
def ambientDimension (n s : ℕ) := 2^(exponent n s+1)
/-- Number of retained columns after the dimension allowance. -/
def truncation (n s : ℕ) := ambientDimension n s-delta n s
/-- Side length of the integer grid used for specialization. -/
def gridSize (n s : ℕ) := 1+3*(s+2)*rankBound s*(ambientDimension n s)^3

theorem threshold_pos (n s : ℕ) : 0 < rankBound s * delta n s := by
  simp only [rankBound,delta,w]
  positivity

theorem threshold_lt (n s : ℕ) : rankBound s * delta n s < ambientDimension n s :=
  Nat.lt_pow_succ_log_self (by omega) _

theorem M_le (n s : ℕ) : ambientDimension n s ≤ 2*(rankBound s*delta n s) := by
  unfold ambientDimension
  rw [pow_succ]
  have h := Nat.pow_log_le_self 2 (threshold_pos n s).ne'
  unfold exponent
  omega

theorem M_minimal (n s k : ℕ) (hk : rankBound s*delta n s < 2^k) : ambientDimension n s ≤ 2^k := by
  apply Nat.pow_le_pow_right (by omega)
  exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow (threshold_pos n s).ne' hk)

theorem N_pos (n s : ℕ) : 1 ≤ truncation n s := by
  have hh := threshold_lt n s
  have hb : 1 ≤ rankBound s := by unfold rankBound; omega
  have hd : delta n s ≤ rankBound s*delta n s := by nlinarith
  unfold truncation
  omega

theorem M_eq (n s : ℕ) : ambientDimension n s = truncation n s+delta n s := by
  have hh := N_pos n s
  unfold truncation at *
  omega

theorem grid_large (n s : ℕ) : (s+2)*(3*rankBound s*(ambientDimension n s)^2) < gridSize n s := by
  have hp : 1 ≤ ambientDimension n s := by
    apply Nat.one_le_iff_ne_zero.mpr
    unfold ambientDimension
    positivity
  have hpow : (ambientDimension n s)^2 ≤ (ambientDimension n s)^3 := Nat.pow_le_pow_right hp (by
    omega)
  unfold gridSize
  nlinarith [Nat.mul_le_mul_left (3*(s+2)*rankBound s) hpow]

theorem w_bound (n s : ℕ) : w n ≤ n+s+1 := by unfold w; omega

theorem B_bound (n s : ℕ) : rankBound s ≤ 2*(n+s+1) := by unfold rankBound; omega

theorem delta_bound (n s : ℕ) : delta n s ≤ 4*(n+s+1)^4 := by
  calc delta n s ≤ 2*(n+s+1)^3*(2*(n+s+1)) := by
         unfold delta
         gcongr
         · exact w_bound n s
         · exact B_bound n s
       _ = _ := by ring

theorem polynomial_M (n s : ℕ) : ambientDimension n s ≤ 16*(n+s+1)^5 := by
  calc ambientDimension n s ≤ 2*(rankBound s*delta n s) := M_le n s
       _ ≤ 2*((2*(n+s+1))*(4*(n+s+1)^4)) := by
          gcongr
          · exact B_bound n s
          · exact delta_bound n s
       _ = _ := by ring

theorem polynomial_H (n s : ℕ) (hn : 1 ≤ n) : gridSize n s ≤ 24577*(n+s+1)^17 := by
  have hp : 1 ≤ (n+s+1)^17 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc gridSize n s ≤ 1+3*(n+s+1)*(2*(n+s+1))*(16*(n+s+1)^5)^3 := by
         unfold gridSize
         apply Nat.add_le_add_left
         apply Nat.mul_le_mul
         · apply Nat.mul_le_mul
           · exact Nat.mul_le_mul_left 3 (by omega)
           · exact B_bound n s
         · exact Nat.pow_le_pow_left (polynomial_M n s) 3
       _ = 1+24576*(n+s+1)^17 := by ring
       _ ≤ _ := by omega

end RationalHitting.Parameters

namespace RationalHitting.Generator
noncomputable section

/-- The list with all parameters fixed by the unary inputs. -/
def list (n s : ℕ) : Output n :=
  output n (Parameters.truncation n s) (Parameters.exponent n s) (Parameters.gridSize n s)

theorem list_hits (n s : ℕ) (hs : 1 ≤ s) : Hits s (list n s) := by
  apply output_hits hs
  · exact Parameters.N_pos n s
  · exact Parameters.M_eq n s
  · exact Parameters.threshold_lt n s
  · exact Parameters.grid_large n s

theorem list_dimension_bound (n s : ℕ) : (list n s).dimension ≤ 256*(n+s+1)^10 := by
  have hd : CyclotomicRing.degree (Parameters.exponent n s) ≤ Parameters.ambientDimension n s := by
    unfold CyclotomicRing.degree Parameters.ambientDimension
    exact Nat.pow_le_pow_right (by omega) (by omega)
  change Parameters.ambientDimension n s * CyclotomicRing.degree (Parameters.exponent n s) ≤ _
  calc _ ≤ (16*(n+s+1)^5)*(16*(n+s+1)^5) :=
             Nat.mul_le_mul (Parameters.polynomial_M n s) (hd.trans (Parameters.polynomial_M n s))
       _ = _ := by ring

theorem list_length_bound (n s : ℕ) (hn : 1 ≤ n) :
    (list n s).tuples.length ≤ 24577^3*(n+s+1)^51 := by
  calc _ ≤ (Parameters.gridSize n s)^3 := length_output_le ..
       _ ≤ (24577*(n+s+1)^17)^3 := Nat.pow_le_pow_left (Parameters.polynomial_H n s hn) 3
       _ = _ := by rw [mul_pow,← pow_mul]

/-- The algebraic hitting property and the polynomial list-cardinality bound. -/

theorem algebraic_generator : ∃ G : (n s : ℕ) → Output n,
    ∀ n s, 1 ≤ n → 1 ≤ s →
      (G n s).dimension ≤ 256*(n+s+1)^10 ∧
      (G n s).tuples.length ≤ 24577^3*(n+s+1)^51 ∧ Hits s (G n s) := by
  exact ⟨list,fun n s hn hs => ⟨list_dimension_bound n s,list_length_bound n s hn,list_hits n s hs⟩⟩

end
end RationalHitting.Generator

end Complexity

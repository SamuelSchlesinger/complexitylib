/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.CyclotomicGrid

/-!
# Rational hitting lists: certificates

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Certificates.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity


namespace RationalHitting.LocalSpecialization
open IsLocalization Matrix
noncomputable section
variable {P K E : Type*} [CommRing P] [Field K] [Field E]

/-- Elements whose specialized values are nonzero. -/
def denominators (ev : P →+* K) : Submonoid P where
  carrier := {p | ev p ≠ 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change ev (x*y) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hx hy

/-- Localize at precisely the denominators nonzero at the chosen point. -/
abbrev Regular (ev : P →+* K) := Localization (denominators ev)

/-- Extend specialization to fractions regular at the chosen point. -/
def evaluate (ev : P →+* K) : Regular ev →+* K :=
  IsLocalization.lift (fun y : denominators ev => isUnit_iff_ne_zero.mpr y.property)

@[simp] lemma evaluate_algebraMap (ev : P →+* K) (p : P) :
    evaluate ev (algebraMap P (Regular ev) p) = ev p := IsLocalization.lift_eq _ _

/-- Only fractions whose denominator is nonzero at the point are evaluated.
The entire division algebra is deliberately not given a specialization. -/
lemma evaluate_reflects_units (ev : P →+* K) (x : Regular ev)
    (hx : IsUnit (evaluate ev x)) : IsUnit x := by
  obtain ⟨a,b,rfl⟩ := IsLocalization.exists_mk'_eq (denominators ev) x
  have heq : ev a = ev b * evaluate ev (IsLocalization.mk' (Regular ev) a b) :=
    (IsLocalization.lift_mk'_spec _ a _ b).mp rfl
  have ha : ev a ≠ 0 := by rw [heq]; exact mul_ne_zero b.property hx.ne_zero
  let a' : denominators ev := ⟨a,ha⟩
  apply isUnit_iff_exists_inv.mpr
  exact ⟨IsLocalization.mk' (Regular ev) (b : P) a', IsLocalization.mk'_mul_mk'_eq_one a' b⟩

/-- Embed the regular localization into a field containing its numerator ring. -/
def intoField (ev : P →+* K) (j : P →+* E) (hj : Function.Injective j) :
    Regular ev →+* E :=
  IsLocalization.lift (g := j) (fun y : denominators ev => isUnit_iff_ne_zero.mpr (by
    intro hz
    have hy : (y : P) = 0 := hj (hz.trans (map_zero j).symm)
    exact y.property (by rw [hy,map_zero])))

@[simp] lemma intoField_algebraMap (ev : P →+* K) (j : P →+* E)
    (hj : Function.Injective j) (p : P) :
    intoField ev j hj (algebraMap P (Regular ev) p) = j p := IsLocalization.lift_eq _ _

lemma intoField_injective (ev : P →+* K) (j : P →+* E) (hj : Function.Injective j) :
    Function.Injective (intoField ev j hj) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro x y
  constructor
  · intro h
    simpa only [intoField_algebraMap] using congrArg (intoField ev j hj) h
  · intro h
    rw [hj h]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma matrix_reflects_units (ev : P →+* K) (A : Matrix ι ι (Regular ev))
    (hA : IsUnit ((evaluate ev).mapMatrix A)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
  apply evaluate_reflects_units ev
  rwa [RingHom.map_det]

end
end RationalHitting.LocalSpecialization

namespace RationalHitting.QuantumLift
open Matrix HahnSeries
open RationalHitting.LocalSpecialization RationalHitting.PolynomialHahn
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
  {n : ℕ} (χ : AddChar (ZMod d) K)

/-- The original tree remains defined after the generic deformation. A nonzero
original value becomes invertible. Domain preservation uses the localization
regular at (1,1), while final invertibility uses the division subring. -/
theorem formula_invertible_value (hχ : χ.IsPrimitive) (f : Formula n)
    (W : Fin n → Matrix (ZMod d) (ZMod d) K) (a : Matrix (ZMod d) (ZMod d) K)
    (ha : f.Eval (algebraMap ℚ _) W a) (ha0 : a ≠ 0) :
    ∃ b : Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K),
      f.Eval (algebraMap ℚ _) (fun i => representation χ (liftD χ (W i))) b ∧ IsUnit b := by
  let P := MvPolynomial (Fin 2) K
  let ev : P →+* K := (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom
  let O := Regular ev
  let cO : ℚ →+* Matrix (ZMod d) (ZMod d) O :=
    (algebraMap O _).comp ((algebraMap P O).comp (MvPolynomial.C.comp (algebraMap ℚ K)))
  let X : Fin n → Matrix (ZMod d) (ZMod d) O := fun i =>
    (algebraMap P O).mapMatrix (polynomialLift χ (W i))
  let eps : Matrix (ZMod d) (ZMod d) O →+* Matrix (ZMod d) (ZMod d) K :=
    (evaluate ev).mapMatrix
  let inc : Matrix (ZMod d) (ZMod d) O →+*
      Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K) :=
    (intoField ev PolynomialHahn.embed PolynomialHahn.embed_injective).mapMatrix
  have hX : (fun i => eps (X i)) = W := by
    funext i
    change (evaluate ev).mapMatrix ((algebraMap P O).mapMatrix (polynomialLift χ (W i))) = W i
    have heq : (evaluate ev).mapMatrix ((algebraMap P O).mapMatrix (polynomialLift χ (W i))) =
        ev.mapMatrix (polynomialLift χ (W i)) := by
      ext j k
      exact evaluate_algebraMap ev _
    rw [heq]
    exact polynomialLift_specialize χ hχ (W i)
  have ha' : f.Eval (eps.comp cO) (fun i => eps (X i)) a := by
    rw [hX, RingHom.ext_rat (eps.comp cO) (algebraMap ℚ _)]
    exact ha
  obtain ⟨y,hy,hyval⟩ := ha'.lift eps (matrix_reflects_units ev)
  have hy0 : y ≠ 0 := by
    intro hz
    apply ha0
    rw [← hyval,hz,map_zero]
  have hinc : Function.Injective inc := Matrix.map_injective (intoField_injective ev _ _)
  have hb0 : inc y ≠ 0 := by
    intro hz
    exact hy0 (hinc (hz.trans (map_zero inc).symm))
  have hiX : (fun i => inc (X i)) = (fun i => representation χ (liftD χ (W i))) := by
    funext i
    have heq : inc (X i) = PolynomialHahn.embed.mapMatrix (polynomialLift χ (W i)) := by
      funext j k
      exact intoField_algebraMap ev PolynomialHahn.embed PolynomialHahn.embed_injective _
    rw [heq]
    exact polynomialLift_embed χ (W i)
  have hb : f.Eval (algebraMap ℚ _) (fun i => representation χ (liftD χ (W i))) (inc y) := by
    have hh := hy.map inc
    rw [hiX, RingHom.ext_rat (inc.comp cO) (algebraMap ℚ _)] at hh
    exact hh
  let : CharZero (Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K)) :=
    charZero_of_inj_zero fun m hm => by
      have hh := congrFun (congrFun hm (0 : ZMod d)) (0 : ZMod d)
      have hh0 := congrArg (fun z : HahnSeries Exponents K => z.coeff 0) hh
      simpa [Matrix.natCast_apply, ← HahnSeries.single_zero_natCast] using hh0
  let : CharZero (divisionSubring χ) :=
    (representation χ).charZero
  refine ⟨inc y,hb,?_⟩
  apply Formula.Eval.unit_of_division_lift (representation χ) (c := Rat.castHom (divisionSubring χ))
    (X := fun i => liftD χ (W i)) (h := f) _ hb0
  rwa [RingHom.ext_rat ((representation χ).comp (Rat.castHom (divisionSubring χ)))
    (algebraMap ℚ _)]

end
end RationalHitting.QuantumLift

namespace RationalHitting
open Matrix
noncomputable section

theorem formula_invertible_witness {n d : ℕ} (hd : 0 < d) (f : Formula n)
    (W : Fin n → Matrix (Fin d) (Fin d) ℚ) (a : Matrix (Fin d) (Fin d) ℚ)
    (ha : f.Eval (algebraMap ℚ _) W a) (ha0 : a ≠ 0) :
    ∃ (X : Fin n → Matrix (Fin d) (Fin d) (HahnSeries QuantumLift.Exponents ℂ))
      (v : Matrix (Fin d) (Fin d) (HahnSeries QuantumLift.Exponents ℂ)),
      f.Eval (algebraMap ℚ _) X v ∧ IsUnit v := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let e := Matrix.reindexRingEquiv ℂ (ZMod.finEquiv d).toEquiv
  let j : Matrix (Fin d) (Fin d) ℚ →+* Matrix (ZMod d) (ZMod d) ℂ :=
    e.toRingHom.comp (algebraMap ℚ ℂ).mapMatrix
  have hj : Function.Injective j := e.injective.comp (Matrix.map_injective (algebraMap ℚ
    ℂ).injective)
  have ha' : f.Eval (algebraMap ℚ _) (fun i => j (W i)) (j a) := by
    have hh := ha.map j
    rwa [RingHom.ext_rat (j.comp (algebraMap ℚ _)) (algebraMap ℚ _)] at hh
  have ha0' : j a ≠ 0 := by
    intro hz
    exact ha0 (hj (hz.trans (map_zero j).symm))
  have hζ := Complex.isPrimitiveRoot_exp d (NeZero.ne d)
  let χ := AddChar.zmodChar d hζ.pow_eq_one
  have hχ : χ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  obtain ⟨b,hb,hbu⟩ := QuantumLift.formula_invertible_value χ hχ f
    (fun i => j (W i)) (j a) ha' ha0'
  let r := Matrix.reindexRingEquiv (HahnSeries QuantumLift.Exponents ℂ) (ZMod.finEquiv
    d).toEquiv.symm
  refine ⟨fun i => r (QuantumLift.representation χ (QuantumLift.liftD χ (j (W i)))), r b, ?_,
    hbu.map r⟩
  have hh := hb.map r.toRingHom
  rwa [RingHom.ext_rat (r.toRingHom.comp (algebraMap ℚ _)) (algebraMap ℚ _)] at hh

end
end RationalHitting

namespace RationalHitting.PencilCertificates
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
instance laurentCharZero {E : Type*} [Field E] [CharZero E] : CharZero (LaurentReduction.F E) :=
  CharZero.of_addMonoidHom (HahnSeries.C : E →+* LaurentReduction.F E).toAddMonoidHom
    (map_one (HahnSeries.C : E →+* LaurentReduction.F E)) HahnSeries.C_injective

variable {n q M N : ℕ} [NeZero M]

/-- Extract the homogeneous coefficient matrices of an affine pencil. -/
def coefficients (L : Matrix (Fin q) (Fin q) (Affine.Form n)) :
    Fin (n+1) → Matrix (Fin q) (Fin q) K :=
  fun i a b => (algebraMap ℚ K) (Affine.coeff (L a b) i)

/-- Polynomial lifts for each homogeneous coordinate at the test points. -/
def lifts (χ : AddChar (ZMod M) K) (N n : ℕ) :
    Fin (n+1) → Matrix (ZMod M) (ZMod M) (MvPolynomial (Fin 3) K) :=
  fun i => ThreeLift.lift χ (PencilDeformation.test M N (i.val : K))

/-- The polynomial matrix certificate for the affine pencil. -/
def polynomial (χ : AddChar (ZMod M) K) (N : ℕ)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) :=
  PencilDeformation.polynomial (N := N) χ (coefficients (K := K) L) (fun i => (i.val : K))

/-- The determinant polynomial certifying invertibility of the lifted pencil. -/
def determinant (χ : AddChar (ZMod M) K) (N : ℕ)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) := (polynomial χ N L).det

lemma polynomial_apply (χ : AddChar (ZMod M) K)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (a b : Fin q × ZMod M) :
    polynomial χ N L a b = ∑ i, MvPolynomial.C ((algebraMap ℚ K) (Affine.coeff (L a.1 b.1) i)) *
      lifts χ N n i a.2 b.2 := by
  unfold polynomial PencilDeformation.polynomial PencilDeformation.polyBlocks
  rw [ThreeLift.lift_sum]
  simp only [Matrix.sum_apply,ThreeLift.lift_smul,Matrix.smul_apply,
    MvPolynomial.smul_eq_C_mul,coefficients,lifts]

lemma specialized (χ : AddChar (ZMod M) K)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (x : Fin 3 → K) :
    (eval₂Hom (RingHom.id K) x).mapMatrix (polynomial χ N L) =
      Matrix.compRingEquiv (Fin q) (ZMod M) K
        (L.map (Affine.homogeneous (algebraMap ℚ _) (fun i =>
          (eval₂Hom (RingHom.id K) x).mapMatrix (lifts χ N n i)))) := by
  rw [Affine.homogeneous_flat]
  funext a b
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply,polynomial_apply,map_sum,map_mul,
    eval₂Hom_C,RingHom.id_apply]

lemma block_eq (φ : K →+* E) (L : Matrix (Fin q) (Fin q) (Affine.Form n))
    {d : ℕ} (X : Fin n → Matrix (Fin d) (Fin d) E) :
    Rectangular.blockMatrix (fun i => φ.mapMatrix (coefficients (K := K) L i)) (Fin.cases 1 X) =
      Matrix.compRingEquiv (Fin q) (Fin d) E (L.map (Affine.eval (algebraMap ℚ _) X)) := by
  have hc (a : ℚ) : φ ((algebraMap ℚ K) a) = (algebraMap ℚ E) a :=
    DFunLike.congr_fun (RingHom.ext_rat (φ.comp (algebraMap ℚ K)) (algebraMap ℚ E)) a
  have hm : L.map (Affine.eval (algebraMap ℚ _) X) =
      L.map (Affine.homogeneous (algebraMap ℚ _) (Fin.cases 1 X)) := by
    funext a b
    exact (Affine.homogeneous_one _ X (L a b)).symm
  rw [hm,Affine.homogeneous_flat]
  funext a b
  simp only [Rectangular.blockMatrix,Matrix.sum_apply,Matrix.kroneckerMap_apply,
    RingHom.mapMatrix_apply,Matrix.map_apply,coefficients,hc]

lemma determinant_ne_zero (χ : AddChar (ZMod M) K) (hχ : χ.IsPrimitive)
    (φ : K →+* E) (L : Matrix (Fin q) (Fin q) (Affine.Form n))
    (B d : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B) (hN : 1 ≤ N)
    (hMN : M = N+2*(n+1)^3*B) (hM : B*(2*(n+1)^3*B) < M) (hd : 0 < d)
    (X : Fin n → Matrix (Fin d) (Fin d) (LaurentReduction.F E))
    (hX : IsUnit (L.map (Affine.eval (algebraMap ℚ _) X))) :
    determinant χ N L ≠ 0 := by
  apply PencilDeformation.det_ne_zero χ hχ φ (fun i : Fin (n+1) => (i.val : K))
    (by intro i j h; apply Fin.ext; change (i.val : K) = (j.val : K) at h; exact
      Nat.cast_injective h) (coefficients L) B d
      (by omega) hq hqB hN hMN hM hd (Fin.cases 1 X)
  apply Rectangular.blockEval_injective_of_isUnit
  rw [block_eq]
  exact hX.map (Matrix.compRingEquiv (Fin q) (Fin d) (LaurentReduction.F E))


lemma degree_le (χ : AddChar (ZMod M) K)
    (L : Matrix (Fin q) (Fin q) (Affine.Form n)) :
    (determinant χ N L).totalDegree ≤ 3*q*M^2 := by
  have hh := FiniteGrid.det_totalDegree_le (polynomial χ N L) (3*M)
    (PencilDeformation.entry_degree χ (coefficients L) (fun i => (i.val : K)))
  simp only [Fintype.card_prod,Fintype.card_fin,ZMod.card] at hh
  exact hh.trans_eq (by ring)

end
end RationalHitting.PencilCertificates

end Complexity

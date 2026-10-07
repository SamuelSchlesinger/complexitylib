/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraPolynomial
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Unrestricted depth-three lower bound: algebra quotient

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/AlgebraQuotient.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators
open Polynomial

namespace DepthThreeLowerBound.BinaryAlgebra

/-- The canonical polynomial representative of a quotient-ring element. -/
def quotientRepresentative {P : Polynomial F2} (hP : P.Monic) :
    AdjoinRoot P →ₗ[F2] Polynomial F2 :=
  AdjoinRoot.modByMonicHom hP

@[simp] theorem quotientRepresentative_mk {P : Polynomial F2} (hP : P.Monic)
    (f : Polynomial F2) :
    quotientRepresentative hP (AdjoinRoot.mk P f) = f %ₘ P :=
  AdjoinRoot.modByMonicHom_mk hP f

theorem mk_quotientRepresentative {P : Polynomial F2} (hP : P.Monic)
    (z : AdjoinRoot P) :
    AdjoinRoot.mk P (quotientRepresentative hP z) = z :=
  AdjoinRoot.mk_leftInverse hP z

theorem degree_quotientRepresentative_lt {P : Polynomial F2} (hP : P.Monic)
    (z : AdjoinRoot P) :
    (quotientRepresentative hP z).degree < P.degree := by
  refine AdjoinRoot.induction_on P z ?_
  intro f
  rw [quotientRepresentative_mk]
  exact Polynomial.degree_modByMonic_lt f hP

theorem quotientRepresentative_one {P : Polynomial F2} (hP : P.Monic)
    (hdeg : 0 < P.natDegree) :
    quotientRepresentative hP (1 : AdjoinRoot P) = 1 := by
  have h : (1 : Polynomial F2).degree < P.degree := by
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hP.ne_zero]
    exact WithBot.coe_lt_coe.mpr hdeg
  calc
    quotientRepresentative hP (1 : AdjoinRoot P) =
        quotientRepresentative hP (AdjoinRoot.mk P 1) := by rw [(AdjoinRoot.mk P).map_one]
    _ = (1 : Polynomial F2) %ₘ P := quotientRepresentative_mk hP 1
    _ = 1 := (Polynomial.modByMonic_eq_self_iff hP).mpr h

/-- The quotient by the monic polynomial specified by the input coefficients. -/
abbrev InputQuotient {r : ℕ} (p : Fin r → F2) :=
  AdjoinRoot (inputPolynomial p)

/-- The input quotient ring with coefficients specified by bits. -/
abbrev BitQuotient {r : ℕ} (p : Fin r → Bool) :=
  InputQuotient (fun i => bitValue (p i))

theorem pack_mod_inputPolynomial {r : ℕ} (p a : Fin r → F2) :
    pack a %ₘ inputPolynomial p = pack a := by
  apply (Polynomial.modByMonic_eq_self_iff (inputPolynomial_monic p)).mpr
  rw [inputPolynomial_degree]
  exact degree_pack_lt a

/-- Map coefficient bits into the polynomial quotient ring. -/
def encode {r : ℕ} (p : Fin r → F2) (a : Fin r → F2) : InputQuotient p :=
  AdjoinRoot.mk (inputPolynomial p) (pack a)

/-- Read the coefficients of the canonical quotient representative. -/
def coordinates {r : ℕ} (p : Fin r → F2) :
    InputQuotient p ≃ₗ[F2] (Fin r → F2) where
  toFun z i := (quotientRepresentative (inputPolynomial_monic p) z).coeff i.val
  invFun := encode p
  map_add' x y := by
    funext i
    simp only [map_add, Polynomial.coeff_add, Pi.add_apply]
  map_smul' c x := by
    funext i
    simp only [map_smul, Polynomial.coeff_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv z := by
    have hd : (quotientRepresentative (inputPolynomial_monic p) z).degree <
        (r : WithBot ℕ) := by
      simpa only [inputPolynomial_degree] using
        degree_quotientRepresentative_lt (inputPolynomial_monic p) z
    change AdjoinRoot.mk (inputPolynomial p)
      (pack (fun i : Fin r =>
        (quotientRepresentative (inputPolynomial_monic p) z).coeff i.val)) = z
    rw [pack_coeff_of_degree_lt _ hd]
    exact mk_quotientRepresentative (inputPolynomial_monic p) z
  right_inv a := by
    funext i
    change (quotientRepresentative (inputPolynomial_monic p)
      (AdjoinRoot.mk (inputPolynomial p) (pack a))).coeff i.val = a i
    rw [quotientRepresentative_mk, pack_mod_inputPolynomial, coeff_pack]

@[simp] theorem coordinates_apply {r : ℕ} (p : Fin r → F2)
    (z : InputQuotient p) (i : Fin r) :
    coordinates p z i =
      (quotientRepresentative (inputPolynomial_monic p) z).coeff i.val := rfl

@[simp] theorem coordinates_symm_apply {r : ℕ} (p a : Fin r → F2) :
    (coordinates p).symm a = encode p a := rfl

@[simp] theorem coordinates_encode {r : ℕ} (p a : Fin r → F2) :
    coordinates p (encode p a) = a :=
  (coordinates p).apply_symm_apply a

@[simp] theorem encode_coordinates {r : ℕ} (p : Fin r → F2) (z : InputQuotient p) :
    encode p (coordinates p z) = z :=
  (coordinates p).symm_apply_apply z

theorem encode_injective {r : ℕ} (p : Fin r → F2) : Function.Injective (encode p) :=
  (coordinates p).symm.injective

theorem encode_surjective {r : ℕ} (p : Fin r → F2) : Function.Surjective (encode p) :=
  (coordinates p).symm.surjective

instance inputQuotientFintype {r : ℕ} (p : Fin r → F2) : Fintype (InputQuotient p) :=
  Fintype.ofEquiv (Fin r → F2) (coordinates p).toEquiv.symm

@[simp] theorem inputQuotient_card {r : ℕ} (p : Fin r → F2) :
    Fintype.card (InputQuotient p) = 2 ^ r := by
  rw [Fintype.card_congr (coordinates p).toEquiv, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

theorem bitQuotient_card {r : ℕ} (p : Fin r → Bool) :
    Fintype.card (BitQuotient p) = 2 ^ r :=
  inputQuotient_card _

theorem coordinates_mk {r : ℕ} (p : Fin r → F2)
    (f : Polynomial F2) (i : Fin r) :
    coordinates p (AdjoinRoot.mk (inputPolynomial p) f) i =
      (f %ₘ inputPolynomial p).coeff i.val := by
  rw [coordinates_apply, quotientRepresentative_mk]

@[simp] theorem encode_zero {r : ℕ} (p : Fin r → F2) :
    encode p (0 : Fin r → F2) = 0 := by
  rw [encode, pack_zero, map_zero]

@[simp] theorem encode_add {r : ℕ} (p a b : Fin r → F2) :
    encode p (a + b) = encode p a + encode p b := by
  simp only [encode, pack_add, map_add]

@[simp] theorem encode_smul {r : ℕ} (p : Fin r → F2) (c : F2) (a : Fin r → F2) :
    encode p (c • a) = c • encode p a := by
  change AdjoinRoot.mk (inputPolynomial p) (pack (c • a)) =
    c • AdjoinRoot.mk (inputPolynomial p) (pack a)
  rw [pack_smul, AdjoinRoot.smul_mk]

theorem coordinates_encode_mul {r : ℕ} (p a b : Fin r → F2) (i : Fin r) :
    coordinates p (encode p a * encode p b) i =
      ((pack a * pack b) %ₘ inputPolynomial p).coeff i.val := by
  change coordinates p
    (AdjoinRoot.mk (inputPolynomial p) (pack a) *
      AdjoinRoot.mk (inputPolynomial p) (pack b)) i = _
  rw [← map_mul, coordinates_mk]

theorem encode_mul {r : ℕ} (p a b : Fin r → F2) :
    encode p (fun i => ((pack a * pack b) %ₘ inputPolynomial p).coeff i.val) =
      encode p a * encode p b := by
  apply (coordinates p).injective
  rw [coordinates_encode]
  funext i
  exact (coordinates_encode_mul p a b i).symm

theorem coordinates_mul {r : ℕ} (p : Fin r → F2) (x y : InputQuotient p) (i : Fin r) :
    coordinates p (x * y) i =
      ((pack (coordinates p x) * pack (coordinates p y)) %ₘ inputPolynomial p).coeff i.val := by
  simpa only [encode_coordinates] using
    coordinates_encode_mul p (coordinates p x) (coordinates p y) i

theorem coordinates_one {r : ℕ} (p : Fin r → F2) (hr : 0 < r) (i : Fin r) :
    coordinates p (1 : InputQuotient p) i = if i.val = 0 then 1 else 0 := by
  rw [coordinates_apply, quotientRepresentative_one (inputPolynomial_monic p)
    (by simpa only [inputPolynomial_natDegree] using hr), Polynomial.coeff_one]

/-- Read the constant coefficient of the quotient representative. -/
def degreeZero {P : Polynomial F2} (hP : P.Monic) : AdjoinRoot P →ₗ[F2] F2 :=
  (Polynomial.lcoeff F2 0).comp (quotientRepresentative hP)

@[simp] theorem degreeZero_apply {P : Polynomial F2} (hP : P.Monic)
    (z : AdjoinRoot P) :
    degreeZero hP z = (quotientRepresentative hP z).coeff 0 := rfl

theorem degreeZero_mk {P : Polynomial F2} (hP : P.Monic) (f : Polynomial F2) :
    degreeZero hP (AdjoinRoot.mk P f) = (f %ₘ P).coeff 0 := by
  rw [degreeZero_apply, quotientRepresentative_mk]

theorem degreeZero_one {P : Polynomial F2} (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    degreeZero hP (1 : AdjoinRoot P) = 1 := by
  rw [degreeZero_apply, quotientRepresentative_one hP hdeg, Polynomial.coeff_one_zero]

theorem degreeZero_surjective {P : Polynomial F2} (hP : P.Monic)
    (hdeg : 0 < P.natDegree) : Function.Surjective (degreeZero hP) := by
  intro c
  refine ⟨c • (1 : AdjoinRoot P), ?_⟩
  rw [map_smul, degreeZero_one hP hdeg, smul_eq_mul, mul_one]

theorem degreeZero_encode {r : ℕ} (p : Fin r → F2) (hr : 0 < r) (a : Fin r → F2) :
    degreeZero (inputPolynomial_monic p) (encode p a) = a ⟨0, hr⟩ := by
  rw [encode, degreeZero_mk, pack_mod_inputPolynomial]
  exact coeff_pack a ⟨0, hr⟩

theorem degreeZero_coordinates {r : ℕ} (p : Fin r → F2) (hr : 0 < r)
    (z : InputQuotient p) :
    degreeZero (inputPolynomial_monic p) z = coordinates p z ⟨0, hr⟩ := rfl

theorem degreeZero_sum_encode_pow {r t : ℕ} (p a : Fin r → F2)
    (beta : Fin t → Fin r → F2) :
    degreeZero (inputPolynomial_monic p)
        (∑ j : Fin t, encode p (beta j) * (encode p a) ^ j.val) =
      ((∑ j : Fin t, pack (beta j) * (pack a) ^ j.val) %ₘ inputPolynomial p).coeff 0 := by
  rw [← degreeZero_mk (inputPolynomial_monic p)
    (∑ j : Fin t, pack (beta j) * (pack a) ^ j.val)]
  congr 1
  simp only [encode, map_sum, map_mul, map_pow]

end DepthThreeLowerBound.BinaryAlgebra

end

end Complexity

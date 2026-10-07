/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Generator

/-!
# Rational hitting lists: integral lift

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/IntegralLift.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.CyclotomicRing
open Polynomial Matrix Module
noncomputable section

lemma root_degree (e : ℕ) : AdjoinRoot.root (modulus e)^degree e = -1 := by
  have h := AdjoinRoot.eval₂_root (modulus e)
  change Polynomial.eval₂ (AdjoinRoot.of (modulus e)) (AdjoinRoot.root (modulus e))
    ((X : ℚ[X])^degree e+1) = 0 at h
  rw [Polynomial.eval₂_add,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_one] at h
  exact eq_neg_of_add_eq_zero_left h

lemma root_pow_reduce (e k : ℕ) :
    AdjoinRoot.root (modulus e)^k = (-1 : R e)^(k/degree e) *
      (basis e ⟨k % degree e,Nat.mod_lt _ (degree_pos e)⟩) := by
  rw [basis_apply,← root_degree,← pow_mul,← pow_add]
  congr 1
  change k = degree e*(k/degree e)+k%degree e
  exact (Nat.div_add_mod k (degree e)).symm

/-- Every regular-representation entry of a cyclotomic monomial is 0 or ±1.
This also gives an explicit integral computation with a division and remainder. -/
lemma rho_root_pow (e k : ℕ) (i j : Fin (degree e)) :
    rho e (AdjoinRoot.root (modulus e)^k) i j =
      if (k+j.val) % degree e = i.val then (-1 : ℚ)^((k+j.val)/degree e) else 0 := by
  rw [rho,Algebra.leftMulMatrix_eq_repr_mul,basis_apply,← pow_add,root_pow_reduce]
  rw [show (-1 : R e)^((k+j.val)/degree e) =
      algebraMap ℚ (R e) ((-1 : ℚ)^((k+j.val)/degree e)) by simp]
  rw [← Algebra.smul_def, map_smul, Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply]
  simp only [smul_eq_mul,mul_ite,mul_one,mul_zero]
  congr 1
  exact propext ⟨fun h => congrArg Fin.val h,fun h => Fin.ext h⟩

lemma rho_character (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) :
    rho e (character e a) i j =
      if (a.val+j.val) % degree e = i.val then (-1 : ℚ)^((a.val+j.val)/degree e) else 0 := by
  rw [character,AddChar.zmodChar_apply,rho_root_pow]

/-- The signed coefficient of the cyclotomic regular representation. -/
def signedEntry (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) : ℤ :=
  if (a.val+j.val) % degree e = i.val then (-1 : ℤ)^((a.val+j.val)/degree e) else 0

lemma rho_character_integral (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) :
    rho e (character e a) i j = (signedEntry e a i j : ℚ) := by
  simp only [rho_character,signedEntry,Int.cast_ite,Int.cast_pow,Int.cast_neg,Int.cast_one,
    Int.cast_zero]

lemma signedEntry_abs (e : ℕ) (a : ZMod (dimension e)) (i j : Fin (degree e)) :
    |signedEntry e a i j| ≤ 1 := by
  unfold signedEntry
  split_ifs <;> simp [abs_pow]

end
end RationalHitting.CyclotomicRing


namespace RationalHitting.IntegralTest
open Polynomial Matrix
open scoped BigOperators

/-- Integer computation of the exact expanded Taylor-reversal matrix at t. -/
def full (M : ℕ) (a t : ℤ) : Matrix (Fin M) (Fin M) ℤ := fun i j =>
  ∑ r : Fin M, ((-a)^(r.rev.val-i.val)*(r.rev.val.choose i.val : ℤ)) *
    (a^(j.val-r.val)*(j.val.choose r.val : ℤ)) * t^r.val

/-- The integer Taylor test matrix with discarded columns set to zero. -/
def padded (M N : ℕ) (a t : ℤ) : Matrix (Fin M) (Fin M) ℤ :=
  fun i j => if j.val < N then full M a t i j else 0

lemma coeff_bound (a : ℤ) (w M k j : ℕ) (hw : 1 ≤ w) (ha : |a| ≤ w) (hk : k ≤ M) :
    |(((X+C a)^k : ℤ[X]).coeff j)| ≤ (2*w : ℤ)^M := by
  rw [coeff_X_add_C_pow,abs_mul,abs_pow,Int.abs_natCast]
  have hw' : (1 : ℤ) ≤ w := by exact_mod_cast hw
  have hc : (k.choose j : ℤ) ≤ (2 : ℤ)^M := by
    exact_mod_cast (Nat.choose_le_two_pow k j).trans (Nat.pow_le_pow_right (by omega) hk)
  calc |a|^(k-j)*(k.choose j : ℤ) ≤ (w : ℤ)^M * (2 : ℤ)^M := by
         apply mul_le_mul _ hc (by positivity) (by positivity)
         exact (pow_le_pow_left₀ (abs_nonneg a) ha (k-j)).trans (pow_le_pow_right₀ hw'
           (Nat.sub_le k j |>.trans hk))
       _ = _ := by rw [← mul_pow]; congr 1; ring

lemma full_bound (M : ℕ) (a t : ℤ) (w H : ℕ) (hw : 1 ≤ w) (hH : 1 ≤ H)
    (ha : |a| ≤ w) (ht : |t| ≤ H) (i j : Fin M) :
    |full M a t i j| ≤ (M : ℤ)*(2*w : ℤ)^(2*M)*(H : ℤ)^M := by
  unfold full
  simp_rw [← coeff_X_add_C_pow]
  calc |∑ r : Fin M, _| ≤ ∑ r : Fin M, |(((X+C (-a))^r.rev.val : ℤ[X]).coeff i.val) *
          (((X+C a)^j.val : ℤ[X]).coeff r.val) * t^r.val| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _r : Fin M, (2*w : ℤ)^(2*M)*(H : ℤ)^M := by
         apply Finset.sum_le_sum
         intro r _
         rw [abs_mul,abs_mul,abs_pow]
         have hh : (1 : ℤ) ≤ H := by exact_mod_cast hH
         calc _ ≤ ((2*w : ℤ)^M*(2*w : ℤ)^M)*(H : ℤ)^M := by
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · apply mul_le_mul (coeff_bound (-a) w M _ _ hw (by simpa using ha)
                  (Nat.le_of_lt r.rev.isLt))
                    (coeff_bound a w M _ _ hw ha (Nat.le_of_lt j.isLt)) (abs_nonneg _) (by
                      positivity)
                · exact (pow_le_pow_left₀ (abs_nonneg t) ht r.val).trans (pow_le_pow_right₀ hh
                  (Nat.le_of_lt r.isLt))
              _ = _ := by rw [← pow_add]; simp [two_mul]
       _ = _ := by simp [mul_assoc]

lemma padded_bound (M N : ℕ) (a t : ℤ) (w H : ℕ) (hw : 1 ≤ w) (hH : 1 ≤ H)
    (ha : |a| ≤ w) (ht : |t| ≤ H) (i j : Fin M) :
    |padded M N a t i j| ≤ (M : ℤ)*(2*w : ℤ)^(2*M)*(H : ℤ)^M := by
  by_cases h : j.val < N
  · simpa [padded,h] using full_bound M a t w H hw hH ha ht i j
  · simp only [padded,h,ite_false,abs_zero]; positivity

end RationalHitting.IntegralTest


namespace RationalHitting.IntegralTest
open Matrix Polynomial
open scoped BigOperators

lemma full_cast {K : Type*} [Field K] (M : ℕ) (a t : ℤ) (i j : Fin M) :
    Polynomial.eval (t : K) (TestPolynomial.full M (a : K) i j) =
      (full M a t i j : K) := by
  simp only [TestPolynomial.full,full,coeff_X_add_C_pow,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_natCast]

lemma padded_cast {K : Type*} [Field K] (M N : ℕ) (a t : ℤ) (i j : Fin M) :
    Polynomial.eval (t : K) (TestPolynomial.padded M N (a : K) i j) =
      (padded M N a t i j : K) := by
  by_cases h : j.val < N
  · simpa [TestPolynomial.padded,padded,h] using full_cast M a t i j (K := K)
  · simp [TestPolynomial.padded,padded,h]

end RationalHitting.IntegralTest

namespace RationalHitting.ThreeLift
open Polynomial MvPolynomial Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]

lemma eval_uni (x : Fin 3 → K) (p : K[X]) : MvPolynomial.eval x (uni p) = Polynomial.eval (x 0)
    p := by
  have he : (MvPolynomial.eval x).comp uni = Polynomial.evalRingHom (x 0) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [uni]
    · simp [uni]
  exact DFunLike.congr_fun he p

lemma eval_lift (χ : AddChar (ZMod d) K) (R : Matrix (ZMod d) (ZMod d) K[X])
    (x : Fin 3 → K) (i j : ZMod d) :
    MvPolynomial.eval x (lift χ R i j) =
      (d : K)⁻¹ * ∑ a : ZMod d, ∑ b : ZMod d, ∑ k : ZMod d,
        χ (-a*k)*Polynomial.eval (x 0) (R k (k-b)) * QuantumMatrices.weyl χ a b i j *
          (x 1)^a.val*(x 2)^b.val := by
  simp only [lift,map_sum,map_mul,map_pow,eval_uni,MvPolynomial.eval_C,MvPolynomial.eval_X,coeffP,
    Polynomial.eval_C]
  simp only [Finset.mul_sum,Finset.sum_mul]
  congr 1
  ext a
  congr 1
  ext b
  congr 1
  ext k
  ring

end
end RationalHitting.ThreeLift

namespace RationalHitting.IntegralLift
open Complexity.RationalHitting.CyclotomicRing Matrix
open scoped BigOperators
noncomputable section

/-- The fixed signed-monomial integer formula for M times a regular lift entry. -/
def entry (e : ℕ) (T : Matrix (ZMod (dimension e)) (ZMod (dimension e)) ℤ)
    (p r : ℤ) (u v : ZMod (dimension e)) (i j : Fin (degree e)) : ℤ :=
  ∑ a : ZMod (dimension e), ∑ b : ZMod (dimension e), ∑ k : ZMod (dimension e),
    if u = v+b then T k (k-b)*signedEntry e (-a*k+a*u) i j*p^a.val*r^b.val else 0

lemma entry_bound (e : ℕ) (T : Matrix (ZMod (dimension e)) (ZMod (dimension e)) ℤ)
    (p r : ℤ) (A H : ℕ) (hT : ∀ i j, |T i j| ≤ A) (hH : 1 ≤ H)
    (hp : |p| ≤ H) (hr : |r| ≤ H) (u v : ZMod (dimension e)) (i j : Fin (degree e)) :
    |entry e T p r u v i j| ≤ (dimension e : ℤ)^3*A*(H : ℤ)^(2*dimension e) := by
  have hH' : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hterm (a b k : ZMod (dimension e)) :
      |(if u=v+b then T k (k-b)*signedEntry e (-a*k+a*u) i j*p^a.val*r^b.val else 0)| ≤
        (A : ℤ)*(H : ℤ)^(2*dimension e) := by
    split_ifs
    · simp only [abs_mul,abs_pow]
      calc _ ≤ ((A : ℤ)*1*(H : ℤ)^dimension e)*(H : ℤ)^dimension e := by
               apply mul_le_mul _ _ (by positivity) (by positivity)
               · apply mul_le_mul _ _ (by positivity) (by positivity)
                 · exact mul_le_mul (hT _ _) (signedEntry_abs ..) (abs_nonneg _) (by positivity)
                 · exact (pow_le_pow_left₀ (abs_nonneg p) hp a.val).trans
                     (pow_le_pow_right₀ hH' (Nat.le_of_lt a.val_lt))
               · exact (pow_le_pow_left₀ (abs_nonneg r) hr b.val).trans
                   (pow_le_pow_right₀ hH' (Nat.le_of_lt b.val_lt))
           _ = _ := by rw [mul_one,mul_assoc,← pow_add]; simp [two_mul]
    · simp only [abs_zero]; positivity
  unfold entry
  calc |∑ a : ZMod (dimension e), _| ≤ ∑ a : ZMod (dimension e), |∑ b : ZMod (dimension e), _| :=
          Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ a : ZMod (dimension e), ∑ b : ZMod (dimension e), ∑ k : ZMod (dimension e),
          (A : ℤ)*(H : ℤ)^(2*dimension e) := by
         apply Finset.sum_le_sum
         intro a _
         apply (Finset.abs_sum_le_sum_abs _ _).trans
         apply Finset.sum_le_sum
         intro b _
         exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => hterm a b k))
       _ = _ := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]; ring

end
end RationalHitting.IntegralLift

namespace RationalHitting.IntegralLift
open Matrix Complexity.RationalHitting.CyclotomicRing Polynomial
open scoped BigOperators
noncomputable section

lemma rho_rat_mul (e : ℕ) (q : ℚ) (z : R e) (i j : Fin (degree e)) :
    rho e (algebraMap ℚ (R e) q * z) i j = q * rho e z i j := by
  rw [← Algebra.smul_def, map_smul, Matrix.smul_apply, smul_eq_mul]

lemma rho_div_nat (e : ℕ) (z : R e) (i j : Fin (degree e)) :
    (dimension e : ℚ) * rho e ((dimension e : R e)⁻¹*z) i j = rho e z i j := by
  have hc : (dimension e : R e)⁻¹ = algebraMap ℚ (R e) ((dimension e : ℚ)⁻¹) := by simp
  have hd : (dimension e : ℚ) ≠ 0 := by exact_mod_cast (dimension_pos e).ne'
  rw [hc,rho_rat_mul,← mul_assoc,mul_inv_cancel₀ hd,one_mul]

lemma entry_spec (e : ℕ)
    (P : Matrix (ZMod (dimension e)) (ZMod (dimension e)) (R e)[X])
    (T : Matrix (ZMod (dimension e)) (ZMod (dimension e)) ℤ) (t p r : ℤ)
    (hT : ∀ u v, Polynomial.eval (t : R e) (P u v) = (T u v : R e))
    (u v : ZMod (dimension e)) (i j : Fin (degree e)) :
    (entry e T p r u v i j : ℚ) = (dimension e : ℚ) *
      rho e (MvPolynomial.eval ![(t : R e),(p : R e),(r : R e)]
        (ThreeLift.lift (character e) P u v)) i j := by
  rw [ThreeLift.eval_lift,rho_div_nat]
  simp only [entry,Int.cast_sum,map_sum,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,hT,
    QuantumMatrices.weyl]
  by_cases h : u = v+b
  · simp only [ite_eq_left h]
    have he : character e (-a*k)*(T k (k-b) : R e)*character e (a*u)*
        (p : R e)^a.val*(r : R e)^b.val =
        algebraMap ℚ (R e) ((T k (k-b)*p^a.val*r^b.val : ℤ) : ℚ) *
          character e (-a*k+a*u) := by
      rw [AddChar.map_add_eq_mul]
      simp only [map_mul,map_pow,map_intCast,Int.cast_mul,Int.cast_pow]
      ring
    change ((T k (k-b)*signedEntry e (-a*k+a*u) i j*p^a.val*r^b.val : ℤ) : ℚ) =
      rho e (character e (-a*k)*(T k (k-b) : R e)*character e (a*u)*
        (p : R e)^a.val*(r : R e)^b.val) i j
    rw [he,rho_rat_mul,rho_character_integral]
    simp only [Int.cast_mul,Int.cast_pow]
    ring
  · simp [h]

end
end RationalHitting.IntegralLift

namespace RationalHitting.Generator
open Matrix
open scoped BigOperators
noncomputable section

/-- Fixed row-major block coordinate. -/
def coordinate (e : ℕ) : ZMod (CyclotomicRing.dimension e) × Fin (CyclotomicRing.degree e) ≃ Fin
    (matrixDimension e) :=
  (Equiv.prodCongr (ZMod.finEquiv (CyclotomicRing.dimension e)).symm.toEquiv
    (Equiv.refl (Fin (CyclotomicRing.degree e)))).trans finProdFinEquiv

lemma regular_apply (e : ℕ)
    (A : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e))
    (i j : Fin (matrixDimension e)) : regular e A i j = CyclotomicRing.rho e
      (A ((coordinate e).symm i).1 ((coordinate e).symm j).1)
      ((coordinate e).symm i).2 ((coordinate e).symm j).2 := rfl

/-- Exact integer Taylor matrices, with the same fixed order of residues. -/
def integerTest (N e : ℕ) (a t : ℤ) :
    Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e)) ℤ :=
  (IntegralTest.padded (CyclotomicRing.dimension e) N a t).reindex
    (ZMod.finEquiv (CyclotomicRing.dimension e)).toEquiv
    (ZMod.finEquiv (CyclotomicRing.dimension e)).toEquiv

/-- The common-denominator-cleared regular matrices used in exact arithmetic. -/
def integralLift (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) : Matrix (Fin (matrixDimension e))
    (Fin (matrixDimension e)) ℤ :=
  fun i j => IntegralLift.entry e (integerTest N e (a.val : ℤ) (x 0 : ℤ))
    (x 1 : ℤ) (x 2 : ℤ) ((coordinate e).symm i).1 ((coordinate e).symm j).1
      ((coordinate e).symm i).2 ((coordinate e).symm j).2

lemma U_cast (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) :
    (integralLift n N e x a).map (Int.castRingHom ℚ) = (CyclotomicRing.dimension e : ℚ) •
      rationalLift n N e x a := by
  ext i j
  change (integralLift n N e x a i j : ℚ) = (CyclotomicRing.dimension e : ℚ) * regular e
    (specializedLift n N e x a) i j
  rw [regular_apply]
  unfold integralLift
  have hh := IntegralLift.entry_spec e
    (PencilDeformation.test (CyclotomicRing.dimension e) N (a.val : CyclotomicRing.R e))
    (integerTest N e (a.val : ℤ) (x 0 : ℤ)) (x 0 : ℤ) (x 1 : ℤ) (x 2 : ℤ)
    (fun u v => by
      simp only [PencilDeformation.test,integerTest,Matrix.reindex_apply]
      simpa only [Int.cast_natCast,Matrix.submatrix_apply] using IntegralTest.padded_cast (K :=
        CyclotomicRing.R e) (CyclotomicRing.dimension e)
        N (a.val : ℤ) (x 0 : ℤ) _ _)
    ((coordinate e).symm i).1 ((coordinate e).symm j).1
    ((coordinate e).symm i).2 ((coordinate e).symm j).2
  have hx : (fun j : Fin 3 => (x j : CyclotomicRing.R e)) =
      ![(x 0 : CyclotomicRing.R e),(x 1 : CyclotomicRing.R e),(x 2 : CyclotomicRing.R e)] := by
    funext j
    fin_cases j <;> rfl
  simpa only [specializedLift,PencilCertificates.lifts,RingHom.mapMatrix_apply,Matrix.map_apply,
    MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_id,Int.cast_natCast,hx] using hh

lemma U_bound (n N e H : ℕ) (x : Fin 3 → ℕ) (hH : 1 ≤ H) (hx : ∀ l, x l ≤ H)
    (a : Fin (n+1)) (i j : Fin (matrixDimension e)) :
    |integralLift n N e x a i j| ≤ (CyclotomicRing.dimension e : ℤ)^4 *
      (2*(n+1) : ℤ)^(2*CyclotomicRing.dimension e) * (H : ℤ)^(3*CyclotomicRing.dimension e) := by
  have hT (u v) : |integerTest N e (a.val : ℤ) (x 0 : ℤ) u v| ≤
      (CyclotomicRing.dimension e : ℤ)*(2*(n+1) : ℤ)^(2*CyclotomicRing.dimension e)*(H :
        ℤ)^CyclotomicRing.dimension e := by
    apply IntegralTest.padded_bound _ _ _ _ (n+1) H (by omega) hH
    · rw [Int.abs_natCast]; exact_mod_cast (Nat.le_of_lt a.isLt)
    · rw [Int.abs_natCast]; exact_mod_cast hx 0
  have hh := IntegralLift.entry_bound e (integerTest N e (a.val : ℤ) (x 0 : ℤ))
    (x 1 : ℤ) (x 2 : ℤ)
    (CyclotomicRing.dimension e*(2*(n+1))^(2*CyclotomicRing.dimension
      e)*H^CyclotomicRing.dimension e)
    H (by simpa using hT) hH (by simpa using hx 1) (by simpa using hx 2)
    ((coordinate e).symm i).1 ((coordinate e).symm j).1
    ((coordinate e).symm i).2 ((coordinate e).symm j).2
  apply hh.trans_eq
  push_cast
  rw [show 3*CyclotomicRing.dimension e = CyclotomicRing.dimension e+2*CyclotomicRing.dimension
    e by omega,pow_add]
  ring

lemma scaled_normalization {d : ℕ} (A B : Mat d) (hA : A.det ≠ 0) (c : ℚ) (hc : c ≠ 0) :
    (c • A)⁻¹ * (c • B) = A⁻¹*B := by
  let : Invertible c := invertibleOfNonzero hc
  have hi : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
    simpa only [invOf_eq_inv] using (Matrix.inv_smul (A := A) c (isUnit_iff_ne_zero.mpr hA))
  rw [hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  simp [hc]

lemma tupleAt_integer (n N e : ℕ) (x : Fin 3 → ℕ) (hz : (rationalLift n N e x 0).det ≠ 0)
    (a : Fin n) :
    tupleAt n N e x a = ((integralLift n N e x 0).map (Int.castRingHom ℚ))⁻¹ *
      (integralLift n N e x a.succ).map (Int.castRingHom ℚ) := by
  rw [U_cast,U_cast,scaled_normalization _ _ hz _ (by exact_mod_cast
    (CyclotomicRing.dimension_pos e).ne')]
  rfl

lemma U_det_ne_zero (n N e : ℕ) (x : Fin 3 → ℕ) (hz : (rationalLift n N e x 0).det ≠ 0) :
    (integralLift n N e x 0).det ≠ 0 := by
  have hu : ((integralLift n N e x 0).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [U_cast,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (CyclotomicRing.dimension_pos e).ne')) hz
  have he : ((integralLift n N e x 0).map (Int.castRingHom ℚ)).det = ((integralLift n N e x
    0).det : ℚ) :=
    (Int.cast_det _).symm
  rw [he] at hu
  exact_mod_cast hu

end
end RationalHitting.Generator

end Complexity

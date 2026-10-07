/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.IntegralLift

/-!
# Rational hitting lists: encoding bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/EncodingBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.EncodingBounds
open Matrix
open scoped BigOperators

lemma encodeNat_length (a : ℕ) : (encodeNat a).length = 2*(Nat.digits 2 a).length+1 := by
  simp [encodeNat]
  omega

lemma encodeNat_le (a L : ℕ) (ha : a < 2^L) : (encodeNat a).length ≤ 2*L+1 := by
  rw [encodeNat_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 ((Nat.digits_length_le_iff (by omega) a).mpr
    ha)) 1

lemma ratio_num_le (a b : ℤ) (hb : b ≠ 0) : (Rat.divInt a b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hb) ha

lemma ratio_den_le (a b : ℤ) (hb : b ≠ 0) : (Rat.divInt a b).den ≤ b.natAbs := by
  simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb

lemma encodeRat_ratio_le (a b : ℤ) (hb : b ≠ 0) (L : ℕ)
    (ha : a.natAbs < 2^L) (hb' : b.natAbs < 2^L) :
    (encodeRat (Rat.divInt a b)).length ≤ 4*L+3 := by
  have hn := encodeNat_le _ L (lt_of_le_of_lt (ratio_num_le a b hb) ha)
  have hd := encodeNat_le _ L (lt_of_le_of_lt (ratio_den_le a b hb) hb')
  simp only [encodeRat,List.length_append,List.length_singleton]
  omega

lemma determinant_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ)
    (hA : ∀ i j, |A i j| ≤ B) : |A.det| ≤ (d.factorial : ℤ)*(B : ℤ)^d := by
  rw [Matrix.det_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc ∑ σ : Equiv.Perm (Fin d), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| ≤
          ∑ _σ : Equiv.Perm (Fin d), (B : ℤ)^d := by
         apply Finset.sum_le_sum
         intro σ _
         rw [Units.smul_def, zsmul_eq_mul, abs_mul]
         have hsign : |((Equiv.Perm.sign σ : ℤˣ) : ℤ)| = 1 := by
           rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
         change |((Equiv.Perm.sign σ : ℤˣ) : ℤ)| * |∏ i, A (σ i) i| ≤ (B : ℤ)^d
         rw [hsign]
         rw [one_mul,Finset.abs_prod]
         calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin d, (B : ℤ) :=
                Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => hA _ _)
              _ = _ := by simp
       _ = _ := by simp [Fintype.card_perm]

/-- Cramer's rule used by the generator, without any assumption on arithmetic algorithms. -/
lemma normalized_entry_ratio {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (hA : A.det ≠ 0)
    (i j : Fin d) :
    ((A.map (Int.castRingHom ℚ))⁻¹ * B.map (Int.castRingHom ℚ)) i j =
      Rat.divInt ((A.updateCol i (fun k => B k j)).det) A.det := by
  let AQ := A.map (Int.castRingHom ℚ)
  have hdet : AQ.det ≠ 0 := by
    change (A.map (fun z : ℤ => (z : ℚ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hA
  have h := Matrix.det_smul_inv_mulVec_eq_cramer AQ ((B.map (Int.castRingHom ℚ)).col j)
    (isUnit_iff_ne_zero.mpr hdet)
  have hi := congrFun h i
  simp only [Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply] at hi
  have hcol : AQ.updateCol i ((B.map (Int.castRingHom ℚ)).col j) =
      (A.updateCol i (fun k => B k j)).map (Int.castRingHom ℚ) := by
    ext a b
    simp [AQ,Matrix.updateCol_apply,Matrix.col,Matrix.map_apply]
  rw [hcol] at hi
  change AQ.det * (AQ⁻¹ *ᵥ (B.map (Int.castRingHom ℚ)).col j) i =
    ((A.updateCol i (fun k => B k j)).map (fun z : ℤ => (z : ℚ))).det at hi
  rw [← Int.cast_det] at hi
  change AQ.det * (AQ⁻¹ * B.map (Int.castRingHom ℚ)) i j = _ at hi
  rw [Rat.divInt_eq_div]
  apply (eq_div_iff (show (A.det : ℚ) ≠ 0 from by exact_mod_cast hA)).mpr
  rw [mul_comm]
  have he : AQ.det = (A.det : ℚ) := (Int.cast_det A).symm
  rw [he] at hi
  exact hi

lemma nat_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have : 0 < 2^n := by positivity
    omega

lemma determinant_pow_bound {d b : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ)^b) : |A.det| < (2 : ℤ)^(d*d+d*b+1) := by
  have hb := determinant_bound A (2^b) (by simpa using hA)
  have hf : d.factorial ≤ (2^d)^d :=
    (Nat.factorial_le_pow d).trans (Nat.pow_le_pow_left ((nat_le_two_pow d)) d)
  have hfc : (d.factorial : ℤ) ≤ ((2 : ℤ)^d)^d := by exact_mod_cast hf
  have hn : |A.det| ≤ (2 : ℤ)^(d*d+d*b) := by
    calc |A.det| ≤ (d.factorial : ℤ)*((2 : ℤ)^b)^d := by simpa using hb
         _ ≤ ((2 : ℤ)^d)^d*((2 : ℤ)^b)^d := mul_le_mul_of_nonneg_right hfc (by positivity)
         _ = _ := by rw [← pow_mul,← pow_mul,← pow_add]; congr 1; ring
  apply hn.trans_lt
  rw [pow_succ]
  have : (0 : ℤ) < 2^(d*d+d*b) := by positivity
  omega

lemma normalization_bit_bound {d b : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (hA : A.det ≠ 0)
    (hAb : ∀ i j, |A i j| ≤ (2 : ℤ)^b) (hBb : ∀ i j, |B i j| ≤ (2 : ℤ)^b) (i j : Fin d) :
    (encodeRat (((A.map (Int.castRingHom ℚ))⁻¹ * B.map (Int.castRingHom ℚ)) i j)).length ≤
      4*(d*d+d*b+1)+3 := by
  rw [normalized_entry_ratio A B hA i j]
  apply encodeRat_ratio_le _ _ hA
  · have h := determinant_pow_bound (A.updateCol i (fun k => B k j)) (b := b) (by
      intro a c
      by_cases hc : c = i
      · simpa [Matrix.updateCol_apply,hc] using hBb a j
      · simpa [Matrix.updateCol_apply,hc] using hAb a c)
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · have h := determinant_pow_bound A hAb
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h

end RationalHitting.EncodingBounds

namespace RationalHitting.EncodingBounds

lemma flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length*B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [Nat.add_mul,Nat.one_mul]
    omega

lemma tuple_length_le {n d B : ℕ} (X : Tuple n d)
    (h : ∀ a i j, (encodeRat (X a i j)).length ≤ B) :
    (encodeTuple X).length ≤ n*d*d*B := by
  unfold encodeTuple
  calc _ ≤ (List.finRange n).length*(d*(d*B)) := by
          apply flatMap_length_le
          intro a _
          calc _ ≤ (List.finRange d).length*(d*B) := by
                   apply flatMap_length_le
                   intro i _
                   calc _ ≤ (List.finRange d).length*B := flatMap_length_le _ _ B (fun j _ => h
                     a i j)
                        _ = _ := by simp
               _ = _ := by simp
       _ = _ := by simp [Nat.mul_assoc]

lemma encodeNat_linear (a : ℕ) : (encodeNat a).length ≤ 2*(a+1)+1 := by
  apply encodeNat_le
  have h := nat_le_two_pow a
  have hp : 0 < 2^a := by positivity
  rw [pow_succ]
  omega

lemma output_length_le {n B : ℕ} (H : Output n)
    (hb : ∀ X ∈ H.tuples, ∀ a i j, (encodeRat (X a i j)).length ≤ B) :
    (encodeOutput H).length ≤ 2*(H.dimension+1)+1 + 2*(H.tuples.length+1)+1 +
      H.tuples.length*n*H.dimension*H.dimension*B := by
  have hd := encodeNat_linear H.dimension
  have hc := encodeNat_linear H.tuples.length
  have ht := flatMap_length_le H.tuples encodeTuple (n*H.dimension*H.dimension*B)
    (fun X hX => tuple_length_le X (hb X hX))
  simp only [encodeOutput,List.length_append] at *
  rw [← Nat.mul_assoc,← Nat.mul_assoc,← Nat.mul_assoc] at ht
  omega

end RationalHitting.EncodingBounds


namespace RationalHitting.PolynomialBounds

/-- Coefficient/exponent bookkeeping, with no symbolic expansion of large powers. -/
lemma mul_monomials (a b m i j : ℕ) : (a*m^i)*(b*m^j) = (a*b)*m^(i+j) := by
  rw [pow_add]
  ac_rfl

lemma lift_power (c m i j : ℕ) (hm : 1 ≤ m) (hij : i ≤ j) : c*m^i ≤ c*m^j :=
  Nat.mul_le_mul_left c (Nat.pow_le_pow_right hm hij)

lemma one_le_pow (m k : ℕ) (hm : 1 ≤ m) : 1 ≤ m^k :=
  Nat.one_le_pow k m hm

/-- Exponent bounding all denominator-cleared matrix entries by a power of 2. -/
def logarithmic (n s : ℕ) : ℕ :=
  4*Parameters.ambientDimension n s + 4*Parameters.ambientDimension n s*(n+1) +
    3*Parameters.ambientDimension n s*Parameters.gridSize n s

/-- Fixed coefficient bounding the binary logarithm of integral entry magnitudes. -/
def logConstant : ℕ := 64+64+3*16*24577

theorem logarithmic_bound (n s : ℕ) (hn : 1 ≤ n) :
    logarithmic n s ≤ logConstant*(n+s+1)^22 := by
  let m := n+s+1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hM := Parameters.polynomial_M n s
  have hH := Parameters.polynomial_H n s hn
  have h₁ : 4*Parameters.ambientDimension n s ≤ 64*m^22 := by
    calc _ ≤ 4*(16*m^5) := Nat.mul_le_mul_left 4 hM
         _ = 64*m^5 := by rw [← Nat.mul_assoc]
         _ ≤ _ := lift_power _ _ _ _ hm (by omega)
  have h₂ : 4*Parameters.ambientDimension n s*(n+1) ≤ 64*m^22 := by
    calc _ ≤ (64*m^5)*m := by
               apply Nat.mul_le_mul
               · calc _ ≤ 4*(16*m^5) := Nat.mul_le_mul_left 4 hM
                      _ = _ := by rw [← Nat.mul_assoc]
               · dsimp [m]; omega
         _ = 64*m^6 := by rw [show m^6 = m^5*m from pow_succ m 5,Nat.mul_assoc]
         _ ≤ _ := lift_power _ _ _ _ hm (by omega)
  have h₃ : 3*Parameters.ambientDimension n s*Parameters.gridSize n s ≤ (3*16*24577)*m^22 := by
    calc _ ≤ (3*(16*m^5))*(24577*m^17) := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hM) hH
         _ = (48*m^5)*(24577*m^17) := by rw [← Nat.mul_assoc 3 16]
         _ = _ := mul_monomials 48 24577 m 5 17
  unfold logarithmic logConstant
  change _ ≤ (64+64+3*16*24577)*m^22
  rw [Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃

/-- Fixed coefficient in the bound on normalized rational entry encodings. -/
def bitConstant : ℕ := 4*(256*256+256*logConstant+1)+3

theorem normalized_bits_bound (m D b : ℕ) (hm : 1 ≤ m)
    (hD : D ≤ 256*m^10) (hb : b ≤ logConstant*m^22) :
    4*(D*D+D*b+1)+3 ≤ bitConstant*m^32 := by
  have h₁ : D*D ≤ (256*256)*m^32 := by
    calc _ ≤ (256*m^10)*(256*m^10) := Nat.mul_le_mul hD hD
         _ = (256*256)*m^20 := mul_monomials ..
         _ ≤ _ := lift_power _ _ _ _ hm (by omega)
  have h₂ : D*b ≤ (256*logConstant)*m^32 := by
    calc _ ≤ (256*m^10)*(logConstant*m^22) := Nat.mul_le_mul hD hb
         _ = _ := mul_monomials ..
  have hp := one_le_pow m 32 hm
  unfold bitConstant
  rw [Nat.add_mul,Nat.mul_assoc,Nat.add_mul,Nat.add_mul,one_mul]
  omega

/-- Fixed coefficient in the bound on the complete binary output length. -/
def outputConstant : ℕ := (2*256+3) + (2*24577^3+3) + 24577^3*256*256*bitConstant

theorem output_bits_bound (n m D L B : ℕ) (hm : 1 ≤ m) (hn : n ≤ m)
    (hD : D ≤ 256*m^10) (hL : L ≤ 24577^3*m^51) (hB : B ≤ bitConstant*m^32) :
    2*(D+1)+1 + 2*(L+1)+1 + L*n*D*D*B ≤ outputConstant*m^104 := by
  have hp := one_le_pow m 104 hm
  have hd : D ≤ 256*m^104 := hD.trans (lift_power _ _ _ _ hm (by omega))
  have hl : L ≤ 24577^3*m^104 := hL.trans (lift_power _ _ _ _ hm (by omega))
  have hproduct : L*n*D*D*B ≤ (24577^3*256*256*bitConstant)*m^104 := by
    calc _ ≤ (24577^3*m^51)*m*(256*m^10)*(256*m^10)*(bitConstant*m^32) := by
               gcongr
         _ = _ := by
           have hh := mul_monomials (24577^3*256*256) bitConstant m 72 32
           calc _ = ((24577^3*256*256)*m^72)*(bitConstant*m^32) := by
                     congr 1
                     calc _ = ((24577^3*256)*m^62)*(256*m^10) := by
                                congr 1
                                calc _ = (24577^3*m^52)*(256*m^10) := by
                                           congr 1
                                           rw [show m^52=m^51*m from pow_succ m 51,Nat.mul_assoc]
                                     _ = _ := mul_monomials _ _ _ _ _
                          _ = _ := mul_monomials _ _ _ _ _
                _ = _ := hh
  unfold outputConstant
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.add_mul]
  omega

end RationalHitting.PolynomialBounds

namespace RationalHitting.Generator
open Matrix EncodingBounds
open scoped BigOperators
noncomputable section

lemma U_power_bound (n N e H : ℕ) (x : Fin 3 → ℕ) (hH : 1 ≤ H) (hx : ∀ l, x l ≤ H)
    (a : Fin (n+1)) (i j : Fin (matrixDimension e)) :
    |integralLift n N e x a i j| ≤ (2 : ℤ)^(4*CyclotomicRing.dimension e +
      4*CyclotomicRing.dimension e*(n+1)+3*CyclotomicRing.dimension e*H) := by
  let M := CyclotomicRing.dimension e
  have hM : (M : ℤ) ≤ 2^M := by exact_mod_cast nat_le_two_pow M
  have hn : (2*(n+1) : ℤ) ≤ 2^(2*(n+1)) := by exact_mod_cast nat_le_two_pow (2*(n+1))
  have hh : (H : ℤ) ≤ 2^H := by exact_mod_cast nat_le_two_pow H
  calc _ ≤ (M : ℤ)^4*(2*(n+1) : ℤ)^(2*M)*(H : ℤ)^(3*M) := U_bound n N e H x hH hx a i j
       _ ≤ ((2 : ℤ)^M)^4*((2 : ℤ)^(2*(n+1)))^(2*M)*((2 : ℤ)^H)^(3*M) := by
          gcongr
       _ = _ := by
          simp only [← pow_mul,← pow_add]
          congr 1
          dsimp [M]
          ring

lemma tupleAt_bit_bound (n N e H : ℕ) (x : Fin 3 → ℕ) (hH : 1 ≤ H) (hx : ∀ l, x l ≤ H)
    (hz : (rationalLift n N e x 0).det ≠ 0) (a : Fin n) (i j : Fin (matrixDimension e)) :
    (encodeRat (tupleAt n N e x a i j)).length ≤
      4*(matrixDimension e*matrixDimension e+matrixDimension e*(4*CyclotomicRing.dimension e +
        4*CyclotomicRing.dimension e*(n+1)+3*CyclotomicRing.dimension e*H)+1)+3 := by
  rw [tupleAt_integer n N e x hz a]
  exact normalization_bit_bound _ _ (U_det_ne_zero n N e x hz)
    (U_power_bound n N e H x hH hx 0) (U_power_bound n N e H x hH hx a.succ) i j

lemma output_entry_bit_bound (n N e H : ℕ) (hH : 1 ≤ H)
    (X : Tuple n (matrixDimension e)) (hX : X ∈ (output n N e H).tuples)
    (a : Fin n) (i j : Fin (matrixDimension e)) :
    (encodeRat (X a i j)).length ≤
      4*(matrixDimension e*matrixDimension e+matrixDimension e*(4*CyclotomicRing.dimension e +
        4*CyclotomicRing.dimension e*(n+1)+3*CyclotomicRing.dimension e*H)+1)+3 := by
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp hX
  by_cases hz : (rationalLift n N e (fun l => (x l).val+1) 0).det = 0
  · simp [atPoint,hz] at he
  · simp only [atPoint,ite_eq_right hz,Option.some.injEq] at he
    rw [← he]
    exact tupleAt_bit_bound n N e H _ hH (fun l => by omega) hz a i j

lemma list_output_bound (n s : ℕ) (hn : 1 ≤ n) :
    (encodeOutput (list n s)).length ≤ PolynomialBounds.outputConstant*(n+s+1)^104 := by
  have hH : 1 ≤ Parameters.gridSize n s := by unfold Parameters.gridSize; omega
  have hb : ∀ X ∈ (list n s).tuples, ∀ a i j,
      (encodeRat (X a i j)).length ≤ PolynomialBounds.bitConstant*(n+s+1)^32 := by
    intro X hX a i j
    apply (output_entry_bit_bound n (Parameters.truncation n s) (Parameters.exponent n s)
      (Parameters.gridSize n s) hH X hX a i j).trans
    apply PolynomialBounds.normalized_bits_bound (hm := by omega)
    · exact list_dimension_bound n s
    · exact PolynomialBounds.logarithmic_bound n s hn
  apply (output_length_le (list n s) hb).trans
  apply PolynomialBounds.output_bits_bound (hm := by omega) (hn := by omega)
  · exact list_dimension_bound n s
  · exact list_length_bound n s hn
  · exact Nat.le_refl _

end
end RationalHitting.Generator


/- A staged division-free determinant computation for integer matrices.
Explicit dense tables prevent recursive matrix-entry recomputation. -/

end Complexity

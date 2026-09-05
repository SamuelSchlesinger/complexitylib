/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHAssembleWindow
public import Complexitylib.Classes.Containments.Internal.PSPACESubsetEXP

/-!
# The enumerator's bounds, in the input's length

⚠️ Unreviewed by Bolton

Every quantity the enumerator's contracts and windows are stated in terms of — the width of a
pair, the number of digits in a counter, the running time of a stage — is bounded by a polynomial
in the input's length. This file collects those bounds.

## Main results

- `PolyExists.dropTop_length_le`, `PolyExists.pair_length_le` — the witness and the pair it goes
  into are no wider than the horizon's exponent allows
- `PolyExists.bits_length_le` — a counter below the horizon has that many digits
- `PolyExists.tally_le` — a tally never exceeds its count
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- **A witness below the horizon is no longer than the exponent.** -/
theorem dropTop_length_le (m j N : ℕ) (hN : N = 2 ^ (m + 1) - 1) (hj : j < N) :
    (dropTop (j + 1)).length ≤ m := by
  refine length_dropTop_le (m := m) ?_
  have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  omega

/-- **And the pair it goes into is bounded too.** -/
theorem pair_length_le (x : List Bool) (m j N : ℕ) (hN : N = 2 ^ (m + 1) - 1) (hj : j < N) :
    (pair x (dropTop (j + 1))).length ≤ 2 * x.length + 2 + m := by
  rw [pair_length]
  have := dropTop_length_le m j N hN hj
  omega

/-- **A counter at most the horizon has at most `m + 1` digits.** -/
theorem bits_length_le (m j N : ℕ) (hN : N = 2 ^ (m + 1) - 1) (hj : j ≤ N) :
    j.bits.length ≤ m + 1 := by
  have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have hjlt : j < 2 ^ (m + 1) := by omega
  have hsize : j.size ≤ m + 1 := Nat.size_le.mpr hjlt
  rw [Nat.size_eq_bits_len j]
  exact hsize

/-- **A tally never exceeds its count.** -/
theorem tally_le (P : ℕ → Bool) : ∀ v, NTM.tally P v ≤ v
  | 0 => le_refl 0
  | v + 1 => by
      have := tally_le P v
      rw [NTM.tally]
      split <;> omega

/-- **The successor's running time, in digits.** -/
theorem binarySuccTime_le' (m v N : ℕ) (hN : N = 2 ^ (m + 1) - 1) (hv : v ≤ N) :
    TM.binarySuccTime v ≤ 2 * (m + 1) + 2 := by
  refine le_trans (BinarySucc.steps_le v.bits) ?_
  have := bits_length_le m v N hN hv
  omega

/-- **The witness advance's running time.** -/
theorem binaryBumpTime_le' (m j N : ℕ) (hN : N = 2 ^ (m + 1) - 1) (hj : j < N) :
    TM.binaryBumpTime (dropTop (j + 1)) ≤ 2 * m + 2 := by
  refine le_trans (BinaryBump.steps_le _) ?_
  have := dropTop_length_le m j N hN hj
  omega

/-- **The comparison's running time.** -/
theorem binaryEqTime_le' (m j N : ℕ) (hN : N = 2 ^ (m + 1) - 1) (hj : j < N) :
    TM.binaryEqTime (j + 1).bits N.bits ≤ m + 2 := by
  rw [TM.binaryEqTime]
  have h1 := bits_length_le m (j + 1) N hN (by omega)
  have h2 := bits_length_le m N N hN (le_refl N)
  omega

/-- **A polynomial with natural coefficients is monotone.** -/
theorem eval_mono (r : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : r.eval a ≤ r.eval b := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add]
      omega
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-! ## The bounds themselves -/

/-- The width of the pair the matrix machine reads. -/
def bP (lx m : ℕ) : ℕ := 2 * lx + 2 + m

/-- The window the matrix machine needs. -/
def bHb (lx m sb : ℕ) : ℕ := bP lx m + sb + 2

/-- The wipe height. -/
def bH (lx m sb : ℕ) : ℕ := bHb lx m sb + 1

/-- The bound on the heads the rewinds have to chase. -/
def bB (lx m : ℕ) : ℕ := (lx + 1) + (2 * lx + m + 4) + (m + 4)

/-- The uniform bound on every head of every intermediate state. -/
def bG (lx m sb : ℕ) : ℕ := (bHb lx m sb + 1) + bB lx m + (bP lx m + 1)

theorem bP_le_bHb (lx m sb : ℕ) : bP lx m ≤ bHb lx m sb := by
  rw [bHb]
  omega

theorem bHb_lt_bH (lx m sb : ℕ) : bHb lx m sb + 1 ≤ bH lx m sb := le_refl _

theorem bP_lt_bH (lx m sb : ℕ) : bP lx m + 1 ≤ bH lx m sb := by
  have := bP_le_bHb lx m sb
  rw [bH]
  omega

theorem bB_le_bG (lx m sb : ℕ) : bB lx m ≤ bG lx m sb := by
  rw [bG]
  omega

theorem bHb_le_bG (lx m sb : ℕ) : bHb lx m sb + 1 ≤ bG lx m sb := by
  rw [bG]
  omega

theorem bP_le_bG (lx m sb : ℕ) : bP lx m + 1 ≤ bG lx m sb := by
  rw [bG]
  omega

theorem one_le_bG (lx m sb : ℕ) : 1 ≤ bG lx m sb := by
  rw [bG, bB]
  omega

theorem one_le_bB (lx m : ℕ) : 1 ≤ bB lx m := by
  rw [bB]
  omega

theorem one_le_bHb (lx m sb : ℕ) : 1 ≤ bHb lx m sb := by
  rw [bHb, bP]
  omega

/-- The window the whole machine runs in: the uniform head bound plus one summand for every
stage's own budget. Sums, not maxima, so that the whole thing is visibly a polynomial in the
input's length. -/
def bW (st lx m sb pro epi : ℕ) : ℕ :=
  bG lx m sb
    + 1
    + (2 * lx + m + 3)
    + (1 + 1 + (2 * ((bB lx m + 2) + (3 * (bB lx m + 3) + 1) + 1) + 1))
    + (2 * bP lx m + 5)
    + (1 + 1 + (2 * ((bHb lx m sb + 2) + (1 * (bHb lx m sb + 3) + 1) + 1) + 1))
    + (3 * ((1 + 1 + ((2 * (m + 1) + 2) + (2 * (m + 1) + 2)) + 5) + (2 * (m + 1) + 2) + 1) + 1)
    + (2 * m + 2)
    + (st * (bH lx m sb + 4) + bH lx m sb * 4 + 8 + 1 + (st * (bH lx m sb + 4) + 1))
    + ((m + 2) + 1 + (3 * ((3 * (bB lx m + 3) + 1) + (bB lx m + 2 + 1 + (2 * 1 + 5)) + 1) + 1))
    + (1 + lx + 1)
    + ((lx + 1) + (1 + 1 + (2 * ((bB lx m + 2) + (1 * (bB lx m + 3) + 1) + 1) + 1)))
    + (1 + pro)
    + (1 + epi)

theorem bG_le_bW (st lx m sb pro epi : ℕ) : bG lx m sb ≤ bW st lx m sb pro epi := by
  rw [bW]
  omega

theorem one_le_bW (st lx m sb pro epi : ℕ) : 1 ≤ bW st lx m sb pro epi := by
  have := one_le_bG lx m sb
  have := bG_le_bW st lx m sb pro epi
  omega

section Bounds

variable (st lx m sb pro epi : ℕ)

theorem bW_stage1 : bG lx m sb + 1 ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_stage2 (x w : List Bool) (hx : x.length = lx) (hw : w.length ≤ m) :
    bG lx m sb + TM.pairInputWorkTime x w ≤ bW st lx m sb pro epi := by
  rw [bW, TM.pairInputWorkTime, hx]
  omega

theorem bW_stage3 : bG lx m sb +
    (1 + 1 + (2 * (max (bB lx m + 2) (3 * (bB lx m + 3) + 1) + 1) + 1))
      ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_stage4 (P : ℕ) (hP : P ≤ bP lx m) :
    bG lx m sb + (2 * P + 5) ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_stage6 : bG lx m sb +
    (1 + 1 + (2 * (max (bHb lx m sb + 2) (1 * (bHb lx m sb + 3) + 1) + 1) + 1))
      ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_stage8 (a r v : ℕ) (ha : TM.binarySuccTime a ≤ 2 * (m + 1) + 2)
    (hr : TM.binarySuccTime r ≤ 2 * (m + 1) + 2) (hv : TM.binarySuccTime v ≤ 2 * (m + 1) + 2) :
    bG lx m sb + (3 * (max (1 + 1 + max (TM.binarySuccTime a) (TM.binarySuccTime r) + 5)
      (TM.binarySuccTime v) + 1) + 1) ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_stage9 (t : ℕ) (ht : t ≤ 2 * m + 2) :
    bG lx m sb + t ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_stage10 (H : ℕ) (hH : H = bH lx m sb) :
    bG lx m sb + (st * (H + 4) + H * 4 + 8 + 1 + (st * (H + 4) + 1))
      ≤ bW st lx m sb pro epi := by
  rw [bW, hH]; omega

theorem bW_test (N j : ℕ) (hj : TM.binaryEqTime (j + 1).bits N.bits ≤ m + 2) :
    bG lx m sb + testTime (bB lx m) N j ≤ bW st lx m sb pro epi := by
  rw [bW, testTime, TM.resetBinaryWorkTime, TM.clearWorkTimeBound]
  omega

theorem bW_copy : 1 + (lx + 1) ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_rewind : (lx + 1) +
    (1 + 1 + (2 * (max (bB lx m + 2) (1 * (bB lx m + 3) + 1) + 1) + 1))
      ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_prologue : 1 + pro ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_epilogue (e : ℕ) (he : e ≤ epi) : 1 + e ≤ bW st lx m sb pro epi := by
  rw [bW]; omega

theorem bW_matrix : bHb lx m sb ≤ bW st lx m sb pro epi := by
  have := bHb_le_bG lx m sb
  have := bG_le_bW st lx m sb pro epi
  omega

end Bounds

/-! ## The bounds as polynomials -/

/-- The width of the pair, as a polynomial in the input's length. -/
noncomputable def bPPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 2 + p

@[simp] theorem bPPoly_eval (p : Polynomial ℕ) (lx : ℕ) :
    (bPPoly p).eval lx = bP lx (p.eval lx) := by
  simp only [bPPoly, bP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

/-- The matrix machine's window, as a polynomial. -/
noncomputable def bHbPoly (p s : Polynomial ℕ) : Polynomial ℕ :=
  bPPoly p + s.comp (bPPoly p) + Polynomial.C 2

@[simp] theorem bHbPoly_eval (p s : Polynomial ℕ) (lx : ℕ) :
    (bHbPoly p s).eval lx = bHb lx (p.eval lx) (s.eval (bP lx (p.eval lx))) := by
  simp only [bHbPoly, bHb, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_comp,
    bPPoly_eval]

/-- The wipe height, as a polynomial. -/
noncomputable def bHPoly (p s : Polynomial ℕ) : Polynomial ℕ := bHbPoly p s + 1

@[simp] theorem bHPoly_eval (p s : Polynomial ℕ) (lx : ℕ) :
    (bHPoly p s).eval lx = bH lx (p.eval lx) (s.eval (bP lx (p.eval lx))) := by
  simp only [bHPoly, bH, Polynomial.eval_add, Polynomial.eval_one, bHbPoly_eval]

/-- The rewind bound, as a polynomial. -/
noncomputable def bBPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.X + 1) + (Polynomial.C 2 * Polynomial.X + p + Polynomial.C 4) +
    (p + Polynomial.C 4)

@[simp] theorem bBPoly_eval (p : Polynomial ℕ) (lx : ℕ) :
    (bBPoly p).eval lx = bB lx (p.eval lx) := by
  simp only [bBPoly, bB, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]

/-- The uniform head bound, as a polynomial. -/
noncomputable def bGPoly (p s : Polynomial ℕ) : Polynomial ℕ :=
  (bHbPoly p s + 1) + bBPoly p + (bPPoly p + 1)

@[simp] theorem bGPoly_eval (p s : Polynomial ℕ) (lx : ℕ) :
    (bGPoly p s).eval lx = bG lx (p.eval lx) (s.eval (bP lx (p.eval lx))) := by
  simp only [bGPoly, bG, Polynomial.eval_add, Polynomial.eval_one, bHbPoly_eval, bBPoly_eval,
    bPPoly_eval]

/-- The Horner cap, as a polynomial. -/
noncomputable def capPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C ((TM.polyCoeffs p).sum + 1) * (Polynomial.X + 1) ^ (TM.polyCoeffs p).length

@[simp] theorem capPoly_eval (p : Polynomial ℕ) (lx : ℕ) :
    (capPoly p).eval lx = prologueCap p lx := by
  simp only [capPoly, prologueCap, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

/-- The register machine's per-operation budget, as a polynomial. -/
noncomputable def opBudgetPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 32 * (capPoly p + Polynomial.C 2) ^ 3

@[simp] theorem opBudgetPoly_eval (p : Polynomial ℕ) (lx : ℕ) :
    (opBudgetPoly p).eval lx = TM.opBudget (prologueCap p lx) := by
  simp only [opBudgetPoly, TM.opBudget, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, capPoly_eval]
  ring

/-- Its per-layer budget. -/
noncomputable def layerBudgetPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 4 * opBudgetPoly p + Polynomial.C 3

@[simp] theorem layerBudgetPoly_eval (p : Polynomial ℕ) (lx : ℕ) :
    (layerBudgetPoly p).eval lx = TM.layerBudget (prologueCap p lx) := by
  simp only [layerBudgetPoly, TM.layerBudget, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, opBudgetPoly_eval]

/-- The prologue's running time, dominated by a polynomial. -/
noncomputable def proPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 7 * ((Polynomial.C 2 * Polynomial.X + Polynomial.C 4) +
    (opBudgetPoly p + 1 + (Polynomial.C (p.natDegree + 1) * (layerBudgetPoly p + 1) + 1)) +
    (Polynomial.C 2 * p + Polynomial.C 4) +
    (opBudgetPoly q + 1 + (Polynomial.C (q.natDegree + 1) * (layerBudgetPoly q + 1) + 1)) +
    (Polynomial.C 2 * q + Polynomial.C 4) + 1) + 1

theorem prologueTime_le (p q : Polynomial ℕ) (lx : ℕ) :
    prologueTime p q lx ≤ (proPoly p q).eval lx := by
  rw [prologueTime, prologueBnd, proPoly]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, opBudgetPoly_eval, layerBudgetPoly_eval]
  omega

/-- The epilogue's running time, dominated by a polynomial. -/
noncomputable def epiPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 6 * p + Polynomial.C 50

theorem epilogueTime_le (m A N : ℕ) (hN : N = 2 ^ (m + 1) - 1) (hA : A ≤ N) :
    epilogueTime A ≤ 6 * m + 50 := by
  have hsize : A.size ≤ m + 1 := by
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    exact Nat.size_le.mpr (by omega)
  have hsucc : TM.binarySuccTime 0 = 2 := rfl
  have hsub : TM.binaryRippleSubTime 1 A ≤ 3 * m + 14 := by
    rw [TM.binaryRippleSubTime]
    have h1 : (1 : ℕ).size = 1 := rfl
    omega
  have heq : TM.binaryEqTime (1 - A).bits (0 : ℕ).bits ≤ 2 := by
    rw [TM.binaryEqTime]
    have h0 : (0 : ℕ).bits = [] := by simp
    have h1 : (1 - A).bits.length ≤ 1 := by
      rcases Nat.eq_zero_or_pos A with rfl | hpos
      · show (1 - 0 : ℕ).bits.length ≤ 1
        decide
      · have : 1 - A = 0 := by omega
        rw [this]
        simp
    rw [h0]
    simp only [List.length_nil]
    omega
  rw [epilogueTime, hsucc]
  omega

/-- **The enumerator's space bound, as a polynomial.** -/
noncomputable def bWPoly (st : ℕ) (p s q : Polynomial ℕ) : Polynomial ℕ :=
  bGPoly p s
    + 1
    + (Polynomial.C 2 * Polynomial.X + p + Polynomial.C 3)
    + (1 + 1 + (Polynomial.C 2 * ((bBPoly p + Polynomial.C 2) +
        (Polynomial.C 3 * (bBPoly p + Polynomial.C 3) + 1) + 1) + 1))
    + (Polynomial.C 2 * bPPoly p + Polynomial.C 5)
    + (1 + 1 + (Polynomial.C 2 * ((bHbPoly p s + Polynomial.C 2) +
        (Polynomial.C 1 * (bHbPoly p s + Polynomial.C 3) + 1) + 1) + 1))
    + (Polynomial.C 3 * ((1 + 1 + ((Polynomial.C 2 * (p + 1) + Polynomial.C 2) +
        (Polynomial.C 2 * (p + 1) + Polynomial.C 2)) + Polynomial.C 5) +
        (Polynomial.C 2 * (p + 1) + Polynomial.C 2) + 1) + 1)
    + (Polynomial.C 2 * p + Polynomial.C 2)
    + (Polynomial.C st * (bHPoly p s + Polynomial.C 4) + bHPoly p s * Polynomial.C 4 +
        Polynomial.C 8 + 1 + (Polynomial.C st * (bHPoly p s + Polynomial.C 4) + 1))
    + ((p + Polynomial.C 2) + 1 + (Polynomial.C 3 *
        ((Polynomial.C 3 * (bBPoly p + Polynomial.C 3) + 1) +
          (bBPoly p + Polynomial.C 2 + 1 + (Polynomial.C 2 * 1 + Polynomial.C 5)) + 1) + 1))
    + (1 + Polynomial.X + 1)
    + ((Polynomial.X + 1) + (1 + 1 + (Polynomial.C 2 * ((bBPoly p + Polynomial.C 2) +
        (Polynomial.C 1 * (bBPoly p + Polynomial.C 3) + 1) + 1) + 1)))
    + (1 + proPoly p q)
    + (1 + epiPoly p)

@[simp] theorem bWPoly_eval (st : ℕ) (p s q : Polynomial ℕ) (lx : ℕ) :
    (bWPoly st p s q).eval lx =
      bW st lx (p.eval lx) (s.eval (bP lx (p.eval lx))) ((proPoly p q).eval lx)
        ((epiPoly p).eval lx) := by
  simp only [bWPoly, bW, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, bGPoly_eval, bBPoly_eval, bPPoly_eval,
    bHbPoly_eval, bHPoly_eval]

@[simp] theorem epiPoly_eval (p : Polynomial ℕ) (lx : ℕ) :
    (epiPoly p).eval lx = 6 * p.eval lx + 50 := by
  simp only [epiPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

/-- **A tally is positive exactly when something below the count satisfied the predicate.** -/
theorem tally_pos_iff (P : ℕ → Bool) : ∀ N, 0 < NTM.tally P N ↔ ∃ j, j < N ∧ P j = true
  | 0 => by
      constructor
      · intro h
        exact absurd h (by simp [NTM.tally])
      · rintro ⟨j, hj, -⟩
        omega
  | N + 1 => by
      have ih := tally_pos_iff P N
      rw [NTM.tally]
      constructor
      · intro h
        by_cases hPN : P N
        · exact ⟨N, by omega, hPN⟩
        · rw [ite_eq_right (by simp [hPN])] at h
          obtain ⟨j, hj, hPj⟩ := ih.mp (by omega)
          exact ⟨j, by omega, hPj⟩
      · rintro ⟨j, hj, hPj⟩
        by_cases hjN : j = N
        · rw [hjN] at hPj
          rw [ite_eq_left (by simp [hPj])]
          omega
        · have := ih.mpr ⟨j, by omega, hPj⟩
          split <;> omega

/-- **What the machine computes is membership in the bounded existential.** -/
theorem tally_pos_iff_mem (L' : Language) (p : Polynomial ℕ) (x : List Bool) (N : ℕ)
    (hN : N = 2 ^ (p.eval x.length + 1) - 1) :
    0 < NTM.tally (enumP L' x) N ↔ x ∈ polyExistsLang p L' := by
  rw [tally_pos_iff, show (x ∈ polyExistsLang p L') ↔
      ∃ v < 2 ^ (p.eval x.length + 1), pair x (dropTop v) ∈ L' from
    (mem_polyExistsLang (p := p) (L := L') (x := x)).trans
      (exists_bounded_iff_count (p.eval x.length) (fun w => pair x w ∈ L'))]
  constructor
  · rintro ⟨j, hj, hPj⟩
    refine ⟨j + 1, ?_, (enumP_iff L' x j).mp hPj⟩
    have h1 : 1 ≤ 2 ^ (p.eval x.length + 1) := Nat.one_le_two_pow
    omega
  · rintro ⟨v, hv, hmem⟩
    have h1 : 1 ≤ 2 ^ (p.eval x.length + 1) := Nat.one_le_two_pow
    rcases Nat.eq_zero_or_pos v with rfl | hpos
    · refine ⟨0, by omega, (enumP_iff L' x 0).mpr ?_⟩
      show pair x (dropTop 1) ∈ L'
      have : dropTop 1 = dropTop 0 := by decide
      rw [this]
      exact hmem
    · refine ⟨v - 1, by omega, (enumP_iff L' x (v - 1)).mpr ?_⟩
      rw [show v - 1 + 1 = v from by omega]
      exact hmem

/-! ## The enumerator, instantiated -/

section Final

variable {k : ℕ}

/-- Every hypothesis the enumerator's contract and window need, at one input. -/
theorem enum_bounds {f : ℕ → ℕ} (s : Polynomial ℕ)
    (hs : ∀ n, f n ≤ s.eval n) (p : Polynomial ℕ)
    (x : List Bool) (j : ℕ)
    (hj : j < 2 ^ (p.eval x.length + 1) - 1) :
    1 + TM.pairInputWorkTime x (dropTop (j + 1)) ≤ bB x.length (p.eval x.length) ∧
    (pair x (dropTop (j + 1))).length + f (pair x (dropTop (j + 1))).length + 2 ≤
      bHb x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))) ∧
    (pair x (dropTop (j + 1))).length + 1 ≤
      bH x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))) ∧
    1 + 1 + TM.binaryEqTime (j + 1).bits (2 ^ (p.eval x.length + 1) - 1).bits ≤
      bB x.length (p.eval x.length) ∧
    (pair x (dropTop (j + 1))).length + 1 ≤
      bG x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))) := by
  set lx := x.length with hlx
  set m := p.eval lx with hm
  set N := 2 ^ (m + 1) - 1 with hNdef
  have hlen : (dropTop (j + 1)).length ≤ m := dropTop_length_le m j N hNdef hj
  have hpairlen : (pair x (dropTop (j + 1))).length ≤ bP lx m := by
    rw [pair_length, bP]
    omega
  have hfle : f (pair x (dropTop (j + 1))).length ≤ s.eval (bP lx m) :=
    le_trans (hs _) (eval_mono s hpairlen)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [TM.pairInputWorkTime, bB]
    omega
  · rw [bHb]
    omega
  · have := bP_lt_bH lx m (s.eval (bP lx m))
    omega
  · have := binaryEqTime_le' m j N hNdef hj
    rw [bB]
    omega
  · have := bP_le_bG lx m (s.eval (bP lx m))
    omega

end Final

/-- **The enumerator decides the bounded existential.** -/
theorem enumTM_decides (M : TM k) {L' : Language} {f : ℕ → ℕ} (s : Polynomial ℕ)
    (hs : ∀ n, f n ≤ s.eval n) (hdecS : M.DecidesInSpace L' f)
    (hdec : M.DecidesInTime L' (TM.spaceTimeBound M f))
    (p : Polynomial ℕ) (x : List Bool) (N H B Hb bBody bTest : ℕ)
    (hNdef : N = 2 ^ (p.eval x.length + 1) - 1)
    (hHdef : H = bH x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))))
    (hBdef : B = bB x.length (p.eval x.length))
    (hHbdef : Hb = bHb x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))))
    (hbBody : ∀ v, v < N → bodyTime k x (TM.spaceTimeBound M f) H Hb B v
      (NTM.tally (enumP L' x) v) (NTM.tally (fun u => !enumP L' x u) v) ≤ bBody)
    (hbTest : ∀ v, v < N → testTime B N v ≤ bTest) :
    ∃ c', (enumTM M p (bHPoly p s)).reaches ((enumTM M p (bHPoly p s)).initCfg x) c' ∧
      (enumTM M p (bHPoly p s)).halted c' ∧
      (x ∈ polyExistsLang p L' → c'.output.cells 1 = Γ.one) ∧
      (x ∉ polyExistsLang p L' → c'.output.cells 1 = Γ.zero) := by
  have hN : 1 ≤ N := by
    have h1 : 2 ≤ 2 ^ (p.eval x.length + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (p.eval x.length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbounds : ∀ v, v < N →
      1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B ∧
      (pair x (dropTop (v + 1))).length + f (pair x (dropTop (v + 1))).length + 2 ≤ Hb ∧
      (pair x (dropTop (v + 1))).length + 1 ≤ H ∧
      1 + 1 + TM.binaryEqTime (v + 1).bits N.bits ≤ B := by
    intro v hv
    have hv' : v < 2 ^ (p.eval x.length + 1) - 1 := by rw [← hNdef]; exact hv
    obtain ⟨h1, h2, h3, h4, -⟩ := enum_bounds s hs p x v hv'
    refine ⟨by rw [hBdef]; exact h1, by rw [hHbdef]; exact h2, by rw [hHdef]; exact h3, ?_⟩
    rw [hBdef, hNdef]
    exact h4
  obtain ⟨c', t, -, hreach, hhalt, hout⟩ :=
    enumTM_hoareTime M hdec hdecS p (bHPoly p s) x N H B Hb bBody bTest hNdef
      (by rw [hHdef, bHPoly_eval]) hN
      (by rw [hBdef]; exact one_le_bB _ _)
      (by rw [hBdef, bB]; omega)
      (by rw [hHbdef]; exact one_le_bHb _ _ _)
      (fun v hv => (hbounds v hv).1) (fun v hv => (hbounds v hv).2.1)
      (by rw [hHbdef, hHdef]; exact bHb_lt_bH _ _ _)
      (fun v hv => (hbounds v hv).2.2.1) hbBody
      (fun v hv => (hbounds v hv).2.2.2) hbTest
      (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init ([] : List Γ))
      (Tape.init ([] : List Γ)) ⟨rfl, rfl, rfl⟩
  refine ⟨c', TM.reaches_of_reachesIn hreach, hhalt, ?_, ?_⟩
  · intro hmem
    have hb : decide (0 < NTM.tally (enumP L' x) N) = true :=
      decide_eq_true ((tally_pos_iff_mem L' p x N hNdef).mpr hmem)
    rw [hout, NTM.outSlot_cells_one, hb]
    rfl
  · intro hmem
    have hb : decide (0 < NTM.tally (enumP L' x) N) = false :=
      decide_eq_false (fun hc => hmem ((tally_pos_iff_mem L' p x N hNdef).mp hc))
    rw [hout, NTM.outSlot_cells_one, hb]
    rfl

/-- **The enumerator keeps a polynomial window.** -/
theorem enumTM_space (M : TM k) {L' : Language} {f : ℕ → ℕ} (s : Polynomial ℕ)
    (hs : ∀ n, f n ≤ s.eval n) (hdecS : M.DecidesInSpace L' f)
    (hdec : M.DecidesInTime L' (TM.spaceTimeBound M f)) (hne : M.qstart ≠ M.qhalt)
    (p : Polynomial ℕ) (x : List Bool) (N H B Hb G W bBody bTest : ℕ)
    (hNdef : N = 2 ^ (p.eval x.length + 1) - 1)
    (hHdef : H = bH x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))))
    (hBdef : B = bB x.length (p.eval x.length))
    (hHbdef : Hb = bHb x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))))
    (hGdef : G = bG x.length (p.eval x.length) (s.eval (bP x.length (p.eval x.length))))
    (hWdef : W = bW ((scratchTargets k).length) x.length (p.eval x.length)
      (s.eval (bP x.length (p.eval x.length)))
      ((proPoly p (bHPoly p s)).eval x.length) ((epiPoly p).eval x.length))
    (hbBody : ∀ v, v < N → bodyTime k x (TM.spaceTimeBound M f) H Hb B v
      (NTM.tally (enumP L' x) v) (NTM.tally (fun u => !enumP L' x u) v) ≤ bBody)
    (hbTest : ∀ v, v < N → testTime B N v ≤ bTest) :
    ∀ c', (enumTM M p (bHPoly p s)).reaches ((enumTM M p (bHPoly p s)).initCfg x) c' →
      c'.WithinDecisionSpace x.length W := by
  have hN : 1 ≤ N := by
    have h1 : 2 ≤ 2 ^ (p.eval x.length + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (p.eval x.length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbounds : ∀ v, v < N →
      1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B ∧
      (pair x (dropTop (v + 1))).length + f (pair x (dropTop (v + 1))).length + 2 ≤ Hb ∧
      (pair x (dropTop (v + 1))).length + 1 ≤ H ∧
      1 + 1 + TM.binaryEqTime (v + 1).bits N.bits ≤ B ∧
      (pair x (dropTop (v + 1))).length + 1 ≤ G := by
    intro v hv
    have hv' : v < 2 ^ (p.eval x.length + 1) - 1 := by rw [← hNdef]; exact hv
    obtain ⟨h1, h2, h3, h4, h5⟩ := enum_bounds s hs p x v hv'
    exact ⟨by rw [hBdef]; exact h1, by rw [hHbdef]; exact h2, by rw [hHdef]; exact h3,
      by rw [hBdef, hNdef]; exact h4, by rw [hGdef]; exact h5⟩
  have hlenw : ∀ v, v < N → (dropTop (v + 1)).length ≤ p.eval x.length := by
    intro v hv
    exact dropTop_length_le _ v _ hNdef hv
  have hpairle : ∀ v, v < N →
      (pair x (dropTop (v + 1))).length ≤ bP x.length (p.eval x.length) := by
    intro v hv
    rw [pair_length, bP]
    have := hlenw v hv
    omega
  have hloopW := enumLoop_keepsWindowOn M hdec hdecS hne x N H hN (strTape x)
    (strTape_parked x) (strTape_startInvariant x) rfl (strTape_startInvariant x).1
    B Hb G W (by rw [hBdef]; exact one_le_bB _ _) (by rw [hHbdef]; exact one_le_bHb _ _ _)
    (by rw [hHbdef, hHdef]; exact bHb_lt_bH _ _ _)
    (fun v hv => (hbounds v hv).1) (fun v hv => (hbounds v hv).2.1)
    (fun v hv => (hbounds v hv).2.2.1) (fun v hv => (hbounds v hv).2.2.2.1)
    (by rw [hGdef]; exact one_le_bG _ _ _) (by rw [hGdef, hBdef]; exact bB_le_bG _ _ _)
    (by rw [hGdef, hHbdef]; exact bHb_le_bG _ _ _)
    (fun v hv => (hbounds v hv).2.2.2.2)
    (by rw [hGdef, hWdef]; exact bW_stage1 _ _ _ _ _ _)
    (fun v hv => by
      rw [hGdef, hWdef]
      exact bW_stage2 _ _ _ _ _ _ x (dropTop (v + 1)) rfl (hlenw v hv))
    (by rw [hGdef, hWdef, hBdef]; exact bW_stage3 _ _ _ _ _ _)
    (fun v hv => by
      rw [hGdef, hWdef]
      exact bW_stage4 _ _ _ _ _ _ _ (hpairle v hv))
    (by rw [hGdef, hWdef, hHbdef]; exact bW_stage6 _ _ _ _ _ _)
    (fun v hv => by
      rw [hGdef, hWdef]
      refine bW_stage8 _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      · exact binarySuccTime_le' _ _ N hNdef
          (le_trans (tally_le _ v) (by omega))
      · exact binarySuccTime_le' _ _ N hNdef
          (le_trans (tally_le _ v) (by omega))
      · exact binarySuccTime_le' _ _ N hNdef (by omega))
    (fun v hv => by
      rw [hGdef, hWdef]
      exact bW_stage9 _ _ _ _ _ _ _ (binaryBumpTime_le' _ v N hNdef (by omega)))
    (by
      rw [hGdef, hWdef, hHdef]
      exact bW_stage10 _ _ _ _ _ _ _ rfl)
    (fun v hv => by
      rw [hGdef, hWdef, hBdef]
      exact bW_test _ _ _ _ _ _ N v (binaryEqTime_le' _ v N hNdef (by omega)))
  have hloopC := enumLoop_hoareTime M hdec hdecS x N H hN (strTape x)
    (strTape_parked x) (strTape_startInvariant x) rfl (strTape_startInvariant x).1
    B Hb bBody bTest (by rw [hBdef]; exact one_le_bB _ _)
    (by rw [hHbdef]; exact one_le_bHb _ _ _)
    (fun v hv => (hbounds v hv).1) (fun v hv => (hbounds v hv).2.1)
    (by rw [hHbdef, hHdef]; exact bHb_lt_bH _ _ _)
    (fun v hv => (hbounds v hv).2.2.1) hbBody
    (fun v hv => (hbounds v hv).2.2.2.1) hbTest
  refine enumTM_keepsWindowOn M p (bHPoly p s) x N H
    (NTM.tally (enumP L' x) N) (NTM.tally (fun u => !enumP L' x u) N) W
    (fun c hc c' hreach => by
      obtain ⟨hst, hpre⟩ := hc
      refine hloopW c.input c.work c.output hpre c' ?_
      have hce : (⟨((bodyTM M).loopTM
          (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).qstart,
          c.input, c.work, c.output⟩ : Cfg _ _) = c := by
        cases c; subst hst; rfl
      rw [hce]
      exact hreach)
    (hloopC.strengthen_post (fun inp work out h => ⟨h.1, h.2.1, by rw [h.2.2, ite_eq_left rfl]⟩))
    (by
      have := prologueTM_hoareTime k p (bHPoly p s) x
      rw [← hNdef, show (bHPoly p s).eval x.length = H from by rw [hHdef, bHPoly_eval]] at this
      exact this)
    B (by rw [hBdef, bB]; omega)
    (by rw [hWdef]; exact one_le_bW _ _ _ _ _ _)
    (by rw [hWdef]; exact bW_copy _ _ _ _ _ _)
    (by rw [hWdef, hBdef]; exact bW_rewind _ _ _ _ _ _)
    (by
      rw [hWdef]
      exact le_trans (by
        have := prologueTime_le p (bHPoly p s) x.length
        omega) (bW_prologue _ _ _ _ _ _))
    (by
      rw [hWdef]
      refine bW_epilogue _ _ _ _ _ _ _ ?_
      rw [epiPoly_eval]
      exact epilogueTime_le (p.eval x.length) _ N hNdef (le_trans (tally_le _ N) (le_refl N)))

/-- **The two loop budgets exist.** Both are finite suprema over the counter range — they need
not be polynomial, since the loop's *time* never enters the space accounting. -/
theorem exists_loop_bounds (M : TM k) (f : ℕ → ℕ) (x : List Bool) (L' : Language)
    (N H B Hb : ℕ) :
    ∃ bBody bTest : ℕ,
      (∀ v, v < N → bodyTime k x (TM.spaceTimeBound M f) H Hb B v
        (NTM.tally (enumP L' x) v) (NTM.tally (fun u => !enumP L' x u) v) ≤ bBody) ∧
      (∀ v, v < N → testTime B N v ≤ bTest) :=
  ⟨(Finset.range N).sup (fun v => bodyTime k x (TM.spaceTimeBound M f) H Hb B v
      (NTM.tally (enumP L' x) v) (NTM.tally (fun u => !enumP L' x u) v)),
    (Finset.range N).sup (fun v => testTime B N v),
    fun _ hv => Finset.le_sup (f := fun v => bodyTime k x (TM.spaceTimeBound M f) H Hb B v
      (NTM.tally (enumP L' x) v) (NTM.tally (fun u => !enumP L' x u) v))
      (Finset.mem_range.mpr hv),
    fun _ hv => Finset.le_sup (f := fun v => testTime B N v) (Finset.mem_range.mpr hv)⟩

end PolyExists

end Complexity

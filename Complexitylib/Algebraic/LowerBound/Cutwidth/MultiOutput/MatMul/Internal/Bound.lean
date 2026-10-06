/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Internal.Component
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian

/-!
# The size bounds for matrix multiplication

* **The finite bound** (`sq_sub_le_of_charges`). Suppose every split has total charge at most
  three times its crossing signals plus `3 L`. Along the ranking of `MultiOutput.exists_rank`,
  the threshold prefix of `Tripartite.exists_threshold` ends at a terminal and satisfies
  `3 n² ≤ 2 (R_I + R_J + R_K) + 3` (`Tripartite.three_mul_sq_le_two_mul_charge`), so it is
  crossed by at least `(n² - 2 L - 1)/2` signals. It is charged to the component holding all
  terminals (`mem_component_of_trace`), which has `2 n²` inputs and at most `s` gates. With a
  totally regular matrix `L = 0` (`half_sq_le_of_totallyRegular`); over every finite field
  `L = 4 n` (`sq_sub_le`).
* **The asymptotic bound** (`eventually_lt_size_of_orderingBound_matMul`). Assume at most
  `(2 + 1/(2A) - ε) n²` gates and choose `η = A² ε`; the cycle term is then at most
  `(1/2 - A ε/2) n²`, while the loss `4 n` and the logarithmic term are `o(n²)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.Internal

open Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Tripartite Filter

variable {σ : Signature} {n s : Nat}

/-! ## The finite bound -/

section Finite

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The finite bound from the charges.** If every split of a fan-in-two program whose wires
`out` carry `matMul n` has total charge at most three times its crossing signals plus `3 L`,
then `(n² - 2 L - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem sq_sub_le_of_charges {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (p : Program σ (n * n + n * n) s)
    (hp : p.FanInAtMost 2) (I : Interpretation σ F) (out : Fin (n * n) → Wire (n * n + n * n) s)
    (hf : ∀ z o, p.trace I z (out o) = matMul n z o) (L : Nat)
    (hcharge : ∀ S : Finset (Wire (n * n + n * n) s),
      chargeI (place (matMulTermA n s) S) (place (matMulTermC out) S) +
          chargeJ (place (matMulTermA n s) S) (place (matMulTermB n s) S) +
          chargeK (place (matMulTermB n s) S) (place (matMulTermC out) S) ≤
        3 * ((forward p S).card + (backward p S).card) + 3 * L) :
    ((n : ℝ) ^ 2 - 2 * L - 1) / 2 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 (2 * (n : ℝ) ^ 2 + 3 * s) := by
    rcases Nat.eq_zero_or_pos (2 * n ^ 2 + 3 * s) with h | h
    · have : (2 * (n : ℝ) ^ 2 + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 := mul_nonneg hAη (le_max_right _ _)
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have h0 : (n : ℝ) ^ 2 = 0 := by
      rw [hn]
      norm_num
    have hneg : ((n : ℝ) ^ 2 - 2 * L - 1) / 2 < 0 := by
      rw [h0]
      linarith
    exact hneg.le.trans (add_nonneg (add_nonneg hmax0 (by linarith)) hC)
  -- All terminals lie in one component, on distinct wires.
  obtain ⟨hin, houtW⟩ := mem_component_of_trace hn hf
  set W₀ := component p (out (matMulOutput n ⟨0, hn⟩ ⟨0, hn⟩)) with hW₀
  have hterm := terminal_injective hf
  -- The ranking and the threshold prefix.
  obtain ⟨rank, hrank, hlt, hbound⟩ := exists_rank hAη order p hp
  obtain ⟨t, ⟨x, hx⟩, hlo, hhi⟩ :=
    exists_threshold hn (matMulTermA n s) (matMulTermB n s) (matMulTermC out) hterm rank hrank _ hlt
  set S := prefixBelow rank (t + 1) with hS
  set w₀ := Sum.elim (matMulTermA n s) (Sum.elim (matMulTermB n s) (matMulTermC out)) x with hw₀def
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
  have hsq := three_mul_sq_le_two_mul_charge _ _ _ hlo hhi
  have hch := hcharge S
  have hlower : n ^ 2 ≤ 2 * ((forward p S).card + (backward p S).card) + 2 * L + 1 := by
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
  have hlowerR : ((n : ℝ) ^ 2 - 2 * L - 1) / 2 ≤
      (((forward p S).card + (backward p S).card : Nat) : ℝ) := by
    have : ((n ^ 2 : Nat) : ℝ) ≤
        ((2 * ((forward p S).card + (backward p S).card) + 2 * L + 1 : Nat) : ℝ) := by
      exact_mod_cast hlower
    push_cast at this ⊢
    linarith
  linarith

/-- **The finite bound with a totally regular matrix.** A fan-in-two program over a finite field
with a totally regular `n × n` matrix, whose wires `out` carry `matMul n`, has
`(n² - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem half_sq_le_of_totallyRegular {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {M : Matrix (Fin n) (Fin n) F}
    (hM : TotallyRegular M) (p : Program σ (n * n + n * n) s) (hp : p.FanInAtMost 2)
    (I : Interpretation σ F) (out : Fin (n * n) → Wire (n * n + n * n) s)
    (hf : ∀ z o, p.trace I z (out o) = matMul n z o) :
    ((n : ℝ) ^ 2 - 1) / 2 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  have h := sq_sub_le_of_charges hAη order p hp I out hf 0 fun S => by
    obtain ⟨h₁, h₂, h₃⟩ := charges_le_of_totallyRegular hf hM S
    omega
  simpa using h

/-- **The finite bound over every finite field.** A fan-in-two program over any finite field
whose wires `out` carry `matMul n` has
`(n² - 8 n - 1)/2 ≤ (A + η) (s - 2 n²)⁺ + 3 log₂ (2 n² + 3 s) + C`. -/
theorem sq_sub_le {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    (p : Program σ (n * n + n * n) s) (hp : p.FanInAtMost 2) (I : Interpretation σ F)
    (out : Fin (n * n) → Wire (n * n + n * n) s)
    (hf : ∀ z o, p.trace I z (out o) = matMul n z o) :
    ((n : ℝ) ^ 2 - 8 * n - 1) / 2 ≤
      (A + η) * max ((s : ℝ) - 2 * n ^ 2) 0 + 3 * Real.logb 2 (2 * n ^ 2 + 3 * s) + C := by
  have h := sq_sub_le_of_charges hAη order p hp I out hf (4 * n) fun S => by
    obtain ⟨h₁, h₂, h₃⟩ := charges_le_add hf S
    omega
  push_cast at h
  linarith

end Finite

/-! ## Asymptotics -/

universe u v

/-- **The asymptotic bound for matrix multiplication** with a general ordering coefficient. -/
theorem eventually_lt_size_of_orderingBound_matMul {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] (σ : Signature.{v})
      (I : Interpretation σ F) (c : Circuit σ (n * n + n * n) (n * n)),
        c.FanInAtMost 2 → c.Computes I (matMul n) → (2 + 1 / (2 * A) - ε) * n ^ 2 < c.size := by
  set ε' := min ε (1 / (2 * A)) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 1 / (2 * A) := min_le_right _ _
  set η := A ^ 2 * ε' with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  set B : ℝ := 8 + 3 / (2 * A) with hB
  have hBpos : 0 < B := by positivity
  have hδ : 0 < A * ε' / 2 := by positivity
  filter_upwards [eventually_mul_logb_add_lt 6 (3 * Real.logb 2 B + C + 1) one_pos,
    eventually_ge_atTop 1, eventually_ge_atTop ⌈10 / (A * ε')⌉₊] with n hlog hn1 hnbig
  intro F _ _ σ I c hfan hc
  classical
  by_contra hs
  rw [not_lt] at hs
  have hs' : (c.size : ℝ) ≤ (2 + 1 / (2 * A) - ε') * n ^ 2 :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have core := sq_sub_le hAη hC c.program hfan I c.outputs fun z o => congrFun (hc z) o
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnbig' : 10 / (A * ε') ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnbig)
  -- The cycle-rank term.
  have hrest : 0 ≤ (1 / (2 * A) - ε') * n ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((c.size : ℝ) - 2 * n ^ 2) 0 ≤ (1 / (2 * A) - ε') * n ^ 2 :=
    max_le (by linarith) hrest
  have hcoef : (A + η) * (1 / (2 * A) - ε') ≤ 1 / 2 - A * ε' / 2 := by
    have h₁ : (A + η) * (1 / (2 * A) - ε') = 1 / 2 - A * ε' + η / (2 * A) - η * ε' := by
      field_simp
      ring
    have h₂ : η / (2 * A) = A * ε' / 2 := by
      rw [hη]
      field_simp
    have h₃ : 0 ≤ η * ε' := by positivity
    linarith
  have hprod : (A + η) * max ((c.size : ℝ) - 2 * n ^ 2) 0 ≤ (1 / 2 - A * ε' / 2) * n ^ 2 := by
    calc (A + η) * max ((c.size : ℝ) - 2 * n ^ 2) 0 ≤ (A + η) * ((1 / (2 * A) - ε') * n ^ 2) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (1 / (2 * A) - ε') * n ^ 2 := by ring
      _ ≤ (1 / 2 - A * ε' / 2) * n ^ 2 := mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- The logarithmic term.
  have hVle : 2 * (n : ℝ) ^ 2 + 3 * c.size ≤ B * n ^ 2 := by
    have h₁ : (2 + 1 / (2 * A) - ε') * (n : ℝ) ^ 2 ≤ (2 + 1 / (2 * A)) * n ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (n : ℝ) ^ 2 = 2 * n ^ 2 + 3 * ((2 + 1 / (2 * A)) * n ^ 2) := by
      rw [hB]
      ring
    linarith
  have hVpos : (0 : ℝ) < 2 * n ^ 2 + 3 * c.size := by positivity
  have hlogV : Real.logb 2 (2 * (n : ℝ) ^ 2 + 3 * c.size) ≤ Real.logb 2 B + 2 * Real.logb 2 n := by
    calc Real.logb 2 (2 * (n : ℝ) ^ 2 + 3 * c.size) ≤ Real.logb 2 (B * n ^ 2) :=
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

end Algebraic.Cutwidth.MultiOutput.MatMul.Internal

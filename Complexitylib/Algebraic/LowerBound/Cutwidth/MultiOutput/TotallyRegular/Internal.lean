/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Rank
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Field.ZMod

/-!
# Proofs for totally regular linear maps

* Every block of a totally regular matrix has rank at least the smaller of its dimensions
  (`min_card_le_blockRank`): it contains a nonsingular square block of that size.
* A circuit computing a totally regular map has distinct output wires (`outputs_injective`):
  two outputs on one wire would give two equal rows, hence a singular `2 × 2` block.
* All inputs and outputs lie in one component of the wire graph: the component of an output is
  closed, so it is crossed by no signal, and the rank-cut bound forces every input and every
  output into it.
* Along the ranking of `MultiOutput.exists_rank`, the number of inputs and outputs in a prefix
  grows by at most two per wire, so some prefix ending at an input or output holds `N` or
  `N + 1` of them. For that prefix the two blocks have ranks summing to at least `N - 1`, and
  the prefix is charged to the component holding all inputs, which gives
  `N - 1 ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C` (`sub_one_le_of_totallyRegular`).
* For a rectangular `m × N` totally regular matrix with `2 ≤ N ≤ m`, the `m` output wires are
  still distinct (`outputs_injective_rect`), so peeling the last gate and at most one output
  wire seated on it `m - N` times leaves a program with `s - (m - N)` gates computing an `N × N`
  totally regular row-submatrix (`exists_square_of_totallyRegular_rect`). This gives the
  rectangular finite bound `N - 1 ≤ (A + η) (s - m)⁺ + 3 log₂ (N + 3 s) + C`
  (`sub_one_le_of_totallyRegular_rect`) and the asymptotic lower bound
  `m + (1 / A - ε) N < s` (`eventually_lt_size_of_orderingBound_rect`).
* Cauchy matrices are totally regular (`totallyRegular_cauchy`): a kernel vector `v` of a square
  Cauchy matrix makes the interpolant through `(y j, v j / w j)`, with `w` the barycentric
  weights, vanish at every `x i`; it has degree below the number of nodes, so it is zero, and
  then `v = 0`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut Matrix Filter

variable {σ : Signature} {F : Type*} [Field F]

/-! ## Blocks of totally regular matrices -/

/-- Every block of a totally regular matrix has rank at least the smaller of its dimensions. -/
theorem min_card_le_blockRank {m n : Nat} {M : Matrix (Fin m) (Fin n) F} (hM : TotallyRegular M)
    (Y : Finset (Fin m)) (X : Finset (Fin n)) : min Y.card X.card ≤ blockRank M Y X := by
  set k := min Y.card X.card
  let r : Fin k → ↥Y := fun i => Y.equivFin.symm (Fin.castLE (min_le_left _ _) i)
  let c : Fin k → ↥X := fun i => X.equivFin.symm (Fin.castLE (min_le_right _ _) i)
  have hr : Function.Injective r :=
    Y.equivFin.symm.injective.comp (Fin.castLE_injective _)
  have hc : Function.Injective c :=
    X.equivFin.symm.injective.comp (Fin.castLE_injective _)
  have hdet : ((M.submatrix (fun i : ↥Y => (i : Fin m)) (fun j : ↥X => (j : Fin n))).submatrix
      r c).det ≠ 0 := by
    rw [Matrix.submatrix_submatrix]
    exact hM k _ _ (Subtype.val_injective.comp hr) (Subtype.val_injective.comp hc)
  have hrank := Matrix.rank_of_det_ne_zero hdet
  rw [Fintype.card_fin] at hrank
  rw [← hrank]
  exact Matrix.rank_submatrix_le _ _ _

/-- A circuit computing a totally regular square map carries distinct outputs on distinct
wires. -/
theorem outputs_injective {n s N : Nat} {M : Matrix (Fin N) (Fin N) F}
    (hM : TotallyRegular M) (p : Program σ n s) (I : Interpretation σ F)
    (out : Fin N → Wire n s) {f : (Fin n → F) → Fin N → F}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (hfM : ∀ i i', (∀ x, f x i = f x i') →
      ∀ j, M i j = M i' j) :
    Function.Injective out := by
  intro i i' h
  by_contra hne
  have hrow : ∀ j, M i j = M i' j := hfM i i' fun x => by rw [← hf, ← hf, h]
  have hrinj : Function.Injective ![i, i'] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hdet := hM 2 ![i, i'] ![i, i'] hrinj hrinj
  apply hdet
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hrow i, hrow i']
  ring

/-- Any injective selection of rows of a totally regular matrix is totally regular. -/
theorem TotallyRegular.submatrix_rows {m m' n : Nat} {M : Matrix (Fin m) (Fin n) F}
    (hM : TotallyRegular M) {r : Fin m' → Fin m} (hr : Function.Injective r) :
    TotallyRegular (M.submatrix r id) := by
  intro k r' c' hr' hc'
  rw [Matrix.submatrix_submatrix]
  exact hM k (r ∘ r') c' (hr.comp hr') hc'

/-- A circuit computing a totally regular map on `N ≥ 2` inputs carries distinct outputs on
distinct wires. -/
theorem outputs_injective_rect {m N s : Nat} (hN : 2 ≤ N) {M : Matrix (Fin m) (Fin N) F}
    (hM : TotallyRegular M) (p : Program σ N s) (I : Interpretation σ F)
    (out : Fin m → Wire N s) (hf : ∀ x i, p.trace I x (out i) = (M *ᵥ x) i) :
    Function.Injective out := by
  intro i i' h
  by_contra hne
  have hrow : ∀ j, M i j = M i' j := fun j => by
    have h₁ := hf (Pi.single j 1) i
    have h₂ := hf (Pi.single j 1) i'
    rw [h] at h₁
    simpa [Matrix.mulVec_single_one] using h₁.symm.trans h₂
  have hrinj : Function.Injective ![i, i'] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  let c : Fin 2 → Fin N := ![⟨0, by omega⟩, ⟨1, by omega⟩]
  have hcinj : Function.Injective c := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [c, Fin.ext_iff]
  have hdet := hM 2 ![i, i'] c hrinj hcinj
  apply hdet
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hrow (c 0), hrow (c 1)]
  ring

/-- Every wire of `p.gate line` other than the last gate comes from `p`. -/
def unlast {n s : Nat} (w : Wire n (s + 1)) (hw : w ≠ Wire.gate (Fin.last s)) : Wire n s :=
  Wire.lastCases (motive := fun w => w ≠ Wire.gate (Fin.last s) → Wire n s)
    (fun h => absurd rfl h) (fun w₀ _ => w₀) w hw

/-- `unlast` inverts `Wire.castSucc`. -/
@[simp] theorem castSucc_unlast {n s : Nat} (w : Wire n (s + 1))
    (hw : w ≠ Wire.gate (Fin.last s)) : (unlast w hw).castSucc = w := by
  induction w using Wire.lastCases with
  | last => exact absurd rfl hw
  | castSucc w₀ => simp [unlast]

/-- A wire of `p.gate line` other than the last gate carries the same value in `p`. -/
theorem trace_unlast {n s : Nat} {U : Type*} (p : Program σ n s) (line : Line σ n s)
    (I : Interpretation σ U) (x : Fin n → U) (w : Wire n (s + 1))
    (hw : w ≠ Wire.gate (Fin.last s)) :
    p.trace I x (unlast w hw) = (p.gate line).trace I x w := by
  rw [← p.trace_gate_castSucc line I x (unlast w hw), castSucc_unlast]

/-- Peeling `m - N` gates from a program computing a rectangular `m × N` totally regular map
leaves a program with `s - (m - N)` gates computing an `N × N` totally regular submatrix. -/
theorem exists_square_of_totallyRegular_rect {N m s : Nat} (hN : 2 ≤ N) (hNm : N ≤ m)
    (p : Program σ N s) (hp : p.FanInAtMost 2) (I : Interpretation σ F)
    (out : Fin m → Wire N s) {M : Matrix (Fin m) (Fin N) F} (hM : TotallyRegular M)
    (hf : ∀ x i, p.trace I x (out i) = (M *ᵥ x) i) :
    ∃ (s' : Nat) (p' : Program σ N s') (out' : Fin N → Wire N s')
      (M' : Matrix (Fin N) (Fin N) F),
      s' + (m - N) = s ∧ p'.FanInAtMost 2 ∧ TotallyRegular M' ∧
        ∀ x i, p'.trace I x (out' i) = (M' *ᵥ x) i := by
  induction m generalizing s with
  | zero => omega
  | succ m ih =>
    by_cases hEq : N = m + 1
    · subst hEq
      exact ⟨s, p, out, M, by omega, hp, hM, hf⟩
    · have hNm' : N ≤ m := by omega
      have hout := outputs_injective_rect hN hM p I out hf
      cases p with
      | empty =>
        have hcard := Fintype.card_le_of_injective out hout
        simp only [Fintype.card_fin, Wire.card, add_zero] at hcard
        omega
      | @gate s₀ p₀ line =>
        classical
        obtain ⟨i₀, hne⟩ : ∃ i₀ : Fin (m + 1),
            ∀ i : Fin m, out (i₀.succAbove i) ≠ Wire.gate (Fin.last s₀) := by
          by_cases hlast : ∃ i₀ : Fin (m + 1), out i₀ = Wire.gate (Fin.last s₀)
          · obtain ⟨i₀, hi₀⟩ := hlast
            exact ⟨i₀, fun i h => Fin.succAbove_ne i₀ i (hout (h.trans hi₀.symm))⟩
          · push Not at hlast
            exact ⟨0, fun i => hlast _⟩
        let out₀ : Fin m → Wire N s₀ := fun i => unlast (out (i₀.succAbove i)) (hne i)
        let M₀ : Matrix (Fin m) (Fin N) F := M.submatrix i₀.succAbove id
        have hM₀ : TotallyRegular M₀ :=
          TotallyRegular.submatrix_rows hM (Fin.succAbove_right_injective)
        have hf₀ : ∀ x i, p₀.trace I x (out₀ i) = (M₀ *ᵥ x) i := fun x i => by
          change p₀.trace I x (unlast (out (i₀.succAbove i)) (hne i)) = _
          rw [trace_unlast, hf]
          rfl
        obtain ⟨s', p', out', M', hs', hp', hM', hf'⟩ := ih hNm' p₀ hp.1 out₀ hM₀ hf₀
        exact ⟨s', p', out', M', by omega, hp', hM', hf'⟩

/-! ## A discrete intermediate value step -/

/-- A function from `0` that reaches `h ≥ 1` crosses `h` at some step. -/
theorem exists_cross (g : Nat → Nat) (hzero : g 0 = 0) {h : Nat} (hh : 1 ≤ h) (T : Nat)
    (hT : h ≤ g T) : ∃ t, g t < h ∧ h ≤ g (t + 1) := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases hlt : h ≤ g T
    · exact ih hlt
    · exact ⟨T, by omega, hT⟩

/-! ## The finite bound -/

theorem card_inputsIn_prefixBelow_succ_le {n s : Nat} (rank : Wire n s → Nat)
    (hrank : Function.Injective rank) (t : Nat) :
    (inputsIn (prefixBelow rank (t + 1))).card ≤ (inputsIn (prefixBelow rank t)).card + 1 := by
  have hsub : inputsIn (prefixBelow rank (t + 1)) ⊆
      inputsIn (prefixBelow rank t) ∪ Finset.univ.filter fun j => rank (Wire.input j) = t := by
    intro j hj
    simp only [mem_inputsIn, prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_union, mem_inputsIn, prefixBelow, Finset.mem_filter, Finset.mem_univ,
      true_and]
    omega
  have hone : (Finset.univ.filter fun j : Fin n => rank (Wire.input j) = t).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hab := hrank (ha.trans hb.symm)
    injection hab
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left hone _))

theorem card_outputsIn_prefixBelow_succ_le {n s m : Nat} (rank : Wire n s → Nat)
    (hrank : Function.Injective rank) (out : Fin m → Wire n s) (hout : Function.Injective out)
    (t : Nat) :
    (outputsIn out (prefixBelow rank (t + 1))).card ≤
      (outputsIn out (prefixBelow rank t)).card + 1 := by
  have hsub : outputsIn out (prefixBelow rank (t + 1)) ⊆
      outputsIn out (prefixBelow rank t) ∪ Finset.univ.filter fun i => rank (out i) = t := by
    intro i hi
    simp only [outputsIn, prefixBelow, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_union, outputsIn, prefixBelow, Finset.mem_filter, Finset.mem_univ,
      true_and]
    omega
  have hone : (Finset.univ.filter fun i : Fin m => rank (out i) = t).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hout (hrank (ha.trans hb.symm))
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left hone _))

/-- The layout bound needs only distinct output wires and the rank inequality at each cut.
No finiteness assumption on the coefficient field enters this graph argument. -/
theorem sub_one_le_of_rank_cuts {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {N s : Nat} (p : Program σ N s)
    (hp : p.FanInAtMost 2) (out : Fin N → Wire N s)
    {M : Matrix (Fin N) (Fin N) F} (hM : TotallyRegular M)
    (hout : Function.Injective out)
    (cuts : ∀ S : Finset (Wire N s),
      blockRank M (outputsIn out S)ᶜ (inputsIn S) +
        blockRank M (outputsIn out S) (inputsIn S)ᶜ ≤
          (forward p S).card + (backward p S).card) :
    (N : ℝ) - 1 ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C := by
  have hC := orderingBound_nonneg order
  have hlog : 0 ≤ Real.logb 2 ((N : ℝ) + 3 * s) := by
    rcases Nat.eq_zero_or_pos (N + 3 * s) with h | h
    · have : ((N : ℝ) + 3 * s) = 0 := by exact_mod_cast h
      rw [this, Real.logb_zero]
    · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
  have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - N) 0 := mul_nonneg hAη (le_max_right _ _)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero] at hmax0 hlog ⊢
    linarith
  -- All inputs and outputs lie in the component of the first output.
  set i₀ : Fin N := ⟨0, hN⟩
  set W₀ := component p (out i₀) with hW₀
  have hclosed := component_closed p (out i₀)
  have hzero := cuts W₀
  rw [forward_eq_empty_of_closed hclosed, backward_eq_empty_of_closed hclosed] at hzero
  simp only [Finset.card_empty, add_zero, Nat.le_zero, Nat.add_eq_zero_iff] at hzero
  have hY : i₀ ∈ outputsIn out W₀ := by
    simp [outputsIn, hW₀, mem_component_self]
  have hX : (inputsIn W₀)ᶜ.card = 0 := by
    have := min_card_le_blockRank hM (outputsIn out W₀) (inputsIn W₀)ᶜ
    rw [hzero.2] at this
    have hpos : 0 < (outputsIn out W₀).card := Finset.card_pos.mpr ⟨i₀, hY⟩
    omega
  have hXcard : (inputsIn W₀).card = N := by
    have := Finset.card_compl (inputsIn W₀)
    rw [Fintype.card_fin] at this
    have hle : (inputsIn W₀).card ≤ N := by simpa using Finset.card_le_univ (inputsIn W₀)
    omega
  have hYc : (outputsIn out W₀)ᶜ.card = 0 := by
    have := min_card_le_blockRank hM (outputsIn out W₀)ᶜ (inputsIn W₀)
    rw [hzero.1, hXcard] at this
    omega
  have hin : ∀ j, Wire.input j ∈ W₀ := by
    intro j
    by_contra hj
    have : j ∈ (inputsIn W₀)ᶜ := Finset.mem_compl.mpr fun h => hj (mem_inputsIn.mp h)
    rw [Finset.card_eq_zero.mp hX] at this
    exact Finset.notMem_empty _ this
  have houtW : ∀ i, out i ∈ W₀ := by
    intro i
    by_contra hi
    have : i ∈ (outputsIn out W₀)ᶜ := Finset.mem_compl.mpr fun h => hi (by
      simpa [outputsIn] using h)
    rw [Finset.card_eq_zero.mp hYc] at this
    exact Finset.notMem_empty _ this
  -- The ranking and the prefix holding about `N` inputs and outputs.
  obtain ⟨rank, hrank, hlt, hbound⟩ := exists_rank hAη order p hp
  let τ : Nat → Nat := fun t =>
    (inputsIn (prefixBelow rank t)).card + (outputsIn out (prefixBelow rank t)).card
  have hτ0 : τ 0 = 0 := by
    simp [τ, inputsIn, outputsIn, prefixBelow]
  have hτstep : ∀ t, τ (t + 1) ≤ τ t + 2 := fun t => by
    have h₁ := card_inputsIn_prefixBelow_succ_le rank hrank t
    have h₂ := card_outputsIn_prefixBelow_succ_le rank hrank out hout t
    simp only [τ]
    omega
  have hτT : 2 * N ≤ τ (N + s) := by
    have hall : prefixBelow rank (N + s) = Finset.univ := by
      ext w
      simp [prefixBelow, hlt w]
    simp [τ, hall, inputsIn, outputsIn]
    omega
  obtain ⟨t, hτt, hτt1⟩ := exists_cross τ hτ0 (h := N) hN (N + s) (by omega)
  have hτup : (inputsIn (prefixBelow rank (t + 1))).card +
      (outputsIn out (prefixBelow rank (t + 1))).card ≤ N + 1 := by
    have := hτstep t
    simp only [τ] at this hτt
    omega
  have hτlow : N ≤ (inputsIn (prefixBelow rank (t + 1))).card +
      (outputsIn out (prefixBelow rank (t + 1))).card := hτt1
  -- A terminal is ranked `t`.
  obtain ⟨w, hwt, hwW⟩ : ∃ w, rank w = t ∧ w ∈ W₀ := by
    by_contra hnone
    push Not at hnone
    have heq : prefixBelow rank (t + 1) = prefixBelow rank t ∪
        Finset.univ.filter fun v => rank v = t := by
      ext v
      simp only [prefixBelow, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hi : inputsIn (prefixBelow rank (t + 1)) = inputsIn (prefixBelow rank t) := by
      ext j
      simp only [mem_inputsIn, heq, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, or_iff_left_iff_imp]
      intro hj
      exact absurd (hin j) (hnone _ hj)
    have ho : outputsIn out (prefixBelow rank (t + 1)) = outputsIn out (prefixBelow rank t) := by
      ext i
      simp only [outputsIn, heq, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        or_iff_left_iff_imp]
      intro hi
      exact absurd (houtW i) (hnone _ hi)
    have : τ (t + 1) = τ t := by simp only [τ, hi, ho]
    omega
  have hprefix : prefixBelow rank (t + 1) = prefixUpTo rank w := by
    ext v
    simp only [prefixBelow, prefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcomp : component p w = W₀ := component_eq_of_mem hwW
  -- The rank lower bound at the prefix.
  set S := prefixBelow rank (t + 1) with hS
  have hcut := cuts S
  have hmin₁ := min_card_le_blockRank hM (outputsIn out S)ᶜ (inputsIn S)
  have hmin₂ := min_card_le_blockRank hM (outputsIn out S) (inputsIn S)ᶜ
  have hYcS : (outputsIn out S)ᶜ.card = N - (outputsIn out S).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hXcS : (inputsIn S)ᶜ.card = N - (inputsIn S).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hXle : (inputsIn S).card ≤ N := by simpa using Finset.card_le_univ (inputsIn S)
  have hYle : (outputsIn out S).card ≤ N := by simpa using Finset.card_le_univ (outputsIn out S)
  have hlower : N - 1 ≤ (forward p S).card + (backward p S).card := by
    rw [hYcS] at hmin₁
    rw [hXcS] at hmin₂
    omega
  -- The ordering bound at the prefix.
  have hupper := hbound w
  rw [← hprefix, hcomp, hXcard] at hupper
  have hgates : ((gatesIn W₀).card : ℝ) ≤ s := by
    exact_mod_cast (by simpa using Finset.card_le_univ (gatesIn W₀))
  have hmax : (A + η) * max (((gatesIn W₀).card : ℝ) - N) 0 ≤ (A + η) * max ((s : ℝ) - N) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hAη
  have hlowerR : (N : ℝ) - 1 ≤ (((forward p S).card + (backward p S).card : Nat) : ℝ) := by
    have : ((N - 1 : Nat) : ℝ) ≤ (((forward p S).card + (backward p S).card : Nat) : ℝ) := by
      exact_mod_cast hlower
    rw [Nat.cast_sub hN] at this
    simpa using this
  linarith

/-- **The finite bound for totally regular maps.** A fan-in-two program over any signature
whose wires `out` carry a totally regular linear map on `N` inputs has
`N - 1 ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C`. -/
theorem sub_one_le_of_totallyRegular [Fintype F] [DecidableEq F] {A η C : ℝ}
    (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C) {N s : Nat}
    (p : Program σ N s) (hp : p.FanInAtMost 2) (I : Interpretation σ F)
    (out : Fin N → Wire N s) {M : Matrix (Fin N) (Fin N) F} (hM : TotallyRegular M)
    (hf : ∀ x i, p.trace I x (out i) = (M *ᵥ x) i) :
    (N : ℝ) - 1 ≤ (A + η) * max ((s : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * s) + C := by
  have hout : Function.Injective out := by
    refine outputs_injective hM p I out hf fun i i' hii' j => ?_
    have := hii' (Pi.single j 1)
    simpa [Matrix.mulVec_single_one] using this
  exact sub_one_le_of_rank_cuts hAη order p hp out hM hout
    (blockRank_add_blockRank_le_of_trace p I out M hf)

/-- **The finite bound for rectangular totally regular maps.** A fan-in-two program over any
signature whose wires `out` carry an `m × N` totally regular linear map with `N ≤ m` has
`N - 1 ≤ (A + η) (s - m)⁺ + 3 log₂ (N + 3 s) + C`. -/
theorem sub_one_le_of_totallyRegular_rect [Fintype F] [DecidableEq F] {A η C : ℝ}
    (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C) {N m s : Nat} (hNm : N ≤ m)
    (p : Program σ N s) (hp : p.FanInAtMost 2) (I : Interpretation σ F)
    (out : Fin m → Wire N s) {M : Matrix (Fin m) (Fin N) F} (hM : TotallyRegular M)
    (hf : ∀ x i, p.trace I x (out i) = (M *ᵥ x) i) :
    (N : ℝ) - 1 ≤ (A + η) * max ((s : ℝ) - m) 0 + 3 * Real.logb 2 (N + 3 * s) + C := by
  by_cases hN : 2 ≤ N
  · obtain ⟨s', p', out', M', hs', hp', hM', hf'⟩ :=
      exists_square_of_totallyRegular_rect hN hNm p hp I out hM hf
    have hsq := sub_one_le_of_totallyRegular hAη order p' hp' I out' hM' hf'
    have hsum : (s' : ℝ) + m = (s : ℝ) + N := by
      exact_mod_cast (by omega : s' + m = s + N)
    have hsub : (s' : ℝ) - N = (s : ℝ) - m := by linarith
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogle : Real.logb 2 ((N : ℝ) + 3 * s') ≤ Real.logb 2 ((N : ℝ) + 3 * s) := by
      refine (Real.logb_le_logb one_lt_two (by positivity) (by positivity)).mpr ?_
      have hsle : (s' : ℝ) ≤ s := by exact_mod_cast (by omega : s' ≤ s)
      linarith
    rw [hsub] at hsq
    linarith
  · have hC := orderingBound_nonneg order
    have hlog : 0 ≤ Real.logb 2 ((N : ℝ) + 3 * s) := by
      rcases Nat.eq_zero_or_pos (N + 3 * s) with h | h
      · have : ((N : ℝ) + 3 * s) = 0 := by exact_mod_cast h
        rw [this, Real.logb_zero]
      · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)
    have hmax0 : 0 ≤ (A + η) * max ((s : ℝ) - m) 0 := mul_nonneg hAη (le_max_right _ _)
    have hN1 : (N : ℝ) ≤ 1 := by exact_mod_cast (by omega : N ≤ 1)
    linarith

/-! ## Asymptotics -/

universe u v

/-- The asymptotic layout transfer is uniform over all fields satisfying the rank-cut bound. -/
theorem eventually_lt_size_of_rank_cuts {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular M →
      ∀ (σ : Signature.{v}) (c : Circuit σ N N),
        c.FanInAtMost 2 → Function.Injective c.outputs →
        (∀ S : Finset (Wire N c.size),
          blockRank M (outputsIn c.outputs S)ᶜ (inputsIn S) +
            blockRank M (outputsIn c.outputs S) (inputsIn S)ᶜ ≤
              (forward c.program S).card + (backward c.program S).card) →
          (1 + 1 / A - ε) * N < c.size := by
  set ε' := min ε (1 / A) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'A : ε' ≤ 1 / A := min_le_right _ _
  set η := A ^ 2 * ε' / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨C, hC⟩ := order η hηpos
  have hAη : 0 ≤ A + η := by linarith
  set B : ℝ := 4 + 3 / A with hB
  have hBpos : 0 < B := by positivity
  filter_upwards [eventually_mul_logb_add_lt 3 (3 * Real.logb 2 B + C + 1)
    (show 0 < A * ε' / 2 by positivity), eventually_ge_atTop 1] with N hlog hN1
  intro F _ M hM σ c hfan hout cuts
  by_contra hs
  rw [not_lt] at hs
  have hs' : (c.size : ℝ) ≤ (1 + 1 / A - ε') * N :=
    hs.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have core := sub_one_le_of_rank_cuts hAη hC c.program hfan c.outputs hM hout cuts
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- The cycle-rank term.
  have hrest : 0 ≤ (1 / A - ε') * N := mul_nonneg (by linarith) (by positivity)
  have hmax : max ((c.size : ℝ) - N) 0 ≤ (1 / A - ε') * N :=
    max_le (by linarith) hrest
  have hcoef : (A + η) * (1 / A - ε') ≤ 1 - A * ε' / 2 := by
    have h₁ : (A + η) * (1 / A - ε') = 1 - A * ε' + η / A - η * ε' := by
      field_simp
      ring
    have h₂ : η / A = A * ε' / 2 := by
      rw [hη]
      field_simp
    have h₃ : 0 ≤ η * ε' := by positivity
    linarith
  have hprod : (A + η) * max ((c.size : ℝ) - N) 0 ≤ (1 - A * ε' / 2) * N := by
    calc (A + η) * max ((c.size : ℝ) - N) 0 ≤ (A + η) * ((1 / A - ε') * N) :=
          mul_le_mul_of_nonneg_left hmax hAη
      _ = (A + η) * (1 / A - ε') * N := by ring
      _ ≤ (1 - A * ε' / 2) * N := mul_le_mul_of_nonneg_right hcoef (by positivity)
  -- The logarithmic term.
  have hVle : (N : ℝ) + 3 * c.size ≤ B * N := by
    have h₁ : (1 + 1 / A - ε') * (N : ℝ) ≤ (1 + 1 / A) * N :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h₂ : B * (N : ℝ) = N + 3 * ((1 + 1 / A) * N) := by
      rw [hB]
      ring
    linarith
  have hVpos : (0 : ℝ) < N + 3 * c.size := by positivity
  have hlogV : Real.logb 2 ((N : ℝ) + 3 * c.size) ≤ Real.logb 2 B + Real.logb 2 N := by
    calc Real.logb 2 ((N : ℝ) + 3 * c.size) ≤ Real.logb 2 (B * N) :=
          (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVle
      _ = Real.logb 2 B + Real.logb 2 N := Real.logb_mul hBpos.ne' (by positivity)
  have hsplit : (1 - A * ε' / 2) * (N : ℝ) = N - A * ε' / 2 * N := by ring
  linarith

/-- **The asymptotic bound for totally regular maps** with a general ordering coefficient. -/
theorem eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (M : Matrix (Fin N) (Fin N) F), TotallyRegular M →
      ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N N),
        c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < c.size := by
  filter_upwards [eventually_lt_size_of_rank_cuts.{u, v} hA order hε] with N bound
  intro F _ _ _ M hM σ I c hfan hc
  have hf : ∀ x i, c.program.trace I x (c.outputs i) = (M *ᵥ x) i :=
    fun x i => congrFun (hc x) i
  apply bound F M hM σ c hfan
  · refine outputs_injective hM c.program I c.outputs hf fun i i' hii' j => ?_
    simpa [Matrix.mulVec_single_one] using hii' (Pi.single j 1)
  · exact blockRank_add_blockRank_le_of_trace c.program I c.outputs M hf

/-- **The asymptotic bound for rectangular totally regular maps** with a general ordering
coefficient. -/
theorem eventually_lt_size_of_orderingBound_rect {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ {m : Nat}, N ≤ m →
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (M : Matrix (Fin m) (Fin N) F), TotallyRegular M →
        ∀ (σ : Signature.{v}) (I : Interpretation σ F) (c : Circuit σ N m),
          c.FanInAtMost 2 → c.Computes I (fun x => M *ᵥ x) →
            (m : ℝ) + (1 / A - ε) * N < c.size := by
  filter_upwards [eventually_lt_size_of_orderingBound.{u, v} hA order hε,
    eventually_ge_atTop 2] with N bound hN2
  intro m hNm F _ _ _ M hM σ I c hfan hc
  have hf : ∀ x i, c.program.trace I x (c.outputs i) = (M *ᵥ x) i :=
    fun x i => congrFun (hc x) i
  obtain ⟨s', p', out', M', hs', hp', hM', hf'⟩ :=
    exists_square_of_totallyRegular_rect hN2 hNm c.program hfan I c.outputs hM hf
  let c' : Circuit σ N N := ⟨p', out'⟩
  have hc' : c'.Computes I (fun x => M' *ᵥ x) := fun x => funext (hf' x)
  have hlt : (1 + 1 / A - ε) * (N : ℝ) < (s' : ℝ) := bound F M' hM' σ I c' hp' hc'
  have hsum : (s' : ℝ) + m = (c.size : ℝ) + N := by
    exact_mod_cast (by omega : s' + m = c.size + N)
  linarith

/-! ## Cauchy matrices -/

/-- **Square Cauchy matrices are nonsingular.** -/
theorem det_cauchy_ne_zero {k : Nat} (x y : Fin k → F) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) : (cauchy x y).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let w : Fin k → F := fun j => (Lagrange.nodalWeight Finset.univ y j)⁻¹ * v j
  have hweight : ∀ j, Lagrange.nodalWeight Finset.univ y j ≠ 0 := fun j =>
    Lagrange.nodalWeight_ne_zero hy.injOn (Finset.mem_univ j)
  have hP : Lagrange.interpolate Finset.univ y w = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn
      (Lagrange.degree_interpolate_lt w hy.injOn) fun i _ => ?_
    rw [Lagrange.eval_interpolate_not_at_node w fun j _ => hxy i j]
    have hsum : ∑ j ∈ Finset.univ, Lagrange.nodalWeight Finset.univ y j * (x i - y j)⁻¹ * w j =
        (cauchy x y *ᵥ v) i := by
      simp only [Matrix.mulVec, dotProduct, cauchy, Matrix.of_apply, w]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hweight j]
    rw [hsum, hv, Pi.zero_apply, mul_zero]
  apply hv0
  funext j
  have := Lagrange.eval_interpolate_at_node w hy.injOn (Finset.mem_univ j)
  rw [hP, Polynomial.eval_zero] at this
  have hwj : (Lagrange.nodalWeight Finset.univ y j)⁻¹ * v j = 0 := this.symm
  rcases mul_eq_zero.mp hwj with h | h
  · exact absurd (inv_eq_zero.mp h) (hweight j)
  · simpa using h

/-- **Cauchy matrices are totally regular**: with distinct nodes `x i`, distinct nodes `y j`
and `x i ≠ y j`, every square submatrix is again a nonsingular Cauchy matrix. -/
theorem totallyRegular_cauchy {m n : Nat} (x : Fin m → F) (y : Fin n → F)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    TotallyRegular (cauchy x y) := by
  intro k r c hr hc
  have : (cauchy x y).submatrix r c = cauchy (x ∘ r) (y ∘ c) := by
    ext i j
    rfl
  rw [this]
  exact det_cauchy_ne_zero _ _ (hx.comp hr) (hy.comp hc) fun i j => hxy (r i) (c j)

/-- **The explicit Cauchy family is totally regular** over `ZMod q` for a prime `q ≥ 2 N`. -/
theorem totallyRegular_cauchyZMod (q N : Nat) [Fact q.Prime] (hq : 2 * N ≤ q) :
    TotallyRegular (cauchyZMod q N) := by
  have hx : Function.Injective fun i : Fin N => ((i : Nat) : ZMod q) := by
    intro i i' h
    have := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext this
  have hy : Function.Injective fun j : Fin N => ((N + j : Nat) : ZMod q) := by
    intro j j' h
    have := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext (by omega)
  have hxy : ∀ i j : Fin N, ((i : Nat) : ZMod q) ≠ ((N + j : Nat) : ZMod q) := by
    intro i j h
    have := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  exact totallyRegular_cauchy _ _ hx hy hxy

end Algebraic.Cutwidth.MultiOutput.Internal

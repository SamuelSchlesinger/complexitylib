/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity
public import Complexitylib.Algebraic.LowerBound.Counting.Sharp

/-!
# Minimum Circuit Size Problem (MCSP) definitions

This module defines the Minimum Circuit Size Problem (`MCSP`) as a family of Boolean
functions on truth tables of length `2 ^ n`.

* `inputEquiv n`: canonical recursive bijection `(Fin n → Bool) ≃ Fin (2 ^ n)` splitting on the
  first coordinate `0 : Fin (n + 1)`.
* `truthTableEquiv n` and `truthTableTargetEquiv n`: equivalences between truth tables
  `Fin (2 ^ n) → Bool`, scalar Boolean functions `ScalarFunction Bool n`, and single-output targets
  `Target Bool n 1`.
* `pairTruthTable tt₀ tt₁`: concatenates two `2 ^ n`-bit truth tables into a `2 ^ (n + 1)`-bit
  truth table corresponding to the subcube multiplexer `muxTarget`.
* `mcspScalar` / `mcspTarget`: gate-complexity MCSP predicate for an arbitrary basis.
* `mcspCostScalar` / `mcspCostTarget`: operation-cost MCSP predicate (used in particular with
  `DeMorgan.binaryCost` where NOT gates are free).
* `yesSet`, `costYesSet`, and `exactCostSet`: finite sets of truth tables with complexity `≤ s`
  or `= s`, together with Shannon and Lupanov/sharp counting upper bounds.
-/

@[expose] public section

namespace Algebraic.MCSP

private theorem two_pow_succ_eq_add (n : Nat) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  rw [Nat.pow_succ]
  omega

/-- Canonical recursive bijection between `n`-bit inputs and truth-table indices `Fin (2 ^ n)`.
For `n + 1`, inputs with `x 0 = false` map to the lower half `0 .. 2 ^ n - 1` and inputs with
`x 0 = true` map to the upper half `2 ^ n .. 2 ^ (n + 1) - 1`. -/
def inputEquiv : (n : Nat) → (Fin n → Bool) ≃ Fin (2 ^ n)
  | 0 =>
    { toFun := fun _ => ⟨0, Nat.one_pos⟩
      invFun := fun _ => Fin.elim0
      left_inv := fun x => funext fun i => Fin.elim0 i
      right_inv := fun i => by
        ext
        exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)).symm }
  | n + 1 =>
    { toFun := fun x =>
        let tailIdx := inputEquiv n (Fin.tail x)
        if x 0 then
          ⟨2 ^ n + tailIdx.val, by
            have := tailIdx.isLt
            have := two_pow_succ_eq_add n
            omega⟩
        else
          ⟨tailIdx.val, by
            have := tailIdx.isLt
            have := two_pow_succ_eq_add n
            omega⟩
      invFun := fun i =>
        if h : i.val < 2 ^ n then
          Fin.cons false ((inputEquiv n).symm ⟨i.val, h⟩)
        else
          Fin.cons true ((inputEquiv n).symm ⟨i.val - 2 ^ n, by
            have := i.isLt
            have := two_pow_succ_eq_add n
            omega⟩)
      left_inv := fun x => by
        dsimp only
        cases hb : x 0
        · have hlt : (inputEquiv n (Fin.tail x)).val < 2 ^ n := (inputEquiv n (Fin.tail x)).isLt
          simp only [Bool.false_eq_true, ↓reduceIte, hlt, ↓reduceDIte, Fin.eta,
            Equiv.symm_apply_apply]
          rw [← hb]
          exact Fin.cons_self_tail x
        · have hlt : ¬ (2 ^ n + (inputEquiv n (Fin.tail x)).val < 2 ^ n) := by omega
          simp only [↓reduceIte, hlt, ↓reduceDIte]
          have hsub :
              (⟨2 ^ n + (inputEquiv n (Fin.tail x)).val - 2 ^ n, by
                have := (inputEquiv n (Fin.tail x)).isLt
                have := two_pow_succ_eq_add n
                omega⟩ : Fin (2 ^ n)) = inputEquiv n (Fin.tail x) := by
            ext
            simp
          rw [hsub, Equiv.symm_apply_apply, ← hb]
          exact Fin.cons_self_tail x
      right_inv := fun i => by
        dsimp only
        by_cases h : i.val < 2 ^ n
        · simp [h]
        · simp only [h, ↓reduceDIte, Fin.cons_zero, ↓reduceIte, Fin.tail_cons,
            Equiv.apply_symm_apply]
          ext
          dsimp only
          omega }

@[simp]
theorem inputEquiv_cons_false {n : Nat} (y : Fin n → Bool) :
    (inputEquiv (n + 1) (Fin.cons false y)).val = (inputEquiv n y).val := by
  simp [inputEquiv]

@[simp]
theorem inputEquiv_cons_true {n : Nat} (y : Fin n → Bool) :
    (inputEquiv (n + 1) (Fin.cons true y)).val = 2 ^ n + (inputEquiv n y).val := by
  simp [inputEquiv]

theorem inputEquiv_symm_lt {n : Nat} {i : Fin (2 ^ (n + 1))} (h : i.val < 2 ^ n) :
    (inputEquiv (n + 1)).symm i = Fin.cons false ((inputEquiv n).symm ⟨i.val, h⟩) := by
  conv_lhs => unfold inputEquiv
  dsimp only [Equiv.coe_fn_symm_mk]
  simp only [h, ↓reduceDIte]

theorem inputEquiv_symm_ge {n : Nat} {i : Fin (2 ^ (n + 1))} (h : ¬ i.val < 2 ^ n) :
    (inputEquiv (n + 1)).symm i =
      Fin.cons true ((inputEquiv n).symm ⟨i.val - 2 ^ n, by
        have := i.isLt
        have := two_pow_succ_eq_add n
        omega⟩) := by
  conv_lhs => unfold inputEquiv
  dsimp only [Equiv.coe_fn_symm_mk]
  simp only [h, ↓reduceDIte]

/-- Equivalence between `2 ^ n`-bit truth tables and `n`-variable scalar Boolean functions. -/
def truthTableEquiv (n : Nat) : (Fin (2 ^ n) → Bool) ≃ ScalarFunction Bool n :=
  Equiv.arrowCongr (inputEquiv n).symm (Equiv.refl Bool)

@[simp]
theorem truthTableEquiv_apply {n : Nat} (tt : Fin (2 ^ n) → Bool) (x : Fin n → Bool) :
    truthTableEquiv n tt x = tt (inputEquiv n x) :=
  rfl

@[simp]
theorem truthTableEquiv_symm_apply {n : Nat} (f : ScalarFunction Bool n) (i : Fin (2 ^ n)) :
    (truthTableEquiv n).symm f i = f ((inputEquiv n).symm i) :=
  rfl

/-- Equivalence between scalar Boolean functions and single-output `Target`s. -/
def scalarTargetEquiv (n : Nat) : ScalarFunction Bool n ≃ Target Bool n 1 where
  toFun := fun f input _ => f input
  invFun := fun target input => target input 0
  left_inv := fun _ => rfl
  right_inv := fun target => by
    funext input output
    rw [Subsingleton.elim output 0]

/-- Equivalence between `2 ^ n`-bit truth tables and single-output `n`-variable Boolean targets. -/
def truthTableTargetEquiv (n : Nat) : (Fin (2 ^ n) → Bool) ≃ Target Bool n 1 where
  toFun := fun tt x _ => tt (inputEquiv n x)
  invFun := fun target i => target ((inputEquiv n).symm i) 0
  left_inv := fun tt => by
    funext i
    simp
  right_inv := fun target => by
    funext x o
    rw [Subsingleton.elim o 0]
    simp

@[simp]
theorem truthTableTargetEquiv_apply {n : Nat} (tt : Fin (2 ^ n) → Bool)
    (x : Fin n → Bool) (o : Fin 1) :
    truthTableTargetEquiv n tt x o = tt (inputEquiv n x) :=
  rfl

@[simp]
theorem truthTableTargetEquiv_symm_apply {n : Nat} (target : Target Bool n 1)
    (i : Fin (2 ^ n)) :
    (truthTableTargetEquiv n).symm target i = target ((inputEquiv n).symm i) 0 :=
  rfl

/-- Multiplex two `n`-variable targets along the leading input bit `0 : Fin (n + 1)`. -/
def muxTarget {n : Nat} (u₀ u₁ : Target Bool n 1) : Target Bool (n + 1) 1 :=
  fun x o => if x 0 then u₁ (Fin.tail x) o else u₀ (Fin.tail x) o

@[simp]
theorem muxTarget_cons_false {n : Nat} (u₀ u₁ : Target Bool n 1)
    (y : Fin n → Bool) (o : Fin 1) :
    muxTarget u₀ u₁ (Fin.cons false y) o = u₀ y o := by
  simp [muxTarget]

@[simp]
theorem muxTarget_cons_true {n : Nat} (u₀ u₁ : Target Bool n 1)
    (y : Fin n → Bool) (o : Fin 1) :
    muxTarget u₀ u₁ (Fin.cons true y) o = u₁ y o := by
  simp [muxTarget]

/-- Concatenate two `2 ^ n`-bit truth tables into a `2 ^ (n + 1)`-bit truth table. -/
def pairTruthTable {n : Nat} (tt₀ tt₁ : Fin (2 ^ n) → Bool) : Fin (2 ^ (n + 1)) → Bool :=
  fun i =>
    if h : i.val < 2 ^ n then
      tt₀ ⟨i.val, h⟩
    else
      tt₁ ⟨i.val - 2 ^ n, by
        have := i.isLt
        have := two_pow_succ_eq_add n
        omega⟩

/-- Extract the lower half (`x 0 = false` subcube) of a `2 ^ (n + 1)`-bit truth table. -/
def leftHalf {n : Nat} (tt : Fin (2 ^ (n + 1)) → Bool) : Fin (2 ^ n) → Bool :=
  fun i => tt ⟨i.val, by
    have := i.isLt
    have := two_pow_succ_eq_add n
    omega⟩

/-- Extract the upper half (`x 0 = true` subcube) of a `2 ^ (n + 1)`-bit truth table. -/
def rightHalf {n : Nat} (tt : Fin (2 ^ (n + 1)) → Bool) : Fin (2 ^ n) → Bool :=
  fun i => tt ⟨2 ^ n + i.val, by
    have := i.isLt
    have := two_pow_succ_eq_add n
    omega⟩

@[simp]
theorem leftHalf_pairTruthTable {n : Nat} (tt₀ tt₁ : Fin (2 ^ n) → Bool) :
    leftHalf (pairTruthTable tt₀ tt₁) = tt₀ := by
  funext i
  simp [leftHalf, pairTruthTable, i.isLt]

@[simp]
theorem rightHalf_pairTruthTable {n : Nat} (tt₀ tt₁ : Fin (2 ^ n) → Bool) :
    rightHalf (pairTruthTable tt₀ tt₁) = tt₁ := by
  funext i
  have hlt : ¬ (2 ^ n + i.val < 2 ^ n) := by omega
  simp [rightHalf, pairTruthTable, hlt]

@[simp]
theorem pairTruthTable_leftHalf_rightHalf {n : Nat} (tt : Fin (2 ^ (n + 1)) → Bool) :
    pairTruthTable (leftHalf tt) (rightHalf tt) = tt := by
  funext i
  by_cases h : i.val < 2 ^ n
  · simp [pairTruthTable, leftHalf, h]
  · simp only [pairTruthTable, h, ↓reduceDIte, rightHalf]
    congr 1
    ext
    dsimp only
    omega

theorem pairTruthTable_injective_left {n : Nat} {tt₀ tt₀' tt₁ : Fin (2 ^ n) → Bool}
    (h : pairTruthTable tt₀ tt₁ = pairTruthTable tt₀' tt₁) : tt₀ = tt₀' := by
  have := congrArg leftHalf h
  simpa using this

theorem pairTruthTable_injective_right {n : Nat} {tt₀ tt₁ tt₁' : Fin (2 ^ n) → Bool}
    (h : pairTruthTable tt₀ tt₁ = pairTruthTable tt₀ tt₁') : tt₁ = tt₁' := by
  have := congrArg rightHalf h
  simpa using this

/-- Pairing two truth tables corresponds under `truthTableTargetEquiv` to `muxTarget`. -/
theorem truthTableTargetEquiv_pairTruthTable {n : Nat} (tt₀ tt₁ : Fin (2 ^ n) → Bool) :
    truthTableTargetEquiv (n + 1) (pairTruthTable tt₀ tt₁) =
      muxTarget (truthTableTargetEquiv n tt₀) (truthTableTargetEquiv n tt₁) := by
  funext x o
  simp only [truthTableTargetEquiv_apply, muxTarget]
  cases hb : x 0
  · have hx : x = Fin.cons false (Fin.tail x) := by
      rw [← hb]
      exact (Fin.cons_self_tail x).symm
    have hval : (inputEquiv (n + 1) x).val = (inputEquiv n (Fin.tail x)).val := by
      conv_lhs => rw [hx]
      exact inputEquiv_cons_false (Fin.tail x)
    have hlt : (inputEquiv (n + 1) x).val < 2 ^ n := by
      rw [hval]
      exact (inputEquiv n (Fin.tail x)).isLt
    simp only [pairTruthTable, hlt, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
    congr 1
    ext
    exact hval
  · have hx : x = Fin.cons true (Fin.tail x) := by
      rw [← hb]
      exact (Fin.cons_self_tail x).symm
    have hval : (inputEquiv (n + 1) x).val = 2 ^ n + (inputEquiv n (Fin.tail x)).val := by
      conv_lhs => rw [hx]
      exact inputEquiv_cons_true (Fin.tail x)
    have hlt : ¬ (inputEquiv (n + 1) x).val < 2 ^ n := by
      rw [hval]
      omega
    simp only [pairTruthTable, hlt, ↓reduceDIte, ↓reduceIte]
    congr 1
    ext
    dsimp only
    omega

/-- Characterization of bounded weighted circuit complexity by existence of a concrete circuit. -/
theorem costComplexity_le_nat_iff {σ : Signature} {n m : Nat}
    (interpretation : Interpretation σ Bool) (cost : OperationCost σ)
    (target : Target Bool n m) (s : Nat) :
    Circuit.costComplexity interpretation cost target ≤ (s : ℕ∞) ↔
      ∃ circuit : Circuit σ n m,
        circuit.cost cost ≤ s ∧ circuit.ComputesWith interpretation target := by
  constructor
  · intro hle
    by_contra hno
    have hge : ((s + 1 : Nat) : ℕ∞) ≤ Circuit.costComplexity interpretation cost target := by
      apply Circuit.le_costComplexity
      intro circuit computes
      have hlt : s < circuit.cost cost :=
        lt_of_not_ge fun hcost => hno ⟨circuit, hcost, computes⟩
      exact_mod_cast Nat.succ_le_of_lt hlt
    have himpossible : ((s + 1 : Nat) : ℕ∞) ≤ (s : ℕ∞) := hge.trans hle
    have : s + 1 ≤ s := by exact_mod_cast himpossible
    omega
  · rintro ⟨circuit, hcost, computes⟩
    exact (circuit.costComplexity_le cost computes).trans (by exact_mod_cast hcost)

/-- Characterization of bounded gate complexity by existence of a concrete circuit. -/
theorem gateComplexity_le_nat_iff {σ : Signature} {n m : Nat}
    (interpretation : Interpretation σ Bool) (target : Target Bool n m) (s : Nat) :
    Circuit.gateComplexity interpretation target ≤ (s : ℕ∞) ↔
      ∃ circuit : Circuit σ n m,
        circuit.size ≤ s ∧ circuit.ComputesWith interpretation target := by
  simpa [Circuit.gateComplexity, Circuit.cost_unit] using
    costComplexity_le_nat_iff interpretation OperationCost.unit target s

/-- Gate-complexity MCSP as a scalar Boolean function on `2 ^ n`-bit truth tables. -/
noncomputable def mcspScalar {σ : Signature} (interpretation : Interpretation σ Bool)
    (n s : Nat) : ScalarFunction Bool (2 ^ n) := by
  classical
  exact fun tt => decide (Circuit.gateComplexity interpretation (truthTableTargetEquiv n tt) ≤ s)

/-- Gate-complexity MCSP as a single-output `Target`. -/
noncomputable def mcspTarget {σ : Signature} (interpretation : Interpretation σ Bool)
    (n s : Nat) : Target Bool (2 ^ n) 1 :=
  fun tt _ => mcspScalar interpretation n s tt

@[simp]
theorem mcspScalar_eq_true_iff {σ : Signature} (interpretation : Interpretation σ Bool)
    (n s : Nat) (tt : Fin (2 ^ n) → Bool) :
    mcspScalar interpretation n s tt = true ↔
      Circuit.gateComplexity interpretation (truthTableTargetEquiv n tt) ≤ s := by
  classical
  simp [mcspScalar]

@[simp]
theorem mcspScalar_eq_false_iff {σ : Signature} (interpretation : Interpretation σ Bool)
    (n s : Nat) (tt : Fin (2 ^ n) → Bool) :
    mcspScalar interpretation n s tt = false ↔
      (s : ℕ∞) < Circuit.gateComplexity interpretation (truthTableTargetEquiv n tt) := by
  classical
  simp [mcspScalar]

/-- Operation-cost MCSP as a scalar Boolean function on `2 ^ n`-bit truth tables. -/
noncomputable def mcspCostScalar {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) : ScalarFunction Bool (2 ^ n) := by
  classical
  exact fun tt =>
    decide (Circuit.costComplexity interpretation cost (truthTableTargetEquiv n tt) ≤ s)

/-- Operation-cost MCSP as a single-output `Target`. -/
noncomputable def mcspCostTarget {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) : Target Bool (2 ^ n) 1 :=
  fun tt _ => mcspCostScalar interpretation cost n s tt

@[simp]
theorem mcspCostScalar_eq_true_iff {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) (tt : Fin (2 ^ n) → Bool) :
    mcspCostScalar interpretation cost n s tt = true ↔
      Circuit.costComplexity interpretation cost (truthTableTargetEquiv n tt) ≤ s := by
  classical
  simp [mcspCostScalar]

@[simp]
theorem mcspCostScalar_eq_false_iff {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) (tt : Fin (2 ^ n) → Bool) :
    mcspCostScalar interpretation cost n s tt = false ↔
      (s : ℕ∞) < Circuit.costComplexity interpretation cost (truthTableTargetEquiv n tt) := by
  classical
  simp [mcspCostScalar]

@[simp]
theorem mcspCostScalar_unit {σ : Signature} (interpretation : Interpretation σ Bool)
    (n s : Nat) :
    mcspCostScalar interpretation OperationCost.unit n s = mcspScalar interpretation n s :=
  rfl

/-- The finite set of `2 ^ n`-bit truth tables with gate complexity at most `s`. -/
noncomputable def yesSet {σ : Signature} (interpretation : Interpretation σ Bool)
    (n s : Nat) : Finset (Fin (2 ^ n) → Bool) := by
  classical
  exact Finset.univ.filter fun tt => mcspScalar interpretation n s tt = true

@[simp]
theorem mem_yesSet_iff {σ : Signature} (interpretation : Interpretation σ Bool)
    (n s : Nat) (tt : Fin (2 ^ n) → Bool) :
    tt ∈ yesSet interpretation n s ↔
      Circuit.gateComplexity interpretation (truthTableTargetEquiv n tt) ≤ s := by
  classical
  simp [yesSet]

/-- The finite set of `2 ^ n`-bit truth tables with operation-cost complexity at most `s`. -/
noncomputable def costYesSet {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) : Finset (Fin (2 ^ n) → Bool) := by
  classical
  exact Finset.univ.filter fun tt => mcspCostScalar interpretation cost n s tt = true

@[simp]
theorem mem_costYesSet_iff {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) (tt : Fin (2 ^ n) → Bool) :
    tt ∈ costYesSet interpretation cost n s ↔
      Circuit.costComplexity interpretation cost (truthTableTargetEquiv n tt) ≤ s := by
  classical
  simp [costYesSet]

/-- The finite set of `2 ^ n`-bit truth tables with operation-cost complexity *exactly* `s`. -/
noncomputable def exactCostSet {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) : Finset (Fin (2 ^ n) → Bool) := by
  classical
  exact Finset.univ.filter fun tt =>
    Circuit.costComplexity interpretation cost (truthTableTargetEquiv n tt) = s

@[simp]
theorem mem_exactCostSet_iff {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) (tt : Fin (2 ^ n) → Bool) :
    tt ∈ exactCostSet interpretation cost n s ↔
      Circuit.costComplexity interpretation cost (truthTableTargetEquiv n tt) = s := by
  classical
  simp [exactCostSet]

theorem exactCostSet_subset_costYesSet {σ : Signature} (interpretation : Interpretation σ Bool)
    (cost : OperationCost σ) (n s : Nat) :
    exactCostSet interpretation cost n s ⊆ costYesSet interpretation cost n s := by
  intro tt htt
  rw [mem_exactCostSet_iff] at htt
  rw [mem_costYesSet_iff, htt]

/-- `yesSet` has the same cardinality as `Circuit.functionsAtMost`. -/
theorem card_yesSet_eq_card_functionsAtMost {σ : Signature} [Fintype σ.Op]
    (interpretation : Interpretation σ Bool) (n s : Nat) :
    (yesSet interpretation n s).card = (Circuit.functionsAtMost interpretation n 1 s).card := by
  classical
  apply Finset.card_bij (fun tt _ => truthTableTargetEquiv n tt)
  · intro tt htt
    rw [mem_yesSet_iff, gateComplexity_le_nat_iff] at htt
    exact Circuit.mem_functionsAtMost_iff.mpr htt
  · intro tt₁ _ tt₂ _ heq
    exact (truthTableTargetEquiv n).injective heq
  · intro target htarget
    refine ⟨(truthTableTargetEquiv n).symm target, ?_,
      (truthTableTargetEquiv n).apply_symm_apply target⟩
    rw [mem_yesSet_iff, (truthTableTargetEquiv n).apply_symm_apply, gateComplexity_le_nat_iff]
    exact Circuit.mem_functionsAtMost_iff.mp htarget

/-- Ordered-syntax Shannon upper bound on the number of `yes` truth tables of `MCSP`. -/
theorem card_yesSet_le_orderedBudget {σ : Signature} [Fintype σ.Op]
    (interpretation : Interpretation σ Bool) (n s : Nat) :
    (yesSet interpretation n s).card ≤ σ.orderedBudget n 1 s := by
  rw [card_yesSet_eq_card_functionsAtMost]
  exact Circuit.card_functionsAtMost_le interpretation

/-- Sharp (`g!`-reduced) Shannon upper bound on the number of `yes` truth tables of `MCSP`. -/
theorem card_yesSet_le_sharpBudget {σ : Signature} [Fintype σ.Op]
    (interpretation : Interpretation σ Bool) (n s : Nat) :
    (yesSet interpretation n s).card ≤ σ.sharpBudget n 1 s := by
  rw [card_yesSet_eq_card_functionsAtMost]
  exact Circuit.card_functionsAtMost_le_sharpBudget interpretation n 1 s

end Algebraic.MCSP

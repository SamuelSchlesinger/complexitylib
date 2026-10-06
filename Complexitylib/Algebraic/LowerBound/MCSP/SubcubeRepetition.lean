/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.CircuitAnalysis
public import Complexitylib.Algebraic.Basis.DeMorgan.Influence
public import Complexitylib.Algebraic.Basis.DeMorgan.RestrictionAnalysis
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit
public import Complexitylib.Algebraic.LowerBound.MCSP.Symmetry
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Subfunctions

/-!
# Exact-complexity subcube repetition and MCSP lower bounds

This module proves **Foundational Lemma B (Exact-Complexity Subcube Repetition)** for
`DeMorgan.binaryCost` and derives three families of circuit and formula lower bounds for
`MCSP`:

1. **Exact-complexity subcube repetition**:
   * For any `n`-variable target `u`, repeating `u` on both halves of the `(n + 1)`-cube via
     `muxTarget u u` preserves `DeMorgan.binaryCost` complexity:
     `costComplexity (muxTarget u u) = costComplexity u`.
   * For any distinct `n`-variable targets `u₀ ≠ u₁` where at least one has positive
     `DeMorgan.binaryCost` complexity, any De Morgan circuit computing `muxTarget u₀ u₁` must
     have a charged gate reading coordinate `0 : Fin (n + 1)` (via `differingPath_of_gate_ne`
     and `DifferingPath.exists_first`), so restricting `0` to either `false` or `true` deletes
     at least one charged gate (`restrictProgram_deleted_of_readsInput`). Consequently both
     `costComplexity u₀ + 1 ≤ costComplexity (muxTarget u₀ u₁)` and
     `costComplexity u₁ + 1 ≤ costComplexity (muxTarget u₀ u₁)`.
   * Specializing to a truth table
     `tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s`
     with `1 ≤ s`, for every `tt' : Fin (2 ^ n) → Bool`:
     `mcspCostScalar ... (n + 1) s (pairTruthTable tt' tt) = true ↔ tt' = tt` and
     `mcspCostScalar ... (n + 1) s (pairTruthTable tt tt') = true ↔ tt' = tt`.
2. **Single-cut communication / cutwidth lower bound**:
   Across any wire cut `S` separating the left-half truth-table inputs (`j.val < 2 ^ n`) from
   the right-half truth-table inputs, the diagonal truth tables `pairTruthTable tt tt` for
   `tt ∈ exactCostSet ... n s` must have pairwise distinct boundary keys, yielding
   `(exactCostSet ... n s).card ≤ 2 ^ ((forward c.program S).card + (backward c.program S).card)`.
3. **Khrapchenko formula and bounded-sharing De Morgan circuit lower bounds**:
   Every diagonal truth table `pairTruthTable tt tt` (`tt ∈ exactCostSet ... n s`, `1 ≤ s`) is a
   `true`-input of `mcspCostScalar ... (n + 1) s` with full sensitivity `2 ^ (n + 1)`, so every
   Khrapchenko measure bound `M` satisfies `2 ^ (n + 1) ≤ M`. This yields
   `2 ^ (n + 1) ≤ F.leaves` for De Morgan formulas and
   `2 ^ (n + 1) ≤ (k + 1) * (c.cost DeMorgan.binaryCost + k + 1)` for De Morgan circuits with at
   most `k` shared gates.
4. **Nechiporuk subfunction and formula lower bounds**:
   For any `Y₀ : Finset (Fin (2 ^ n))`, embedded into the left half of `Fin (2 ^ (n + 1))` as
   `leftBlock Y₀`, distinct restrictions `restrictTo Y₀ tt` of truth tables
   `tt ∈ exactCostSet ... n s` induce distinct subfunctions of `mcspCostScalar ... (n + 1) s` on
   `leftBlock Y₀`:
   `((exactCostSet ... n s).image (restrictTo Y₀)).card ≤
     (Nechiporuk.subfunctions ... (leftBlock Y₀)).card`.
   Taking `Y₀ = Finset.univ` gives
   `(exactCostSet ... n s).card ≤ (Nechiporuk.subfunctions ... (leftBlock Finset.univ)).card`.
   Combined with `Nechiporuk.card_subfunctions_le`, these give the corresponding
   `Binary.Formula` leaf lower bounds `... ≤ 2 * 16 ^ F.leavesIn (leftBlock Y₀)`.

All results above hold for every `s ≥ 1` such that some truth table has exact
`DeMorgan.binaryCost` complexity `s` (hypothesis `htt` or a nonempty `exactCostSet`);
`Complexitylib.Algebraic.LowerBound.MCSP.NonVacuity` exhibits such a table for `s = 1`.

The resulting lower bounds are modest: writing `N = 2 ^ (n + 1)` for the number of MCSP inputs,
the Khrapchenko consequences give `N ≤ F.leaves` (and the analogous linear bound with sharing),
since the sensitivity argument uses a single `true`-input. The Nechiporuk consequences are also at
most linear in `N`, because `(exactCostSet ... n s).card ≤ 2 ^ (2 ^ n) = 2 ^ (N / 2)`, so the
bound on `F.leavesIn (leftBlock Finset.univ)` is at most about `N / 8`.
-/

@[expose] public section

namespace Algebraic.MCSP

open scoped BigOperators

/-! ## Subcube repetition and `DeMorgan.binaryCost` gate elimination -/

/-- Fixing coordinate `0 : Fin (n + 1)` to `b` sends `y : Fin n → Bool` to `Fin.cons b y`. -/
@[simp]
theorem fix_zero_apply {n : Nat} (b : Bool) (y : Fin n → Bool) :
    (InputSubstitution.fix (0 : Fin (n + 1)) b).apply y = Fin.cons b y := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j => exact InputSubstitution.fix_succAbove 0 b y j

/-- Fixing the leading bit of `muxTarget u₀ u₁` to `false` recovers `u₀`. -/
@[simp]
theorem muxTarget_substitute_fix_false {n : Nat} (u₀ u₁ : Target Bool n 1) :
    (muxTarget u₀ u₁).substitute (InputSubstitution.fix 0 false) = u₀ := by
  funext y o
  simp

/-- Fixing the leading bit of `muxTarget u₀ u₁` to `true` recovers `u₁`. -/
@[simp]
theorem muxTarget_substitute_fix_true {n : Nat} (u₀ u₁ : Target Bool n 1) :
    (muxTarget u₀ u₁).substitute (InputSubstitution.fix 0 true) = u₁ := by
  funext y o
  simp

/-- Repeating a target on both halves of the `(n + 1)`-cube does not increase its
`DeMorgan.binaryCost` complexity. -/
theorem costComplexity_muxTarget_self_le {n : Nat} (u : Target Bool n 1) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (muxTarget u u) ≤
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u := by
  apply Circuit.le_costComplexity
  intro c hc
  have hcomp : (c.mapInputs Fin.succ).ComputesWith DeMorgan.interpretation (muxTarget u u) := by
    intro x
    funext o
    have htail : x ∘ Fin.succ = Fin.tail x := rfl
    simp [muxTarget, htail, hc (Fin.tail x)]
  have hle := (c.mapInputs Fin.succ).costComplexity_le DeMorgan.binaryCost hcomp
  simpa using hle

/-- Restricting coordinate `0` of a De Morgan circuit computing `muxTarget u₀ u₁` to `b` yields a
circuit computing the corresponding branch `cond b u₁ u₀`. -/
theorem restrictCircuit_computes_muxTarget {n : Nat} {u₀ u₁ : Target Bool n 1}
    {c : Circuit DeMorgan.signature (n + 1) 1}
    (hc : c.ComputesWith DeMorgan.interpretation (muxTarget u₀ u₁)) (b : Bool) :
    (DeMorgan.restrictCircuit c 0 b).result.ComputesWith DeMorgan.interpretation
      (cond b u₁ u₀) := by
  intro y
  funext o
  rw [(DeMorgan.restrictCircuit c 0 b).eval_eq y, hc ((InputSubstitution.fix 0 b).apply y),
    fix_zero_apply]
  cases b <;> simp

/-- Restricting coordinate `0` to `b` shows
`costComplexity (cond b u₁ u₀) ≤ costComplexity (muxTarget u₀ u₁)`. -/
theorem costComplexity_le_muxTarget {n : Nat} (u₀ u₁ : Target Bool n 1) (b : Bool) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (cond b u₁ u₀) ≤
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (muxTarget u₀ u₁) := by
  apply Circuit.le_costComplexity
  intro c hc
  let rest := DeMorgan.restrictCircuit c 0 b
  have hcost : rest.result.cost DeMorgan.binaryCost ≤ c.cost DeMorgan.binaryCost := by
    have := rest.cost_eq
    omega
  exact (rest.result.costComplexity_le DeMorgan.binaryCost
    (restrictCircuit_computes_muxTarget hc b)).trans (by exact_mod_cast hcost)

/-- Restricting coordinate `0` to `false` shows
`costComplexity u₀ ≤ costComplexity (muxTarget u₀ u₁)`. -/
theorem costComplexity_le_muxTarget_left {n : Nat} (u₀ u₁ : Target Bool n 1) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₀ ≤
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (muxTarget u₀ u₁) :=
  costComplexity_le_muxTarget u₀ u₁ false

/-- Restricting coordinate `0` to `true` shows
`costComplexity u₁ ≤ costComplexity (muxTarget u₀ u₁)`. -/
theorem costComplexity_le_muxTarget_right {n : Nat} (u₀ u₁ : Target Bool n 1) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₁ ≤
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (muxTarget u₀ u₁) :=
  costComplexity_le_muxTarget u₀ u₁ true

/-- **Subcube repetition**: repeating a target on both halves of the `(n + 1)`-cube preserves its
`DeMorgan.binaryCost` complexity exactly. -/
@[simp]
theorem costComplexity_muxTarget_self {n : Nat} (u : Target Bool n 1) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (muxTarget u u) =
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u :=
  le_antisymm (costComplexity_muxTarget_self_le u) (costComplexity_le_muxTarget_left u u)

/-- Constant targets have zero `DeMorgan.binaryCost` complexity. -/
@[simp]
theorem costComplexity_constant_eq_zero {n : Nat} (b : Bool) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
      (fun (_ : Fin n → Bool) (_ : Fin 1) => b) = 0 := by
  rw [← nonpos_iff_eq_zero]
  let c : Circuit DeMorgan.signature n 1 :=
    { program := Program.empty.gate (DeMorgan.constantLine b)
      outputs := fun _ => Wire.gate 0 }
  have hcomp : c.ComputesWith DeMorgan.interpretation (fun _ _ => b) := by
    intro x
    funext o
    rw [Subsingleton.elim o 0]
    cases b <;> rfl
  have hcost : c.cost DeMorgan.binaryCost = 0 := by
    cases b <;> rfl
  simpa [hcost] using c.costComplexity_le DeMorgan.binaryCost hcomp

/-- If `u₀ ≠ u₁` and at least one of `u₀, u₁` has positive `DeMorgan.binaryCost` complexity,
then any circuit computing `muxTarget u₀ u₁` has `binaryCost` strictly larger than both
`costComplexity u₀` and `costComplexity u₁`. -/
theorem costComplexity_add_one_le_cost_of_computes_muxTarget {n : Nat}
    {u₀ u₁ : Target Bool n 1} (hne : u₀ ≠ u₁)
    (hpos : 1 ≤ Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₀ ∨
      1 ≤ Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₁)
    (c : Circuit DeMorgan.signature (n + 1) 1)
    (hc : c.ComputesWith DeMorgan.interpretation (muxTarget u₀ u₁)) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₀ + 1 ≤
        (c.cost DeMorgan.binaryCost : ℕ∞) ∧
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₁ + 1 ≤
        (c.cost DeMorgan.binaryCost : ℕ∞) := by
  have hex : ∃ y : Fin n → Bool, u₀ y 0 ≠ u₁ y 0 := by
    by_contra hall
    apply hne
    funext y o
    rw [Subsingleton.elim o 0]
    exact not_ne_iff.mp fun h => hall ⟨y, h⟩
  obtain ⟨y, hy⟩ := hex
  let left : Fin (n + 1) → Bool := Fin.cons false y
  let right : Fin (n + 1) → Bool := Fin.cons true y
  have hdiff : c.eval DeMorgan.interpretation left 0 ≠ c.eval DeMorgan.interpretation right 0 := by
    have hl := congrFun (hc left) 0
    have hr := congrFun (hc right) 0
    simp only [left, right, muxTarget_cons_false, muxTarget_cons_true] at hl hr
    rw [hl, hr]
    exact hy
  have hagree : ∀ k : Fin (n + 1), k ≠ 0 → left k = right k := by
    intro k hk
    cases k using Fin.cases with
    | zero => exact False.elim (hk rfl)
    | succ j => rfl
  have valid := DeMorgan.origins_valid c.program (c.outputs 0)
  generalize horig : DeMorgan.origins c.program (c.outputs 0) = orig at valid
  cases orig with
  | constant val =>
      exfalso
      apply hdiff
      have hl := DeMorgan.origins_eval c.program left (c.outputs 0)
      have hr := DeMorgan.origins_eval c.program right (c.outputs 0)
      rw [horig, DeMorgan.ResidualValue.eval_constant] at hl hr
      change c.program.trace DeMorgan.interpretation left (c.outputs 0) =
        c.program.trace DeMorgan.interpretation right (c.outputs 0)
      rw [← hl, ← hr]
  | wire neg w =>
      rcases valid with ⟨inputIdx, rfl⟩ | ⟨gate, rfl, hcharged⟩
      · exfalso
        have hidx0 : inputIdx = 0 := by
          by_contra hne0
          apply hdiff
          have hl := DeMorgan.origins_eval c.program left (c.outputs 0)
          have hr := DeMorgan.origins_eval c.program right (c.outputs 0)
          rw [horig] at hl hr
          change c.program.trace DeMorgan.interpretation left (c.outputs 0) =
            c.program.trace DeMorgan.interpretation right (c.outputs 0)
          rw [← hl, ← hr]
          have hlr := hagree inputIdx hne0
          cases neg <;> simp [DeMorgan.ResidualValue.eval, Program.trace, hlr]
        subst inputIdx
        have hu₀ : u₀ = fun _ _ => neg := by
          funext z o
          rw [Subsingleton.elim o 0]
          have hcz := congrFun (hc (Fin.cons false z)) 0
          have horig_z := DeMorgan.origins_eval c.program (Fin.cons false z) (c.outputs 0)
          rw [horig] at horig_z
          simp only [muxTarget_cons_false] at hcz
          rw [← hcz]
          change c.program.trace DeMorgan.interpretation (Fin.cons false z) (c.outputs 0) = neg
          rw [← horig_z]
          cases neg <;> rfl
        have hu₁ : u₁ = fun _ _ => !neg := by
          funext z o
          rw [Subsingleton.elim o 0]
          have hcz := congrFun (hc (Fin.cons true z)) 0
          have horig_z := DeMorgan.origins_eval c.program (Fin.cons true z) (c.outputs 0)
          rw [horig] at horig_z
          simp only [muxTarget_cons_true] at hcz
          rw [← hcz]
          change c.program.trace DeMorgan.interpretation (Fin.cons true z) (c.outputs 0) = !neg
          rw [← horig_z]
          cases neg <;> rfl
        rw [hu₀, hu₁, costComplexity_constant_eq_zero, costComplexity_constant_eq_zero] at hpos
        rcases hpos with h | h <;> exact absurd h (by decide)
      · let root : DeMorgan.OutputRoot c :=
          { gate := gate
            negated := neg
            origin_eq := horig
            charged := hcharged }
        have hgate_ne := root.gate_ne_of_output_ne left right hdiff
        have hpath := DeMorgan.differingPath_of_gate_ne c.program 0 left right hagree
          gate hcharged hgate_ne
        obtain ⟨first, hreads, _, _⟩ := hpath.exists_first
        have hdel : ∀ b : Bool, 1 ≤ (DeMorgan.restrictCircuit c 0 b).deleted.card := by
          intro b
          exact Finset.card_pos.mpr
            ⟨first, DeMorgan.restrictProgram_deleted_of_readsInput c.program 0 b hreads⟩
        have hstep : ∀ b : Bool,
            Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (cond b u₁ u₀) + 1 ≤
              (c.cost DeMorgan.binaryCost : ℕ∞) := by
          intro b
          let rest := DeMorgan.restrictCircuit c 0 b
          have hcost : rest.result.cost DeMorgan.binaryCost + 1 ≤ c.cost DeMorgan.binaryCost := by
            have hceq := rest.cost_eq
            have hd : 1 ≤ rest.deleted.card := hdel b
            omega
          calc
            Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (cond b u₁ u₀) + 1
                ≤ (rest.result.cost DeMorgan.binaryCost : ℕ∞) + 1 :=
              add_le_add_left (rest.result.costComplexity_le DeMorgan.binaryCost
                (restrictCircuit_computes_muxTarget hc b)) 1
            _ ≤ (c.cost DeMorgan.binaryCost : ℕ∞) := by exact_mod_cast hcost
        exact ⟨hstep false, hstep true⟩

/-- If `u₀ ≠ u₁` and at least one has positive `DeMorgan.binaryCost` complexity, then
`muxTarget u₀ u₁` has `DeMorgan.binaryCost` complexity strictly greater than both `u₀` and `u₁`. -/
theorem costComplexity_muxTarget_ge_add_one {n : Nat} {u₀ u₁ : Target Bool n 1}
    (hne : u₀ ≠ u₁)
    (hpos : 1 ≤ Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₀ ∨
      1 ≤ Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₁) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₀ + 1 ≤
        Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (muxTarget u₀ u₁) ∧
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost u₁ + 1 ≤
        Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost (muxTarget u₀ u₁) := by
  constructor
  · apply Circuit.le_costComplexity
    intro c hc
    exact (costComplexity_add_one_le_cost_of_computes_muxTarget hne hpos c hc).1
  · apply Circuit.le_costComplexity
    intro c hc
    exact (costComplexity_add_one_le_cost_of_computes_muxTarget hne hpos c hc).2

/-- **Foundational Lemma B (left half)**: For `1 ≤ s` and any truth table `tt` of exact
`DeMorgan.binaryCost` complexity `s`, pairing `tt'` with `tt` yields complexity `≤ s` if and only
if `tt' = tt`. -/
theorem mcspCostScalar_pairTruthTable_left_eq_true_iff {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    (tt' : Fin (2 ^ n) → Bool) :
    mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
        (pairTruthTable tt' tt) = true ↔
      tt' = tt := by
  rw [mem_exactCostSet_iff] at htt
  rw [mcspCostScalar_eq_true_iff, truthTableTargetEquiv_pairTruthTable]
  constructor
  · intro hle
    by_contra hne
    have hne_target : truthTableTargetEquiv n tt' ≠ truthTableTargetEquiv n tt :=
      fun heq => hne ((truthTableTargetEquiv n).injective heq)
    have hpos : 1 ≤ Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (truthTableTargetEquiv n tt) := by
      rw [htt]
      exact_mod_cast hs
    have hgt := (costComplexity_muxTarget_ge_add_one hne_target (Or.inr hpos)).2
    rw [htt] at hgt
    have himp : ((s + 1 : Nat) : ℕ∞) ≤ (s : ℕ∞) := hgt.trans hle
    have : s + 1 ≤ s := by exact_mod_cast himp
    omega
  · rintro rfl
    rw [costComplexity_muxTarget_self, htt]

/-- **Foundational Lemma B (right half)**: For `1 ≤ s` and any truth table `tt` of exact
`DeMorgan.binaryCost` complexity `s`, pairing `tt` with `tt'` yields complexity `≤ s` if and only
if `tt' = tt`. -/
theorem mcspCostScalar_pairTruthTable_right_eq_true_iff {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    (tt' : Fin (2 ^ n) → Bool) :
    mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
        (pairTruthTable tt tt') = true ↔
      tt' = tt := by
  rw [mem_exactCostSet_iff] at htt
  rw [mcspCostScalar_eq_true_iff, truthTableTargetEquiv_pairTruthTable]
  constructor
  · intro hle
    by_contra hne
    have hne_target : truthTableTargetEquiv n tt ≠ truthTableTargetEquiv n tt' :=
      fun heq => hne ((truthTableTargetEquiv n).injective heq.symm)
    have hpos : 1 ≤ Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (truthTableTargetEquiv n tt) := by
      rw [htt]
      exact_mod_cast hs
    have hgt := (costComplexity_muxTarget_ge_add_one hne_target (Or.inl hpos)).1
    rw [htt] at hgt
    have himp : ((s + 1 : Nat) : ℕ∞) ≤ (s : ℕ∞) := hgt.trans hle
    have : s + 1 ≤ s := by exact_mod_cast himp
    omega
  · rintro rfl
    rw [costComplexity_muxTarget_self, htt]

/-! ## Single-cut communication and cutwidth lower bound for MCSP -/

/-- If a wire cut `S` contains the left-half input wires (`j.val < 2 ^ n`) and excludes the
right-half input wires, mixing two diagonal truth tables `pairTruthTable tt₁ tt₁` and
`pairTruthTable tt₂ tt₂` across `S` produces `pairTruthTable tt₁ tt₂`. -/
theorem mix_pairTruthTable_of_halfCut {n g : Nat}
    {S : Finset (Wire (2 ^ (n + 1)) g)}
    (hS : ∀ j : Fin (2 ^ (n + 1)), Wire.input j ∈ S ↔ j.val < 2 ^ n)
    (tt₁ tt₂ : Fin (2 ^ n) → Bool) :
    Cutwidth.SingleCut.mix S (pairTruthTable tt₁ tt₁) (pairTruthTable tt₂ tt₂) =
      pairTruthTable tt₁ tt₂ := by
  funext j
  simp only [Cutwidth.SingleCut.mix, hS j, pairTruthTable]
  split_ifs with hlt <;> rfl

/-- **Single-cut communication lower bound for MCSP**: For any circuit `c` computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` (`1 ≤ s`) and any wire
cut `S` separating the left-half truth-table inputs (`j.val < 2 ^ n`) from the right-half
truth-table inputs, the boundary keys of `pairTruthTable tt tt` for `tt ∈ exactCostSet ... n s`
are pairwise distinct, so
`(exactCostSet ... n s).card ≤ 2 ^ ((forward c.program S).card + (backward c.program S).card)`. -/
theorem mcsp_singleCut_card_exactCostSet_le {σ : Signature}
    {interpretation : Interpretation σ Bool} {n s : Nat} (hs : 1 ≤ s)
    (c : Circuit σ (2 ^ (n + 1)) 1)
    (hc : c.ComputesWith interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s))
    (S : Finset (Wire (2 ^ (n + 1)) c.size))
    (hS : ∀ j : Fin (2 ^ (n + 1)), Wire.input j ∈ S ↔ j.val < 2 ^ n) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
      2 ^ ((Cutwidth.SingleCut.forward c.program S).card +
        (Cutwidth.SingleCut.backward c.program S).card) := by
  classical
  let exact := exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s
  let diag : (Fin (2 ^ n) → Bool) → (Fin (2 ^ (n + 1)) → Bool) :=
    fun tt => pairTruthTable tt tt
  let keyMap : (Fin (2 ^ n) → Bool) → _ :=
    fun tt => Cutwidth.SingleCut.boundaryKey c.program interpretation S (diag tt)
  have hinj : Set.InjOn keyMap exact := by
    intro tt₁ htt₁ tt₂ htt₂ hkey
    have hkey' :
        Cutwidth.SingleCut.boundaryKey c.program interpretation S (diag tt₁) =
          Cutwidth.SingleCut.boundaryKey c.program interpretation S (diag tt₂) := hkey
    have hfwd := Cutwidth.SingleCut.agree_forward_of_boundaryKey_eq hkey'
    have hbwd := Cutwidth.SingleCut.agree_backward_of_boundaryKey_eq hkey'
    have hmix := Cutwidth.SingleCut.trace_mix c.program interpretation hfwd hbwd (c.outputs 0)
    rw [mix_pairTruthTable_of_halfCut hS tt₁ tt₂] at hmix
    have htrace₁ : c.program.trace interpretation (diag tt₁) (c.outputs 0) = true := by
      have h1 := congrFun (hc (diag tt₁)) 0
      simpa [Circuit.eval, mcspCostTarget, diag,
        (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt₁ tt₁).mpr rfl] using h1
    have htrace₂ : c.program.trace interpretation (diag tt₂) (c.outputs 0) = true := by
      have h2 := congrFun (hc (diag tt₂)) 0
      simpa [Circuit.eval, mcspCostTarget, diag,
        (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt₂ tt₂).mpr rfl] using h2
    have htrace_mix :
        c.program.trace interpretation (pairTruthTable tt₁ tt₂) (c.outputs 0) = true := by
      rw [hmix]
      split_ifs <;> assumption
    have hmcsp :
        mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
          (pairTruthTable tt₁ tt₂) = true := by
      have h12 := congrFun (hc (pairTruthTable tt₁ tt₂)) 0
      simpa [Circuit.eval, mcspCostTarget, htrace_mix] using h12.symm
    exact (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt₂ tt₁).mp hmcsp
  have hcard_eq : (exact.image keyMap).card = exact.card :=
    Finset.card_image_of_injOn hinj
  have himage_eq :
      exact.image keyMap =
        (exact.image diag).image (Cutwidth.SingleCut.boundaryKey c.program interpretation S) := by
    rw [Finset.image_image]
    rfl
  calc
    exact.card = (exact.image keyMap).card := hcard_eq.symm
    _ = ((exact.image diag).image
          (Cutwidth.SingleCut.boundaryKey c.program interpretation S)).card := by
      rw [himage_eq]
    _ ≤ Fintype.card Bool ^ ((Cutwidth.SingleCut.forward c.program S).card +
          (Cutwidth.SingleCut.backward c.program S).card) :=
      Cutwidth.SingleCut.card_image_boundaryKey_le c.program interpretation S (exact.image diag)
    _ = 2 ^ ((Cutwidth.SingleCut.forward c.program S).card +
          (Cutwidth.SingleCut.backward c.program S).card) := by
      rw [Fintype.card_bool]

/-! ## Khrapchenko sensitivity, formula, and bounded-sharing circuit lower bounds for MCSP -/

/-- Flipping coordinate `j` (`j.val < 2 ^ n`) of `pairTruthTable tt₀ tt₁` flips coordinate
`⟨j.val, ...⟩` of the left half `tt₀`. -/
theorem flip_pairTruthTable_lt {n : Nat} (tt₀ tt₁ : Fin (2 ^ n) → Bool)
    {j : Fin (2 ^ (n + 1))} (hj : j.val < 2 ^ n) :
    KW.flip (pairTruthTable tt₀ tt₁) j =
      pairTruthTable (KW.flip tt₀ ⟨j.val, hj⟩) tt₁ := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [KW.flip, pairTruthTable, hj]
  · have hval : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    by_cases hi : i.val < 2 ^ n
    · have hne : (⟨i.val, hi⟩ : Fin (2 ^ n)) ≠ ⟨j.val, hj⟩ :=
        fun heq => hval (Fin.mk.inj heq)
      simp [KW.flip, pairTruthTable, hij, hi, hne]
    · simp [KW.flip, pairTruthTable, hij, hi]

/-- Flipping coordinate `j` (`¬ j.val < 2 ^ n`) of `pairTruthTable tt₀ tt₁` flips coordinate
`⟨j.val - 2 ^ n, ...⟩` of the right half `tt₁`. -/
theorem flip_pairTruthTable_ge {n : Nat} (tt₀ tt₁ : Fin (2 ^ n) → Bool)
    {j : Fin (2 ^ (n + 1))} (hj : ¬ j.val < 2 ^ n) :
    KW.flip (pairTruthTable tt₀ tt₁) j =
      pairTruthTable tt₀ (KW.flip tt₁ ⟨j.val - 2 ^ n, by
        have := j.isLt
        have := Nat.pow_succ 2 n
        omega⟩) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [KW.flip, pairTruthTable, hj]
  · have hval : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    by_cases hi : i.val < 2 ^ n
    · simp [KW.flip, pairTruthTable, hij, hi]
    · have hne : (⟨i.val - 2 ^ n, by
          have := i.isLt
          have := Nat.pow_succ 2 n
          omega⟩ : Fin (2 ^ n)) ≠
        ⟨j.val - 2 ^ n, by
          have := j.isLt
          have := Nat.pow_succ 2 n
          omega⟩ := by
        intro heq
        have := Fin.mk.inj heq
        omega
      simp [KW.flip, pairTruthTable, hij, hi, hne]

private theorem flip_ne_self {N : Nat} (x : Fin N → Bool) (i : Fin N) :
    KW.flip x i ≠ x := by
  intro heq
  have := congrFun heq i
  simp [KW.flip] at this

/-- Every diagonal truth table `pairTruthTable tt tt` (`tt ∈ exactCostSet ... n s`, `1 ≤ s`)
has full sensitivity `Finset.univ` (all `2 ^ (n + 1)` coordinates) for `mcspCostScalar`. -/
theorem sensitiveCoordinates_mcsp_pairTruthTable_eq_univ {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s) :
    KW.sensitiveCoordinates
      (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
      (pairTruthTable tt tt) = Finset.univ := by
  ext j
  simp only [KW.sensitiveCoordinates, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  have htrue :
      mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
        (pairTruthTable tt tt) = true :=
    (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt tt).mpr rfl
  rw [htrue]
  by_cases hj : j.val < 2 ^ n
  · rw [flip_pairTruthTable_lt tt tt hj]
    intro heq
    have := (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt (KW.flip tt ⟨j.val, hj⟩)).mp heq
    exact flip_ne_self tt ⟨j.val, hj⟩ this
  · rw [flip_pairTruthTable_ge tt tt hj]
    intro heq
    have := (mcspCostScalar_pairTruthTable_right_eq_true_iff hs htt _).mp heq
    exact flip_ne_self tt _ this

/-- **Khrapchenko bound for MCSP**: Whenever `1 ≤ s` and some truth table `tt` has exact
`DeMorgan.binaryCost` complexity `s`, any Khrapchenko measure bound `M` for
`mcspCostScalar ... (n + 1) s` satisfies `2 ^ (n + 1) ≤ M`. The proof applies the Khrapchenko
inequality to the single `true`-input `pairTruthTable tt tt` and its `2 ^ (n + 1)` one-bit flips,
so the bound is linear in the number `2 ^ (n + 1)` of inputs. -/
theorem khrapchenkoBound_mcsp_lower_bound {n s M : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    (hM : KW.KhrapchenkoBound
      (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) M) :
    2 ^ (n + 1) ≤ M := by
  classical
  let f := mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
  let x := pairTruthTable tt tt
  let A : Finset (Fin (2 ^ (n + 1)) → Bool) := {x}
  let B : Finset (Fin (2 ^ (n + 1)) → Bool) :=
    Finset.univ.image fun j : Fin (2 ^ (n + 1)) => KW.flip x j
  have hA : ∀ a ∈ A, f a = true := by
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt tt).mpr rfl
  have hB : ∀ b ∈ B, f b = false := by
    intro b hb
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    have hsens := sensitiveCoordinates_mcsp_pairTruthTable_eq_univ hs htt
    have hj : j ∈ KW.sensitiveCoordinates f x := by rw [hsens]; exact Finset.mem_univ j
    simp only [KW.sensitiveCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hx : f x = true := hA x (Finset.mem_singleton_self x)
    rw [hx] at hj
    exact Bool.eq_false_iff.mpr hj
  have h1 : ∀ a ∈ A, 2 ^ (n + 1) ≤ (KW.neighbours B a).card := by
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    have hsub : (Finset.univ : Finset (Fin (2 ^ (n + 1)))) ⊆ KW.neighbours B x := by
      intro j _
      simp [KW.neighbours, B]
    simpa using Finset.card_le_card hsub
  have h0 : ∀ b ∈ B, 1 ≤ (KW.neighbours A b).card := by
    intro b hb
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.card_pos.mpr ⟨j, ?_⟩
    have hflip_invol : KW.flip (KW.flip x j) j = x := by
      funext k
      by_cases hk : k = j
      · subst hk; simp [KW.flip]
      · simp [KW.flip, Function.update_of_ne hk]
    simp [KW.neighbours, A, hflip_invol]
  have hB_nonempty : B.Nonempty := ⟨KW.flip x 0, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩
  simpa using KW.mul_le_of_neighbours (hM A B hA hB) ⟨x, Finset.mem_singleton_self x⟩
    hB_nonempty h1 h0

/-- Any De Morgan formula computing
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` (`1 ≤ s`,
`exactCostSet ... n s` nonempty) has at least `2 ^ (n + 1)` leaves. -/
theorem mcsp_formula_leaves_lower_bound {n s : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    {F : KW.Formula (2 ^ (n + 1))}
    (hF : F.Computes (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)) :
    2 ^ (n + 1) ≤ F.leaves :=
  khrapchenkoBound_mcsp_lower_bound hs htt (KW.Formula.khrapchenkoBound hF)

/-- Any De Morgan circuit computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` (`1 ≤ s`,
`exactCostSet ... n s` nonempty) with `sharedGateCount c ≤ k` satisfies
`2 ^ (n + 1) ≤ (k + 1) * (c.cost DeMorgan.binaryCost + k + 1)`. -/
theorem mcsp_sharedGateCount_cost_lower_bound {n s k : Nat} (hs : 1 ≤ s)
    {tt : Fin (2 ^ n) → Bool}
    (htt : tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s)
    (c : Circuit DeMorgan.signature (2 ^ (n + 1)) 1)
    (hc : c.ComputesWith DeMorgan.interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s))
    (hk : KW.sharedGateCount c ≤ k) :
    2 ^ (n + 1) ≤ (k + 1) * (c.cost DeMorgan.binaryCost + k + 1) := by
  obtain ⟨k', P, hk', hP, hgates⟩ := KW.exists_sharedProgram_of_circuit c hc
  have hbound := khrapchenkoBound_mcsp_lower_bound hs htt (KW.SharedProgram.khrapchenkoBound hP)
  have hleaves := P.inputLeaves_le_gates (2 ^ (n + 1))
  calc
    2 ^ (n + 1) ≤ (k' + 1) * P.inputLeaves (2 ^ (n + 1)) := hbound
    _ ≤ (k' + 1) * (P.gates + k' + 1) := Nat.mul_le_mul_left _ hleaves
    _ ≤ (k + 1) * (c.cost DeMorgan.binaryCost + k + 1) :=
      Nat.mul_le_mul (by omega) (by omega)

/-! ## Nechiporuk subfunction and `Binary.Formula` lower bounds for MCSP -/

/-- Embedding of `Fin (2 ^ n)` into the left half (`j.val < 2 ^ n`) of `Fin (2 ^ (n + 1))`. -/
def leftHalfEmbed (n : Nat) : Fin (2 ^ n) ↪ Fin (2 ^ (n + 1)) where
  toFun := fun i => ⟨i.val, by
    have := i.isLt
    have := Nat.pow_succ 2 n
    omega⟩
  inj' := fun _ _ heq => Fin.ext (Fin.mk.inj heq)

/-- Given a subset `Y₀ : Finset (Fin (2 ^ n))` of coordinates in the `n`-bit truth table, its
embedded block in the left half of `Fin (2 ^ (n + 1))` is `Y₀.map (leftHalfEmbed n)`. -/
def leftBlock {n : Nat} (Y₀ : Finset (Fin (2 ^ n))) : Finset (Fin (2 ^ (n + 1))) :=
  Y₀.map (leftHalfEmbed n)

@[simp]
theorem card_leftBlock {n : Nat} (Y₀ : Finset (Fin (2 ^ n))) :
    (leftBlock Y₀).card = Y₀.card :=
  Finset.card_map _

@[simp]
theorem mem_leftBlock_iff {n : Nat} {Y₀ : Finset (Fin (2 ^ n))} {j : Fin (2 ^ (n + 1))} :
    j ∈ leftBlock Y₀ ↔ ∃ h : j.val < 2 ^ n, (⟨j.val, h⟩ : Fin (2 ^ n)) ∈ Y₀ := by
  simp only [leftBlock, Finset.mem_map, leftHalfEmbed]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨⟨j.val, h⟩, hi, Fin.ext rfl⟩

/-- Restriction of a truth table `tt : Fin (2 ^ n) → Bool` to a subset of coordinates
`Y₀ : Finset (Fin (2 ^ n))`. -/
def restrictTo {n : Nat} (Y₀ : Finset (Fin (2 ^ n))) (tt : Fin (2 ^ n) → Bool) :
    ↥Y₀ → Bool :=
  fun i => tt i.val

/-- **Nechiporuk subfunction lower bound for MCSP on arbitrary left-half blocks**:
For `1 ≤ s` and any subset `Y₀ : Finset (Fin (2 ^ n))`, distinct restrictions `restrictTo Y₀ tt`
of truth tables `tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s` induce
distinct subfunctions of `mcspCostScalar ... (n + 1) s` on `leftBlock Y₀`. -/
theorem mcsp_card_image_restrictTo_le_subfunctions_leftBlock {n s : Nat} (hs : 1 ≤ s)
    (Y₀ : Finset (Fin (2 ^ n))) :
    ((exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).image (restrictTo Y₀)).card ≤
      (Nechiporuk.subfunctions
        (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
        (leftBlock Y₀)).card := by
  classical
  let exact := exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s
  let Y := leftBlock Y₀
  let f := mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s
  let outsideOf : (Fin (2 ^ n) → Bool) → (↥Yᶜ → Bool) :=
    fun tt j => pairTruthTable tt tt j.val
  let subfnOf : (Fin (2 ^ n) → Bool) → ((↥Y → Bool) → Bool) :=
    fun tt y => f (Cutwidth.glue Y y (outsideOf tt))
  have hsubfn_mem : ∀ tt, subfnOf tt ∈ Nechiporuk.subfunctions f Y :=
    fun tt => Nechiporuk.restrict_mem_subfunctions f Y (outsideOf tt)
  have hagree :
      ∀ {tt₁ tt₂ : Fin (2 ^ n) → Bool},
        tt₁ ∈ exact → tt₂ ∈ exact → subfnOf tt₁ = subfnOf tt₂ →
        restrictTo Y₀ tt₁ = restrictTo Y₀ tt₂ := by
    intro tt₁ tt₂ htt₁ htt₂ heq
    let y₁ : ↥Y → Bool := fun j => pairTruthTable tt₁ tt₁ j.val
    have hglue₁ : Cutwidth.glue Y y₁ (outsideOf tt₁) = pairTruthTable tt₁ tt₁ :=
      Cutwidth.glue_restrict Y (pairTruthTable tt₁ tt₁)
    have hval₁ : subfnOf tt₁ y₁ = true := by
      dsimp only [subfnOf]
      rw [hglue₁]
      exact (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt₁ tt₁).mpr rfl
    have hval₂ : subfnOf tt₂ y₁ = true := heq ▸ hval₁
    dsimp only [subfnOf] at hval₂
    have hright :
        Cutwidth.glue Y y₁ (outsideOf tt₂) =
          pairTruthTable (leftHalf (Cutwidth.glue Y y₁ (outsideOf tt₂))) tt₂ := by
      conv_lhs => rw [← pairTruthTable_leftHalf_rightHalf (Cutwidth.glue Y y₁ (outsideOf tt₂))]
      congr 1
      funext i
      let j : Fin (2 ^ (n + 1)) := ⟨2 ^ n + i.val, by
        have := i.isLt
        have := Nat.pow_succ 2 n
        omega⟩
      have hj_not_mem : j ∉ Y := by
        rw [mem_leftBlock_iff]
        rintro ⟨hlt, _⟩
        change 2 ^ n + i.val < 2 ^ n at hlt
        omega
      change Cutwidth.glue Y y₁ (outsideOf tt₂) j = tt₂ i
      simp only [Cutwidth.glue, hj_not_mem, ↓reduceDIte]
      change pairTruthTable tt₂ tt₂ j = tt₂ i
      have := rightHalf_pairTruthTable tt₂ tt₂
      exact congrFun this i
    rw [hright] at hval₂
    have hlh_eq : leftHalf (Cutwidth.glue Y y₁ (outsideOf tt₂)) = tt₂ :=
      (mcspCostScalar_pairTruthTable_left_eq_true_iff hs htt₂ _).mp hval₂
    funext ⟨i, hi⟩
    have hi_eq := congrFun hlh_eq i
    have hj_mem : leftHalfEmbed n i ∈ Y := Finset.mem_map_of_mem (leftHalfEmbed n) hi
    have h_lhs :
        leftHalf (Cutwidth.glue Y y₁ (outsideOf tt₂)) i = tt₁ i := by
      change Cutwidth.glue Y y₁ (outsideOf tt₂) (leftHalfEmbed n i) = tt₁ i
      simp only [Cutwidth.glue, hj_mem, ↓reduceDIte]
      change pairTruthTable tt₁ tt₁ (leftHalfEmbed n i) = tt₁ i
      exact congrFun (leftHalf_pairTruthTable tt₁ tt₁) i
    dsimp only [restrictTo]
    exact h_lhs.symm.trans hi_eq
  let toSubfn : ↥(exact.image (restrictTo Y₀)) → ↥(Nechiporuk.subfunctions f Y) :=
    fun r =>
      ⟨subfnOf (Finset.mem_image.mp r.2).choose,
        hsubfn_mem (Finset.mem_image.mp r.2).choose⟩
  have hinj : Function.Injective toSubfn := by
    intro r₁ r₂ heq
    have hval :
        subfnOf (Finset.mem_image.mp r₁.2).choose =
          subfnOf (Finset.mem_image.mp r₂.2).choose :=
      congrArg Subtype.val heq
    have hspec₁ := (Finset.mem_image.mp r₁.2).choose_spec
    have hspec₂ := (Finset.mem_image.mp r₂.2).choose_spec
    have hres := hagree hspec₁.1 hspec₂.1 hval
    exact Subtype.ext (hspec₁.2.symm.trans (hres.trans hspec₂.2))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective toSubfn hinj

/-- **Full-left-half Nechiporuk subfunction lower bound for MCSP**: For `1 ≤ s`, every truth table
`tt ∈ exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s` induces a distinct subfunction
of `mcspCostScalar ... (n + 1) s` on the left-half coordinate block `leftBlock Finset.univ`. -/
theorem mcsp_card_exactCostSet_le_subfunctions_leftHalf {n s : Nat} (hs : 1 ≤ s) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
      (Nechiporuk.subfunctions
        (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
        (leftBlock (Finset.univ : Finset (Fin (2 ^ n))))).card := by
  have hcard :
      ((exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).image
        (restrictTo (Finset.univ : Finset (Fin (2 ^ n))))).card =
      (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card := by
    refine Finset.card_image_of_injective _ ?_
    intro tt₁ tt₂ heq
    funext i
    exact congrFun heq ⟨i, Finset.mem_univ i⟩
  rw [← hcard]
  exact mcsp_card_image_restrictTo_le_subfunctions_leftBlock hs Finset.univ

/-- **Nechiporuk `Binary.Formula` leaf lower bound for MCSP**: For `1 ≤ s`, any binary formula
`F : Binary.Formula (2 ^ (n + 1))` computing
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` satisfies
`((exactCostSet ... n s).image (restrictTo Y₀)).card ≤ 2 * 16 ^ F.leavesIn (leftBlock Y₀)`
for every coordinate subset `Y₀ : Finset (Fin (2 ^ n))`. -/
theorem mcsp_binaryFormula_leavesIn_leftBlock_lower_bound {n s : Nat} (hs : 1 ≤ s)
    (Y₀ : Finset (Fin (2 ^ n)))
    {F : Binary.Formula (2 ^ (n + 1))}
    (hF : F.eval = mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) :
    ((exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).image (restrictTo Y₀)).card ≤
      2 * 16 ^ F.leavesIn (leftBlock Y₀) := by
  calc
    ((exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).image (restrictTo Y₀)).card ≤
        (Nechiporuk.subfunctions
          (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
          (leftBlock Y₀)).card :=
      mcsp_card_image_restrictTo_le_subfunctions_leftBlock hs Y₀
    _ = (Nechiporuk.subfunctions F.eval (leftBlock Y₀)).card := by rw [hF]
    _ ≤ 2 * 16 ^ F.leavesIn (leftBlock Y₀) :=
      Nechiporuk.card_subfunctions_le (leftBlock Y₀) F

/-- **Full-left-half `Binary.Formula` leaf lower bound for MCSP**: For `1 ≤ s`, any binary formula
`F : Binary.Formula (2 ^ (n + 1))` computing
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` satisfies
`(exactCostSet ... n s).card ≤ 2 * 16 ^ F.leavesIn (leftBlock Finset.univ)`. -/
theorem mcsp_binaryFormula_leavesIn_leftHalf_lower_bound {n s : Nat} (hs : 1 ≤ s)
    {F : Binary.Formula (2 ^ (n + 1))}
    (hF : F.eval = mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s) :
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
      2 * 16 ^ F.leavesIn (leftBlock (Finset.univ : Finset (Fin (2 ^ n)))) := by
  calc
    (exactCostSet DeMorgan.interpretation DeMorgan.binaryCost n s).card ≤
        (Nechiporuk.subfunctions
          (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s)
          (leftBlock (Finset.univ : Finset (Fin (2 ^ n))))).card :=
      mcsp_card_exactCostSet_le_subfunctions_leftHalf hs
    _ = (Nechiporuk.subfunctions F.eval (leftBlock Finset.univ)).card := by rw [hF]
    _ ≤ 2 * 16 ^ F.leavesIn (leftBlock Finset.univ) :=
      Nechiporuk.card_subfunctions_le (leftBlock Finset.univ) F

end Algebraic.MCSP

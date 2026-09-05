/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Hadamard

/-!
# Arithmetizing a constraint

The Hadamard tester checks a single quadratic equation over `𝔽₂`. The
constraint it is composed with in Dinur's proof is an arbitrary predicate on a
constant number of bits — the relation of an outer edge, spelled out on the
encodings of the two labels. Two gaps to close, both classical:

* An arbitrary predicate is not one quadratic equation, but it is a *system* of
  them once auxiliary variables are allowed. The system used here is the
  **one-hot** encoding: a selector variable for each candidate assignment,
  constrained to have exactly one selector set (a linear equation for the sum
  and a quadratic one for each pair), only selectors of satisfying candidates
  allowed, and the input bits equal to the selected candidate.

* A system of equations is checked with one query by taking a **random linear
  combination**: if any equation fails, the combination fails on exactly half
  of the coefficient vectors, because the failing values form a nonzero vector
  and a nonzero vector has odd inner product with half of all vectors.

## Main definitions

- `Complexity.QuadConstraint.combine` — a linear combination of constraints
- `Complexity.oneHotSystem` — the one-hot system for a set of satisfying
  assignments

## Main results

- `Complexity.checkValue_combine` — the check of a combination is the
  combination of the checks
- `Complexity.forall_checkValue_of_prob` — a combination passing on more than
  half the coefficient vectors means every equation passes
- `Complexity.exists_sat_oneHotSystem`, `Complexity.mem_of_sat_oneHotSystem`
  — the one-hot system is satisfiable exactly on the given set
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

variable {n : ℕ}

/-! ### Linearity of the Hadamard table -/

/-- Reading a Hadamard table at a sum of vectors. -/
theorem hadamard_add_arg (a x y : Cube n) :
    hadamard a (x + y) = hadamard a x + hadamard a y := by
  show ∑ i, a i * (x i + y i) = (∑ i, a i * x i) + (∑ i, a i * y i)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Reading a Hadamard table at a scalar multiple. -/
theorem hadamard_smul_arg (a : Cube n) (c : ZMod 2) (x : Cube n) :
    hadamard a (fun i => c * x i) = c * hadamard a x := by
  show ∑ i, a i * (c * x i) = c * ∑ i, a i * x i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Reading a Hadamard table at a finite sum of scaled vectors. -/
theorem hadamard_sum_smul {J : ℕ} (a : Cube n) (c : Cube J) (v : Fin J → Cube n) :
    hadamard a (fun i => ∑ j, c j * v j i) = ∑ j, c j * hadamard a (v j) := by
  show ∑ i, a i * ∑ j, c j * v j i = ∑ j, c j * ∑ i, a i * v j i
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Random linear combinations -/

/-- A linear combination of constraints with coefficients `c`. -/
def QuadConstraint.combine {J : ℕ} (C : Fin J → QuadConstraint n) (c : Cube J) :
    QuadConstraint n where
  quad := fun p => ∑ j, c j * (C j).quad p
  lin := fun i => ∑ j, c j * (C j).lin i
  const := ∑ j, c j * (C j).const

/-- **The check of a combination is the combination of the checks**, when the
tables are Hadamard codewords (so linear). -/
theorem checkValue_combine {J : ℕ} (a : Cube n) (b : Cube (n * n))
    (C : Fin J → QuadConstraint n) (c : Cube J) :
    checkValue (hadamard b) (hadamard a) (QuadConstraint.combine C c)
      = hadamard (fun j => checkValue (hadamard b) (hadamard a) (C j)) c := by
  show hadamard b (fun p => ∑ j, c j * (C j).quad p) + hadamard a (fun i => ∑ j, c j * (C j).lin i)
      + ∑ j, c j * (C j).const
    = ∑ j, (hadamard b (C j).quad + hadamard a (C j).lin + (C j).const) * c j
  rw [hadamard_sum_smul, hadamard_sum_smul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Rigidity of the combination.** If the combined check passes on more than
half of the coefficient vectors, every constraint's check passes. -/
theorem forall_checkValue_of_prob {J : ℕ} (a : Cube n) (b : Cube (n * n))
    (C : Fin J → QuadConstraint n)
    (h : 1 / 2 < Pr[fun c : Cube J =>
      checkValue (hadamard b) (hadamard a) (QuadConstraint.combine C c) = 0]) :
    ∀ j, checkValue (hadamard b) (hadamard a) (C j) = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hcon
  have hv : (fun j => checkValue (hadamard b) (hadamard a) (C j)) ≠ 0 := by
    intro h0
    exact hj (congrFun h0 j)
  have hhalf := prob_hadamard_ne_zero _ hv
  have hrw : (fun c : Cube J =>
      checkValue (hadamard b) (hadamard a) (QuadConstraint.combine C c) = 0)
      = fun c : Cube J =>
        ¬ (hadamard (fun j => checkValue (hadamard b) (hadamard a) (C j)) c ≠ 0) := by
    funext c
    rw [checkValue_combine]
    exact propext not_not.symm
  rw [hrw] at h
  have hcompl := BooleanAnalysis.Internal.prob_compl
    (fun c : Cube J => hadamard (fun j => checkValue (hadamard b) (hadamard a) (C j)) c ≠ 0)
  linarith

/-- The combination of constraints satisfied by `a` is satisfied by `a`. -/
theorem QuadConstraint.sat_combine {J : ℕ} (C : Fin J → QuadConstraint n) (a : Cube n)
    (h : ∀ j, (C j).Sat a) (c : Cube J) : (QuadConstraint.combine C c).Sat a := by
  show hadamard (tensorAssign a) (fun p => ∑ j, c j * (C j).quad p)
    + hadamard a (fun i => ∑ j, c j * (C j).lin i) + ∑ j, c j * (C j).const = 0
  rw [hadamard_sum_smul, hadamard_sum_smul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj : hadamard (tensorAssign a) (C j).quad + hadamard a (C j).lin + (C j).const = 0 :=
    h j
  calc c j * hadamard (tensorAssign a) (C j).quad + c j * hadamard a (C j).lin
        + c j * (C j).const
      = c j * (hadamard (tensorAssign a) (C j).quad + hadamard a (C j).lin + (C j).const) := by
        ring
    _ = 0 := by rw [hj, mul_zero]

/-! ### Reading a table at an appended vector -/

/-- Reading at an appended vector reads the two blocks separately. -/
theorem hadamard_append {k t : ℕ} (a : Cube (k + t)) (u : Cube k) (v : Cube t) :
    hadamard a (Fin.append u v) = hadamard (leftBlock a) u + hadamard (rightBlock a) v := by
  show ∑ i : Fin (k + t), a i * (Fin.append u v) i
    = (∑ i : Fin k, a (Fin.castAdd t i) * u i) + ∑ j : Fin t, a (Fin.natAdd k j) * v j
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by rw [Fin.append_right]

theorem hadamard_zero_arg (a : Cube n) : hadamard a 0 = 0 := by
  show ∑ i, a i * (0 : ZMod 2) = 0
  simp

theorem hadamard_tensorAssign_basisVec (a : Cube n) (u v : Fin n) :
    hadamard (tensorAssign a) (basisVec (finProdFinEquiv (u, v))) = a u * a v := by
  rw [hadamard_basisVec]
  show a (finProdFinEquiv.symm (finProdFinEquiv (u, v))).1
    * a (finProdFinEquiv.symm (finProdFinEquiv (u, v))).2 = a u * a v
  rw [Equiv.symm_apply_apply]

/-! ### The one-hot system -/

/-- Candidate assignments, numbered. -/
noncomputable def candIdx (k : ℕ) : Cube k ≃ Fin (2 ^ k) :=
  Fintype.equivFinOfCardEq (card_cube k)

/-- The selector variable of candidate number `m`. -/
def auxVar (k : ℕ) (m : Fin (2 ^ k)) : Fin (k + 2 ^ k) := Fin.natAdd k m

/-- The trivial constraint `0 = 0`. -/
def QuadConstraint.trivial (n : ℕ) : QuadConstraint n := ⟨0, 0, 0⟩

theorem QuadConstraint.sat_trivial (a : Cube n) : (QuadConstraint.trivial n).Sat a := by
  show hadamard (tensorAssign a) 0 + hadamard a 0 + 0 = 0
  rw [hadamard_zero_arg, hadamard_zero_arg]
  simp

/-- The index set of the one-hot system: the sum constraint, a constraint per
pair of candidates, a constraint per candidate, and a constraint per input
coordinate. -/
abbrev OneHotIdx (k : ℕ) : Type :=
  Unit ⊕ ((Fin (2 ^ k) × Fin (2 ^ k)) ⊕ (Fin (2 ^ k) ⊕ Fin k))

/-- The constraints of the one-hot system for the satisfying set `S`. -/
noncomputable def oneHotOf {k : ℕ} (S : Finset (Cube k)) : OneHotIdx k → QuadConstraint (k + 2 ^ k)
  | Sum.inl () => ⟨0, Fin.append 0 (fun _ => 1), 1⟩
  | Sum.inr (Sum.inl (m, m')) =>
      if m = m' then QuadConstraint.trivial _
      else ⟨basisVec (finProdFinEquiv (auxVar k m, auxVar k m')), 0, 0⟩
  | Sum.inr (Sum.inr (Sum.inl m)) =>
      if (candIdx k).symm m ∈ S then QuadConstraint.trivial _
      else ⟨0, basisVec (auxVar k m), 0⟩
  | Sum.inr (Sum.inr (Sum.inr i)) =>
      ⟨0, Fin.append (basisVec i) (fun m => ((candIdx k).symm m) i), 0⟩

/-- **The one-hot system**, as a `Fin`-indexed family for `combine`. -/
noncomputable def oneHotSystem {k : ℕ} (S : Finset (Cube k)) :
    Fin (Fintype.card (OneHotIdx k)) → QuadConstraint (k + 2 ^ k) :=
  fun j => oneHotOf S ((Fintype.equivFin (OneHotIdx k)).symm j)

theorem forall_oneHotSystem_iff {k : ℕ} (S : Finset (Cube k)) (a : Cube (k + 2 ^ k)) :
    (∀ j, (oneHotSystem S j).Sat a) ↔ ∀ x, (oneHotOf S x).Sat a := by
  constructor
  · intro h x
    have := h (Fintype.equivFin (OneHotIdx k) x)
    simpa [oneHotSystem] using this
  · intro h j
    exact h _

/-! #### Evaluating the constraints -/

theorem sat_oneHot_sum_iff {k : ℕ} (S : Finset (Cube k)) (a : Cube (k + 2 ^ k)) :
    (oneHotOf S (Sum.inl ())).Sat a ↔ ∑ m, rightBlock a m = 1 := by
  show hadamard (tensorAssign a) 0 + hadamard a (Fin.append 0 (fun _ => 1)) + 1 = 0 ↔ _
  rw [hadamard_zero_arg, hadamard_append, hadamard_zero_arg]
  have h : hadamard (rightBlock a) (fun _ => 1) = ∑ m, rightBlock a m := by
    show ∑ m, rightBlock a m * 1 = _
    simp
  rw [h]
  rcases (by decide : ∀ u : ZMod 2, (0 + (0 + u) + 1 = 0) ↔ (u = 1)) (∑ m, rightBlock a m)
    with h'
  exact h'

theorem sat_oneHot_pair_iff {k : ℕ} (S : Finset (Cube k)) (a : Cube (k + 2 ^ k))
    (m m' : Fin (2 ^ k)) (hne : m ≠ m') :
    (oneHotOf S (Sum.inr (Sum.inl (m, m')))).Sat a ↔ rightBlock a m * rightBlock a m' = 0 := by
  unfold QuadConstraint.Sat QuadConstraint.eval
  simp only [oneHotOf, ite_eq_right hne]
  rw [hadamard_tensorAssign_basisVec, hadamard_zero_arg, add_zero, add_zero]
  rfl

theorem sat_oneHot_allowed_iff {k : ℕ} (S : Finset (Cube k)) (a : Cube (k + 2 ^ k))
    (m : Fin (2 ^ k)) (hm : (candIdx k).symm m ∉ S) :
    (oneHotOf S (Sum.inr (Sum.inr (Sum.inl m)))).Sat a ↔ rightBlock a m = 0 := by
  unfold QuadConstraint.Sat QuadConstraint.eval
  simp only [oneHotOf, ite_eq_right hm]
  rw [hadamard_zero_arg, hadamard_basisVec, zero_add, add_zero]
  rfl

theorem sat_oneHot_coord_iff {k : ℕ} (S : Finset (Cube k)) (a : Cube (k + 2 ^ k)) (i : Fin k) :
    (oneHotOf S (Sum.inr (Sum.inr (Sum.inr i)))).Sat a
      ↔ leftBlock a i + ∑ m, rightBlock a m * ((candIdx k).symm m) i = 0 := by
  show hadamard (tensorAssign a) 0
    + hadamard a (Fin.append (basisVec i) (fun m => ((candIdx k).symm m) i)) + 0 = 0 ↔ _
  rw [hadamard_zero_arg, hadamard_append, hadamard_basisVec, zero_add, add_zero]
  rfl

/-! #### Exactly one selector -/

/-- A `0`/`1` vector with odd sum and pairwise zero products is a basis vector. -/
theorem eq_basis_of_sum_one {T : ℕ} (y : Fin T → ZMod 2) (hsum : ∑ m, y m = 1)
    (hpair : ∀ m m', m ≠ m' → y m * y m' = 0) :
    ∃ m₀, y m₀ = 1 ∧ ∀ m, m ≠ m₀ → y m = 0 := by
  classical
  have hex : ∃ m₀, y m₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∑ m, y m = 0 := Finset.sum_eq_zero fun m _ => hcon m
    rw [this] at hsum
    exact absurd hsum (by decide)
  obtain ⟨m₀, hm₀⟩ := hex
  have hone : y m₀ = 1 := by
    rcases (by decide : ∀ u : ZMod 2, u ≠ 0 → u = 1) (y m₀) hm₀ with h
    exact h
  refine ⟨m₀, hone, fun m hm => ?_⟩
  have := hpair m m₀ hm
  rw [hone, mul_one] at this
  exact this

/-! #### The characterization -/

/-- **Satisfying the one-hot system puts the input in the set.** -/
theorem mem_of_sat_oneHotSystem {k : ℕ} (S : Finset (Cube k)) (a : Cube (k + 2 ^ k))
    (h : ∀ j, (oneHotSystem S j).Sat a) : leftBlock a ∈ S := by
  classical
  rw [forall_oneHotSystem_iff] at h
  have hsum := (sat_oneHot_sum_iff S a).1 (h (Sum.inl ()))
  obtain ⟨m₀, hm₀, hother⟩ := eq_basis_of_sum_one (rightBlock a) hsum
    fun m m' hne => (sat_oneHot_pair_iff S a m m' hne).1 (h _)
  have hmem : (candIdx k).symm m₀ ∈ S := by
    by_contra hnot
    have := (sat_oneHot_allowed_iff S a m₀ hnot).1 (h _)
    rw [hm₀] at this
    exact absurd this (by decide)
  have hw : leftBlock a = (candIdx k).symm m₀ := by
    funext i
    have hc := (sat_oneHot_coord_iff S a i).1 (h _)
    rw [Finset.sum_eq_single m₀ (fun m _ hm => by rw [hother m hm, zero_mul])
      (fun hn => absurd (Finset.mem_univ m₀) hn), hm₀, one_mul] at hc
    rcases (by decide : ∀ u v : ZMod 2, u + v = 0 → u = v) _ _ hc with h'
    exact h'
  rw [hw]
  exact hmem

/-- The honest extension of an input: select its own candidate. -/
noncomputable def oneHotExtend {k : ℕ} (w : Cube k) : Cube (k + 2 ^ k) :=
  Fin.append w (fun m => if m = candIdx k w then 1 else 0)

theorem leftBlock_oneHotExtend {k : ℕ} (w : Cube k) : leftBlock (oneHotExtend w) = w := by
  funext i
  unfold leftBlock oneHotExtend
  rw [Fin.append_left]

theorem rightBlock_oneHotExtend {k : ℕ} (w : Cube k) (m : Fin (2 ^ k)) :
    rightBlock (oneHotExtend w) m = if m = candIdx k w then 1 else 0 := by
  unfold rightBlock oneHotExtend
  rw [Fin.append_right]

/-- **An input in the set satisfies the one-hot system**, once extended by its
own selector. -/
theorem sat_oneHotSystem_extend {k : ℕ} (S : Finset (Cube k)) (w : Cube k) (hw : w ∈ S) :
    ∀ j, (oneHotSystem S j).Sat (oneHotExtend w) := by
  classical
  rw [forall_oneHotSystem_iff]
  intro x
  rcases x with _ | ⟨⟨m, m'⟩ | m | i⟩
  · rw [sat_oneHot_sum_iff]
    rw [Finset.sum_eq_single (candIdx k w)
      (fun m _ hm => by rw [rightBlock_oneHotExtend, ite_eq_right hm])
      (fun hn => absurd (Finset.mem_univ _) hn), rightBlock_oneHotExtend, ite_eq_left rfl]
  · by_cases hne : m = m'
    · simp only [oneHotOf, ite_eq_left hne]
      exact QuadConstraint.sat_trivial _
    · rw [sat_oneHot_pair_iff S _ m m' hne, rightBlock_oneHotExtend, rightBlock_oneHotExtend]
      by_cases hm : m = candIdx k w
      · have hm' : m' ≠ candIdx k w := fun h => hne (hm.trans h.symm)
        rw [ite_eq_right hm', mul_zero]
      · rw [ite_eq_right hm, zero_mul]
  · by_cases hm : (candIdx k).symm m ∈ S
    · simp only [oneHotOf, ite_eq_left hm]
      exact QuadConstraint.sat_trivial _
    · rw [sat_oneHot_allowed_iff S _ m hm, rightBlock_oneHotExtend, ite_eq_right]
      intro hmw
      apply hm
      rw [hmw, Equiv.symm_apply_apply]
      exact hw
  · rw [sat_oneHot_coord_iff, leftBlock_oneHotExtend]
    rw [Finset.sum_eq_single (candIdx k w)
      (fun m _ hm => by rw [rightBlock_oneHotExtend, ite_eq_right hm, zero_mul])
      (fun hn => absurd (Finset.mem_univ _) hn), rightBlock_oneHotExtend, ite_eq_left rfl,
      one_mul, Equiv.symm_apply_apply]
    rcases (by decide : ∀ u : ZMod 2, u + u = 0) (w i) with h'
    exact h'

/-- **The one-hot system is satisfiable exactly on the set.** -/
theorem exists_sat_oneHotSystem_iff {k : ℕ} (S : Finset (Cube k)) (w : Cube k) :
    (∃ a : Cube (k + 2 ^ k), leftBlock a = w ∧ ∀ j, (oneHotSystem S j).Sat a) ↔ w ∈ S := by
  constructor
  · rintro ⟨a, ha, hsat⟩
    rw [← ha]
    exact mem_of_sat_oneHotSystem S a hsat
  · intro hw
    exact ⟨oneHotExtend w, leftBlock_oneHotExtend w, sat_oneHotSystem_extend S w hw⟩

end Complexity

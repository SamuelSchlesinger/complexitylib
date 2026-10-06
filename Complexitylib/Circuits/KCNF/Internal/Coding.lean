/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# The satisfiability coding lemma -- proofs

Internal proofs for `Complexitylib.Circuits.KCNF.Coding`.

On a solution `x` of `ψ`, the decoder for the order `σ` recovers `x` from every input `y` that
agrees with `x` off the forced variables (`decode_eq_of_agree`). So the sets of such inputs are
disjoint for distinct solutions, and the sum of `2 ^ |forced σ x|` over the solutions is at most
`2 ^ N`. Averaging over all orders and applying Jensen's inequality to `t ↦ 2 ^ t` gives the
bound with the average number of forced variables in the exponent.

For a clause set of width `k`, every isolated direction `i` of a solution `x` has a clause whose
only true literal under `x` is on `i`; then `i` is forced whenever `σ` places `i` after the other
variables of that clause, which happens for at least a `1/k` fraction of the orders
(`card_lastIn_mul_card`).
-/

@[expose] public section

namespace Complexity

open Finset

variable {N : ℕ}

namespace ClauseSet

namespace Coding

/-- In a satisfied clause whose other literals are false, the remaining literal is true. -/
theorem eval_eq_true_of_others_false {C : Finset (Literal N)} {x : BitString N}
    (hsat : ∃ l ∈ C, l.eval x = true) {l : Literal N}
    (hothers : ∀ l' ∈ C, l' ≠ l → l'.eval x = false) : l.eval x = true := by
  obtain ⟨l'', hl'', htrue⟩ := hsat
  by_cases h : l'' = l
  · exact h ▸ htrue
  · simp [hothers l'' hl'' h] at htrue

/-- The firing condition only reads the variables placed before `v`. -/
theorem fires_congr {σ : Equiv.Perm (Fin N)} {z x : BitString N} {v : Fin N}
    (hzx : ∀ u, σ u < σ v → z u = x u) (C : Finset (Literal N)) (l : Literal N) :
    (∀ l' ∈ C, l' ≠ l → σ l'.var < σ v ∧ l'.eval z = false) ↔
      (∀ l' ∈ C, l' ≠ l → σ l'.var < σ v ∧ l'.eval x = false) := by
  refine forall₂_congr fun l' _ => imp_congr_right fun _ => and_congr_right fun hlt => ?_
  simp only [Literal.eval, hzx _ hlt]

/-- One decoding step: on a partial assignment that agrees with the solution `x` before `v`, and
with an input bit that is `x v` unless `v` is forced, the decoder gives `v` its value in `x`. -/
theorem decodeValue_eq {ψ : ClauseSet N} {σ : Equiv.Perm (Fin N)} {x z : BitString N}
    {v : Fin N} {b : Bool} (hx : ψ.Sat x) (hzx : ∀ u, σ u < σ v → z u = x u)
    (hb : v ∉ ψ.forced σ x → b = x v) : ψ.decodeValue σ z v b = x v := by
  unfold decodeValue
  simp_rw [fires_congr hzx]
  split_ifs with hfire
  · obtain ⟨C, hC, l, hl, hvar, hothers⟩ := hfire
    have hlx : l.eval x = true :=
      eval_eq_true_of_others_false (hx C hC) fun l' hl' hne => (hothers l' hl' hne).2
    rw [Literal.eval_eq_true_iff, hvar] at hlx
    rw [hlx]
    cases hpol : l.polarity
    · rw [decide_eq_false_iff_not]
      rintro ⟨C', hC', l', hl', hvar', hpol', hothers'⟩
      have hl'x : l'.eval x = true :=
        eval_eq_true_of_others_false (hx C' hC') fun l'' hl'' hne => (hothers' l'' hl'' hne).2
      rw [Literal.eval_eq_true_iff, hvar', hpol'] at hl'x
      rw [hlx, hpol] at hl'x
      exact Bool.false_ne_true hl'x
    · rw [decide_eq_true_iff]
      exact ⟨C, hC, l, hl, hvar, hpol, hothers⟩
  · exact hb fun hmem => hfire (mem_forced.mp hmem)

/-- **The decoder invariant.** After `p` positions, the decoder holds the solution's values at
the positions before `p` and the input's values elsewhere. -/
theorem decodeUpTo_eq {ψ : ClauseSet N} {σ : Equiv.Perm (Fin N)} {x y : BitString N}
    (hx : ψ.Sat x) (hy : ∀ v ∉ ψ.forced σ x, y v = x v) :
    ∀ p ≤ N, ∀ v, ψ.decodeUpTo σ y p v = if (σ v : ℕ) < p then x v else y v := by
  intro p
  induction p with
  | zero => intro _ v; simp [decodeUpTo]
  | succ p ih =>
    intro hp v
    have hpN : p < N := hp
    have ih' := ih hpN.le
    simp only [decodeUpTo, hpN, dite_true]
    set v₀ := σ.symm ⟨p, hpN⟩ with hv₀
    have hσv₀ : σ v₀ = ⟨p, hpN⟩ := by simp [hv₀]
    by_cases hv : v = v₀
    · subst hv
      rw [Function.update_self, hσv₀]
      simp only [Nat.lt_succ_self, ite_true]
      refine decodeValue_eq hx (fun u hu => ?_) (hy v₀)
      rw [ih' u, ite_eq_left (by rw [hσv₀] at hu; exact hu)]
    · rw [Function.update_of_ne hv, ih' v]
      have hne : (σ v : ℕ) ≠ p := by
        intro h
        apply hv
        apply σ.injective
        rw [hσv₀]
        exact Fin.ext h
      by_cases hlt : (σ v : ℕ) < p
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have : ¬ (σ v : ℕ) < p + 1 := by omega
        simp [hlt, this]

/-- **Decoding.** On every input that agrees with a solution `x` off its forced variables, the
decoder outputs `x`. -/
theorem decode_eq_of_agree {ψ : ClauseSet N} {σ : Equiv.Perm (Fin N)} {x y : BitString N}
    (hx : ψ.Sat x) (hy : ∀ v ∉ ψ.forced σ x, y v = x v) : ψ.decode σ y = x := by
  funext v
  rw [decode, decodeUpTo_eq hx hy N le_rfl v, ite_eq_left (σ v).isLt]

/-- **The coding bound for one order.** -/
theorem sum_two_pow_forced_le (ψ : ClauseSet N) (σ : Equiv.Perm (Fin N)) :
    ∑ x ∈ ψ.solutions, 2 ^ (ψ.forced σ x).card ≤ 2 ^ N := by
  let B : BitString N → Finset (BitString N) := fun x =>
    univ.filter fun y => ∀ v ∉ ψ.forced σ x, y v = x v
  have hdisj : (ψ.solutions : Set (BitString N)).PairwiseDisjoint B := by
    intro x hx x' hx' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    simp only [B, mem_filter, mem_univ, true_and] at hy hy'
    have h := decode_eq_of_agree (mem_solutions.mp hx) hy
    rw [decode_eq_of_agree (mem_solutions.mp hx') hy'] at h
    exact hne h.symm
  calc ∑ x ∈ ψ.solutions, 2 ^ (ψ.forced σ x).card
      = ∑ x ∈ ψ.solutions, (B x).card := by
        refine sum_congr rfl fun x _ => ?_
        rw [BitString.card_filter_agree]
    _ = (ψ.solutions.biUnion B).card := (card_biUnion hdisj).symm
    _ ≤ (univ : Finset (BitString N)).card := card_le_univ _
    _ = 2 ^ N := by simp

/-- **The coding bound, averaged over all orders.** With the average number of forced variables
in the exponent, the sum over the solutions is at most `2 ^ N` (Jensen's inequality). -/
theorem sum_two_rpow_average_forced_le (ψ : ClauseSet N) :
    ∑ x ∈ ψ.solutions,
        (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((ψ.forced σ x).card : ℝ)) / N.factorial) ≤
      2 ^ N := by
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin N))).card = N.factorial := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
  have hjensen : ∀ x : BitString N,
      (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((ψ.forced σ x).card : ℝ)) / N.factorial) ≤
        ∑ σ : Equiv.Perm (Fin N), (1 / N.factorial : ℝ) * 2 ^ (ψ.forced σ x).card := by
    intro x
    have h := (convexOn_rpow_left (b := 2) (by norm_num)).map_sum_le
      (t := (Finset.univ : Finset (Equiv.Perm (Fin N))))
      (w := fun _ => (1 / N.factorial : ℝ)) (p := fun σ => ((ψ.forced σ x).card : ℝ))
      (fun _ _ => by positivity) (by rw [sum_const, hcard, nsmul_eq_mul]; field_simp)
      (fun _ _ => trivial)
    simp only [smul_eq_mul, Real.rpow_natCast] at h
    convert h using 2
    rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
  calc ∑ x ∈ ψ.solutions,
        (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((ψ.forced σ x).card : ℝ)) / N.factorial)
      ≤ ∑ x ∈ ψ.solutions,
          ∑ σ : Equiv.Perm (Fin N), (1 / N.factorial : ℝ) * 2 ^ (ψ.forced σ x).card :=
        sum_le_sum fun x _ => hjensen x
    _ = (1 / N.factorial : ℝ) *
          ∑ σ : Equiv.Perm (Fin N), ∑ x ∈ ψ.solutions, (2 : ℝ) ^ (ψ.forced σ x).card := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine sum_congr rfl fun σ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (1 / N.factorial : ℝ) * ∑ _σ : Equiv.Perm (Fin N), (2 : ℝ) ^ N := by
        gcongr with σ
        exact_mod_cast sum_two_pow_forced_le ψ σ
    _ = 2 ^ N := by
        rw [sum_const, hcard, nsmul_eq_mul]
        field_simp

/-! ### Isolated directions are forced often -/

/-- The orders that place `j` after every other element of `V`. -/
def lastIn (V : Finset (Fin N)) (j : Fin N) : Finset (Equiv.Perm (Fin N)) :=
  univ.filter fun σ => ∀ u ∈ V, u ≠ j → σ u < σ j

theorem card_lastIn_eq {V : Finset (Fin N)} {i j : Fin N} (hi : i ∈ V) (hj : j ∈ V) :
    (lastIn V j).card = (lastIn V i).card := by
  refine card_nbij' (fun σ => σ * Equiv.swap i j) (fun σ => σ * Equiv.swap i j)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_coe, lastIn, mem_filter, mem_univ, true_and] at hσ ⊢
    intro u hu hne
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
    by_cases huj : u = j
    · rw [huj, Equiv.swap_apply_right]
      exact hσ i hi fun h => hne (huj.trans h.symm)
    · rw [Equiv.swap_apply_of_ne_of_ne hne huj]
      exact hσ u hu huj
  · intro σ hσ
    simp only [mem_coe, lastIn, mem_filter, mem_univ, true_and] at hσ ⊢
    intro u hu hne
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_right]
    by_cases hui : u = i
    · rw [hui, Equiv.swap_apply_left]
      exact hσ j hj fun h => hne (hui.trans h.symm)
    · rw [Equiv.swap_apply_of_ne_of_ne hui hne]
      exact hσ u hu hui
  · intro σ _
    simp [mul_assoc]
  · intro σ _
    simp [mul_assoc]

/-- **Symmetry of orders.** Exactly a `1/|V|` fraction of the orders place a given element of `V`
after the others. -/
theorem card_lastIn_mul_card {V : Finset (Fin N)} {i : Fin N} (hi : i ∈ V) :
    (lastIn V i).card * V.card = N.factorial := by
  have hdisj : (V : Set (Fin N)).PairwiseDisjoint (lastIn V) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hσ hσ'
    simp only [lastIn, mem_filter, mem_univ, true_and] at hσ hσ'
    exact lt_asymm (hσ j' hj' (Ne.symm hne)) (hσ' j hj hne)
  have hcover : V.biUnion (lastIn V) = univ := by
    refine eq_univ_of_forall fun σ => ?_
    obtain ⟨j, hj, hmax⟩ := V.exists_max_image σ ⟨i, hi⟩
    refine mem_biUnion.mpr ⟨j, hj, ?_⟩
    simp only [lastIn, mem_filter, mem_univ, true_and]
    intro u hu hne
    exact lt_of_le_of_ne (hmax u hu) fun h => hne (σ.injective (Fin.ext (congrArg Fin.val h)))
  have := card_biUnion hdisj
  rw [hcover, card_univ, Fintype.card_perm, Fintype.card_fin] at this
  rw [this, sum_congr rfl fun j hj => card_lastIn_eq hi hj, sum_const, smul_eq_mul, mul_comm]

/-- An isolated direction of a solution has a *critical clause*: a clause whose only true literal
under `x` is a literal on that direction. -/
theorem exists_critical_clause {ψ : ClauseSet N} {x : BitString N} {i : Fin N}
    (hx : ψ.Sat x) (hi : i ∈ isolatedDirections ψ.solutions x) :
    ∃ C ∈ ψ, ∃ l ∈ C, l.var = i ∧ ∀ l' ∈ C, l' ≠ l → l'.var ≠ i ∧ l'.eval x = false := by
  simp only [isolatedDirections, mem_filter, mem_univ, true_and, mem_solutions, Sat,
    not_forall, not_exists, not_and] at hi
  obtain ⟨C, hC, hfalse⟩ := hi
  have hflip : ∀ l ∈ C, l.eval (x.flipOn {i}) = false := fun l hl => by
    simpa using hfalse l hl
  have hsame : ∀ l ∈ C, l.var ≠ i → l.eval x = false := by
    intro l hl hne
    have h1 := hflip l hl
    have h2 : x.flipOn {i} l.var = x l.var :=
      BitString.flipOn_apply_of_not_mem (by simpa using hne)
    unfold Literal.eval at h1 ⊢
    rw [h2] at h1
    exact h1
  obtain ⟨l, hl, htrue⟩ := hx C hC
  have hvar : l.var = i := by
    by_contra hne
    simp [hsame l hl hne] at htrue
  refine ⟨C, hC, l, hl, hvar, fun l' hl' hne => ?_⟩
  by_cases hvar' : l'.var = i
  · exfalso
    have hflip' := hflip l' hl'
    have hl'x : l'.eval x = true := by
      have : (x.flipOn {i}) l'.var = !x l'.var := by
        rw [hvar']; exact BitString.flipOn_apply_of_mem (mem_singleton_self i)
      cases hp : l'.polarity <;>
        simp_all [Literal.eval]
    exact hne (Literal.eq_of_eval_eq_true (hvar'.trans hvar.symm) hl'x htrue)
  · exact ⟨hvar', hsame l' hl' hvar'⟩

/-- **Isolated directions are forced on average.** For a clause set of width at most `k`, the
number of isolated directions of a solution times `N!` is at most `k` times the total number of
forced variables over all orders. -/
theorem card_isolated_mul_factorial_le {ψ : ClauseSet N} {k : ℕ}
    (hk : ∀ C ∈ ψ, C.card ≤ k) {x : BitString N} (hx : ψ.Sat x) :
    (isolatedDirections ψ.solutions x).card * N.factorial ≤
      k * ∑ σ : Equiv.Perm (Fin N), (ψ.forced σ x).card := by
  classical
  have hcrit := fun i (hi : i ∈ isolatedDirections ψ.solutions x) =>
    exists_critical_clause hx hi
  choose C hC l hl hvar hothers using hcrit
  -- each isolated direction is forced in a `1/k` fraction of the orders
  have hlast : ∀ i (hi : i ∈ isolatedDirections ψ.solutions x),
      N.factorial ≤ k * (lastIn ((C i hi).image Literal.var) i).card := by
    intro i hi
    have hmem : i ∈ (C i hi).image Literal.var := mem_image.mpr ⟨l i hi, hl i hi, hvar i hi⟩
    rw [← card_lastIn_mul_card hmem, mul_comm]
    exact Nat.mul_le_mul_right _ (card_image_le.trans (hk _ (hC i hi)))
  have hsub : ∀ i (hi : i ∈ isolatedDirections ψ.solutions x),
      lastIn ((C i hi).image Literal.var) i ⊆ univ.filter fun σ => i ∈ ψ.forced σ x := by
    intro i hi σ hσ
    simp only [lastIn, mem_filter, mem_univ, true_and, mem_image] at hσ ⊢
    refine mem_forced.mpr ⟨C i hi, hC i hi, l i hi, hl i hi, hvar i hi, fun l' hl' hne => ?_⟩
    obtain ⟨hne', hfalse⟩ := hothers i hi l' hl' hne
    exact ⟨hσ l'.var ⟨l', hl', rfl⟩ hne', hfalse⟩
  have hswap : ∑ σ : Equiv.Perm (Fin N), (ψ.forced σ x).card =
      ∑ i : Fin N, (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ ψ.forced σ x).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun σ _ => ?_
    rw [← sum_filter]
    congr 1
    ext i; simp
  rw [hswap, Finset.mul_sum]
  calc (isolatedDirections ψ.solutions x).card * N.factorial
      = ∑ i ∈ isolatedDirections ψ.solutions x, N.factorial := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ i ∈ (isolatedDirections ψ.solutions x).attach,
          k * (univ.filter fun σ : Equiv.Perm (Fin N) => i.1 ∈ ψ.forced σ x).card := by
        rw [← sum_attach]
        refine sum_le_sum fun i _ => (hlast i.1 i.2).trans ?_
        exact Nat.mul_le_mul_left _ (card_le_card (hsub i.1 i.2))
    _ = ∑ i ∈ isolatedDirections ψ.solutions x,
          k * (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ ψ.forced σ x).card :=
        sum_attach _ (fun i => k * (univ.filter fun σ : Equiv.Perm (Fin N) =>
          i ∈ ψ.forced σ x).card)
    _ ≤ ∑ i : Fin N, k * (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ ψ.forced σ x).card :=
        sum_le_sum_of_subset (subset_univ _)

/-- **The coding lemma for `k`-CNFs.** For a clause set of width at most `k ≥ 1`, the sum over
its solutions of `2 ^ (ι(x)/k)`, `ι(x)` the number of isolated directions, is at most `2 ^ N`. -/
theorem sum_two_rpow_isolated_div_le {ψ : ClauseSet N} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ C ∈ ψ, C.card ≤ k) :
    ∑ x ∈ ψ.solutions,
        (2 : ℝ) ^ (((isolatedDirections ψ.solutions x).card : ℝ) / k) ≤ 2 ^ N := by
  refine le_trans (sum_le_sum fun x hx => ?_) (sum_two_rpow_average_forced_le ψ)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_div_iff₀ hkpos hfact]
  have := card_isolated_mul_factorial_le hk (mem_solutions.mp hx)
  have hcast : ((isolatedDirections ψ.solutions x).card : ℝ) * N.factorial ≤
      k * ∑ σ : Equiv.Perm (Fin N), ((ψ.forced σ x).card : ℝ) := by
    exact_mod_cast this
  linarith

end Coding

end ClauseSet

end Complexity

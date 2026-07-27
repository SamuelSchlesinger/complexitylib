/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Common

/-!
# The `S₅` five-cycle commutator (Barrington's non-solvability input)

Barrington's theorem needs a specific algebraic fact about the symmetric group
`S₅ = Equiv.Perm (Fin 5)`: there are two `5`-cycles whose commutator is again a
`5`-cycle. This is precisely the failure of solvability of `S₅` that lets the
commutator-trick `AND` gate (`Circuits/Barrington.lean`, `BP.Computes_and`) hit a
genuine `5`-cycle target, so the inductive construction can be conjugated to any
desired output cycle.

We exhibit an explicit witness — `a = finRotate 5` and the `5`-cycle
`b = (0 2 4 3 1)` — and verify by kernel computation (`decide`, hence **no**
`native_decide` and no extra axioms) that `a`, `b`, and `⁅a, b⁆` each have order
`5`. Order `5` (a prime) together with a nonidentity element forces a single
cycle via `Equiv.Perm.isCycle_of_prime_order`.

Conjugation upgrades the single witness to *every* `5`-cycle: since the `5`-cycles
form one conjugacy class of `S₅` and conjugation distributes over commutators, any
`5`-cycle is the commutator of two `5`-cycles (`every_fiveCycle_is_commutator`).
That is the form Barrington's induction consumes — it may target an arbitrary
output cycle.

## Main results

- `Complexity.isCycle_orderOf_five_of_pow` — a nonidentity `g : S₅` with `g⁵ = 1`
  is a `5`-cycle of order `5`.
- `Complexity.conj_isCycle_orderOf_five` — a conjugate of a `5`-cycle is a
  `5`-cycle.
- `Complexity.exists_fiveCycle_commutator` — two `5`-cycles of `S₅` whose
  commutator is again a `5`-cycle.
- `Complexity.every_fiveCycle_is_commutator` — *every* `5`-cycle of `S₅` is the
  commutator of two `5`-cycles.
-/

@[expose] public section

open scoped commutatorElement
open Equiv

set_option maxRecDepth 100000

namespace Complexity

/-- A nonidentity permutation of `Fin 5` whose fifth power is the identity is a
    `5`-cycle of order `5`. (Order divides the prime `5` and is not `1`, so it is
    `5`; a prime-order permutation is a single cycle.) -/
theorem isCycle_orderOf_five_of_pow {g : Perm (Fin 5)} (h5 : g ^ 5 = 1) (hne : g ≠ 1) :
    g.IsCycle ∧ orderOf g = 5 := by
  have hp : Nat.Prime 5 := by norm_num
  have hdvd : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hord : orderOf g = 5 := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  refine ⟨?_, hord⟩
  apply Equiv.Perm.isCycle_of_prime_order (by rw [hord]; exact hp)
  have hle : g.support.card ≤ 5 := by simpa using Finset.card_le_univ g.support
  rw [hord]; omega

/-- A conjugate of a `5`-cycle is again a `5`-cycle. (Conjugation preserves both
    `g⁵ = 1` — via the homomorphism `MulAut.conj` — and nonidentity, so
    `isCycle_orderOf_five_of_pow` applies to the conjugate.) -/
theorem conj_isCycle_orderOf_five {a : Perm (Fin 5)} (h : a.IsCycle ∧ orderOf a = 5)
    (g : Perm (Fin 5)) : (g * a * g⁻¹).IsCycle ∧ orderOf (g * a * g⁻¹) = 5 := by
  obtain ⟨_, ho⟩ := h
  have ha5 : a ^ 5 = 1 := by have h := pow_orderOf_eq_one a; rwa [ho] at h
  have h5 : (g * a * g⁻¹) ^ 5 = 1 := by
    have hp := map_pow (MulAut.conj g) a 5
    rw [ha5, map_one, MulAut.conj_apply] at hp
    exact hp.symm
  have hne : g * a * g⁻¹ ≠ 1 := by
    have hane : a ≠ 1 := by rw [Ne, ← orderOf_eq_one_iff, ho]; norm_num
    intro hcon
    apply hane
    have hb : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [hcon] at hb; simpa using hb
  exact isCycle_orderOf_five_of_pow h5 hne

/-- **Barrington's `S₅` input.** There exist two `5`-cycles of `S₅` whose
    commutator is again a `5`-cycle. The explicit witnesses are `finRotate 5` and
    the `5`-cycle `(0 2 4 3 1)`; the order-`5` facts are checked by kernel
    computation. -/
theorem exists_fiveCycle_commutator :
    ∃ a b : Perm (Fin 5),
      a.IsCycle ∧ orderOf a = 5 ∧ b.IsCycle ∧ orderOf b = 5 ∧
      ⁅a, b⁆.IsCycle ∧ orderOf ⁅a, b⁆ = 5 := by
  refine ⟨finRotate 5, ([0, 2, 4, 3, 1] : List (Fin 5)).formPerm, ?_⟩
  obtain ⟨ha, ha'⟩ := isCycle_orderOf_five_of_pow (g := finRotate 5) (by decide) (by decide)
  obtain ⟨hb, hb'⟩ := isCycle_orderOf_five_of_pow
    (g := ([0, 2, 4, 3, 1] : List (Fin 5)).formPerm) (by decide) (by decide)
  obtain ⟨hc, hc'⟩ := isCycle_orderOf_five_of_pow
    (g := ⁅finRotate 5, ([0, 2, 4, 3, 1] : List (Fin 5)).formPerm⁆) (by decide) (by decide)
  exact ⟨ha, ha', hb, hb', hc, hc'⟩

/-- **Every `5`-cycle is a commutator of `5`-cycles.** Combining the single
    witness `exists_fiveCycle_commutator` with the fact that the `5`-cycles form a
    single conjugacy class of `S₅` (equal cycle type ⟹ conjugate) and that
    conjugation distributes over the commutator, any `5`-cycle `c` of `S₅` can be
    written as `⁅a, b⁆` for `5`-cycles `a, b`. This is the target-cycle freedom
    Barrington's `AND` gate needs. -/
theorem every_fiveCycle_is_commutator (c : Perm (Fin 5)) (hc : c.IsCycle)
    (hco : orderOf c = 5) :
    ∃ a b : Perm (Fin 5),
      a.IsCycle ∧ orderOf a = 5 ∧ b.IsCycle ∧ orderOf b = 5 ∧ ⁅a, b⁆ = c := by
  obtain ⟨a₀, b₀, ha₀, ha₀o, hb₀, hb₀o, hcc, hcco⟩ := exists_fiveCycle_commutator
  have hs₀ : (⁅a₀, b₀⁆).support.card = 5 := by rw [← hcc.orderOf]; exact hcco
  have hsc : c.support.card = 5 := by rw [← hc.orderOf]; exact hco
  have hct : (⁅a₀, b₀⁆).cycleType = c.cycleType := by
    rw [hcc.cycleType, hc.cycleType, hs₀, hsc]
  have hconj : IsConj (⁅a₀, b₀⁆) c := Equiv.Perm.isConj_iff_cycleType_eq.mpr hct
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨haC, haO⟩ := conj_isCycle_orderOf_five ⟨ha₀, ha₀o⟩ g
  obtain ⟨hbC, hbO⟩ := conj_isCycle_orderOf_five ⟨hb₀, hb₀o⟩ g
  refine ⟨g * a₀ * g⁻¹, g * b₀ * g⁻¹, haC, haO, hbC, hbO, ?_⟩
  have hcomm : ⁅g * a₀ * g⁻¹, g * b₀ * g⁻¹⁆ = g * ⁅a₀, b₀⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [hcomm, hg]

end Complexity

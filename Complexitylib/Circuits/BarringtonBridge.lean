/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Barrington
public import Complexitylib.Circuits.BarringtonS5

/-!
# Barrington: bridging the abstract move-set to the `S₅` cycle algebra

`Circuits/Barrington.lean` develops the width-`w` representation predicate
`BP.Computes` and its closure moves (conjugation, negation, the commutator-trick
`AND`, `OR`). `Circuits/BarringtonS5.lean` proves the group-theoretic `S₅` input:
every `5`-cycle is the commutator of two `5`-cycles. This module joins the two,
specializing to width `5`, to obtain the moves in the form Barrington's induction
actually consumes — where the *target* representing cycle is an arbitrary
`5`-cycle rather than whatever the subprograms happened to produce.

## Main results

- `Complexity.BP.Computes_retarget` — a program representing `f` through one
  `5`-cycle can be rebuilt to represent `f` through *any* chosen `5`-cycle
  (`5`-cycles are conjugate, and pointwise conjugation preserves length).
- `Complexity.BP.Computes_retarget_length` — the retargeted program has exactly
  the original length.
- `Complexity.BP.Computes_and5` — given subprograms representing `f` and `g`
  through `5`-cycles, `f ∧ g` is representable through *any* target `5`-cycle.
  This is Barrington's `AND` gate with full target-cycle freedom, the exact shape
  the formula induction needs.
-/

@[expose] public section

open scoped commutatorElement
open Equiv

namespace Complexity

/-- Both `5`-cycles of `S₅` have cycle type `{5}` (a single `5`-cycle). -/
private theorem cycleType5 {g : Perm (Fin 5)} (hc : g.IsCycle) (ho : orderOf g = 5) :
    g.cycleType = {5} := by
  have hs : g.support.card = 5 := by rw [← hc.orderOf]; exact ho
  rw [hc.cycleType, hs]

/-- **Retargeting.** If `p` represents `f` through a `5`-cycle `σ`, then for any
    `5`-cycle `a` there is a program representing `f` through `a`. (The two
    `5`-cycles are conjugate — `isConj_iff_cycleType_eq` — and pointwise
    conjugation changes the representing permutation without adding
    instructions.) -/
theorem BP.Computes_retarget {p : BP 5} {f : (ℕ → Bool) → Bool} {σ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    {a : Perm (Fin 5)} (hac : a.IsCycle) (hao : orderOf a = 5) :
    ∃ r : BP 5, BP.Computes a r f := by
  have hconj : IsConj σ a := Equiv.Perm.isConj_iff_cycleType_eq.mpr
    (by rw [cycleType5 hσc hσo, cycleType5 hac hao])
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  have h := BP.Computes_conjugate hp τ
  rw [hτ] at h
  exact ⟨_, h⟩

/-- **Exact-length retargeting.** Retargeting between `5`-cycles by pointwise
conjugation preserves program length exactly. -/
theorem BP.Computes_retarget_length {p : BP 5}
    {f : (ℕ → Bool) → Bool} {σ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    {a : Perm (Fin 5)} (hac : a.IsCycle) (hao : orderOf a = 5) :
    ∃ r : BP 5, BP.Computes a r f ∧ r.length = p.length := by
  have hconj : IsConj σ a := Equiv.Perm.isConj_iff_cycleType_eq.mpr
    (by rw [cycleType5 hσc hσo, cycleType5 hac hao])
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  have h := BP.Computes_conjugate hp τ
  rw [hτ] at h
  exact ⟨BP.conjugate τ p, h, BP.length_conjugate τ p⟩

/-- **Barrington's `AND` gate, with target-cycle freedom.** Given subprograms
    representing `f` and `g` each through some `5`-cycle, and any chosen target
    `5`-cycle `c`, there is a program representing `f ∧ g` through `c`.

    Proof: `c = ⁅a, b⁆` for `5`-cycles `a, b` (`every_fiveCycle_is_commutator`);
    retarget the two subprograms to `a` and `b`; the commutator trick
    (`BP.Computes_and`) then represents `f ∧ g` through `⁅a, b⁆ = c`. -/
theorem BP.Computes_and5 {p q : BP 5} {f g : (ℕ → Bool) → Bool} {σ τ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    (hq : BP.Computes τ q g) (hτc : τ.IsCycle) (hτo : orderOf τ = 5)
    {c : Perm (Fin 5)} (hcc : c.IsCycle) (hco : orderOf c = 5) :
    ∃ r : BP 5, BP.Computes c r (fun α => f α && g α) := by
  obtain ⟨a, b, hac, hao, hbc, hbo, hab⟩ := every_fiveCycle_is_commutator c hcc hco
  obtain ⟨p', hp'⟩ := BP.Computes_retarget hp hσc hσo hac hao
  obtain ⟨q', hq'⟩ := BP.Computes_retarget hq hτc hτo hbc hbo
  have h := BP.Computes_and hp' hq'
  rw [hab] at h
  exact ⟨_, h⟩

end Complexity

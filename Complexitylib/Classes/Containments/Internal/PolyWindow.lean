/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Defs

/-!
# Class membership as an explicit polynomial bound

⚠️ Unreviewed by Bolton

Membership in `PSPACE` is stated asymptotically: some space function that is `O(n^k)`. A machine
under construction needs the opposite — a concrete polynomial it can be checked against, and a
way to hand that polynomial back as a `PSPACE` membership when it is done. The two theorems here
are that exchange, in both directions. The iteration lemma (`SpaceIter.mem_PSPACE_of_iterate`),
Savitch's theorem, and the `PP ⊆ PSPACE` and `PH ⊆ PSPACE` machines pass through them; other
space results in this folder (complement closure, `PSPACE ⊆ EXP`, the `NL` results) work with
the space predicates directly.

## Main results

- `exists_poly_window_of_mem_PSPACE` — a `PSPACE` language with an explicit polynomial window
- `mem_PSPACE_of_polyWindow` — and the converse
- `mem_P_of_polyTime` — the time-domain counterpart, for `P`
-/

@[expose] public section

namespace Complexity

/-- **A `PSPACE` language comes with an explicit polynomial window.** Membership in `PSPACE` only
gives an asymptotic bound on some space function; a machine has to be handed a concrete
polynomial, since the window it must respect is a function of the input length it can evaluate. -/
theorem exists_poly_window_of_mem_PSPACE {L : Language} (h : L ∈ PSPACE) :
    ∃ (k : ℕ) (tm : TM k) (q : Polynomial ℕ),
      (∀ x : List Bool, ∀ c', tm.reaches (tm.initCfg x) c' →
        c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
      (∀ x : List Bool, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
        (x ∈ L → c'.output.cells 1 = Γ.one) ∧
        (x ∉ L → c'.output.cells 1 = Γ.zero)) := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp h
  obtain ⟨k, tm, f, hdec, hf⟩ := hm
  obtain ⟨q, hq⟩ := BigO.pow_polynomial_bound hf
  refine ⟨k, tm, q, fun x c' hreach => ?_, hdec.2⟩
  have hb := hdec.1 x c' hreach
  have hle := hq x.length
  exact ⟨⟨fun i => (hb.1.1 i).trans hle, by have := hb.1.2; omega⟩, by have := hb.2; omega⟩

/-- **A machine with an explicit polynomial window decides a `PSPACE` language.** The exact
converse: together the two say that membership in `PSPACE` *is* the existence of a machine
keeping a polynomial window, with no asymptotics left to manage. -/
theorem mem_PSPACE_of_polyWindow {L : Language} {k : ℕ} (tm : TM k) (q : Polynomial ℕ)
    (hwin : ∀ (x : List Bool) (c' : Cfg k tm.Q), tm.reaches (tm.initCfg x) c' →
      c'.WithinDecisionSpace x.length (q.eval x.length))
    (hdec : ∀ x : List Bool, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)) :
    L ∈ PSPACE :=
  Set.mem_iUnion.mpr ⟨q.natDegree, k, tm, fun n => q.eval n, ⟨hwin, hdec⟩,
    BigO.of_polynomial_bound q (fun _ => le_rfl)⟩


/-- **A machine with an explicit polynomial time bound decides a `P` language.** The time-domain
counterpart of `mem_PSPACE_of_polyWindow`: a construction hands back a concrete `Polynomial ℕ`
and gets the class membership, with the asymptotics discharged here. -/
theorem mem_P_of_polyTime {L : Language} {k : ℕ} (tm : TM k) (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L (fun n => q.eval n)) : L ∈ P :=
  Set.mem_iUnion.mpr ⟨q.natDegree, k, tm, fun n => q.eval n, hdec,
    BigO.of_polynomial_bound q (fun _ => le_rfl)⟩

end Complexity

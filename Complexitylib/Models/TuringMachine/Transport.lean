/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Samuel’s dot
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Exact configuration transport

Successful-step preservation transports exact runs without changing their duration.
The stronger equality of optional steps also reflects every reachable configuration
from an embedded start. The distinction matters: a controller may continue after a
child halts, whereas a tape-layout embedding reflects the child's halt as well.

No injectivity, halting-time bound, or tape invariant is assumed implicitly.
-/

public section

namespace Complexity
namespace TM

/-- Cross-arity generalization of `reachesIn_map`: the simulating
    machine may have a different number of work tapes. If `wrap` commutes
    with `step`, then `reachesIn` lifts through the embedding. -/
theorem reachesIn_map' {n n' : ℕ} {tm : TM n} {tm' : TM n'}
    (wrap : Cfg n tm.Q → Cfg n' tm'.Q)
    (h_step : ∀ c c' : Cfg n tm.Q, tm.step c = some c' →
      tm'.step (wrap c) = some (wrap c'))
    {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') :
    tm'.reachesIn t (wrap c) (wrap c') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (h_step _ _ hstep) ih

/-- If optional steps commute with an embedding, every target configuration reachable
from an embedded start is the image of a reachable source configuration. This includes
all prefixes, not just successful endpoints; no injectivity assumption is needed. -/
theorem reaches_map_reflect {n n' : ℕ} {tm : TM n} {tm' : TM n'}
    (wrap : Cfg n tm.Q → Cfg n' tm'.Q)
    (h_step : ∀ c, tm'.step (wrap c) = (tm.step c).map wrap)
    (c₀ : Cfg n tm.Q) :
    ∀ D, tm'.reaches (wrap c₀) D →
      ∃ c, tm.reaches c₀ c ∧ D = wrap c := by
  intro D hD
  induction hD with
  | refl => exact ⟨c₀, Relation.ReflTransGen.refl, rfl⟩
  | @tail dmid dnext _ hstp ih =>
      obtain ⟨c, hreach, rfl⟩ := ih
      have hstp' : tm'.step (wrap c) = some dnext := hstp
      rw [h_step] at hstp'
      obtain ⟨c', hstep, hD⟩ := Option.map_eq_some_iff.mp hstp'
      exact ⟨c', hreach.tail hstep, hD.symm⟩

end TM
end Complexity

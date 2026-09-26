/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Randomized
public import Complexitylib.Classes.Containments
public import Complexitylib.Classes.Containments.Internal.PPSubsetPSPACE
public import Complexitylib.Classes.P.Defs

/-!
# `PP ⊆ PSPACE`

⚠️ Unreviewed by Bolton

Probabilistic polynomial time with unbounded error is contained in polynomial space.

Membership in `PP` compares the number of accepting computation paths with half of the total. A
deterministic machine can enumerate the choice sequences one at a time — each is only polynomially
long — simulating the machine on each and keeping a running count. The counter needs as many bits
as the number of paths has digits, which is polynomial, and each simulation reuses the same space.

## The machine

`NTM.ppMachine` is the enumerator. It parks every head past the left marker, writes the horizon
`2 ^ p |x| ` into a register by Horner-evaluating `p` on the input length, then loops: for each
counter value it simulates one path of the source machine — the counter tape *is* the choice
tape — bumps whichever tally the verdict names, and wipes its scratch space before the next pass.
The loop ends when the counter reaches the horizon, and the epilogue compares the two tallies.

Space is the point of the construction, and it is not "space ≤ time": the loop runs `2 ^ p |x|`
times. Each pass is bounded on its own, and the wipe restores the bank the next pass starts from,
so a window one iteration wide holds for the whole run.

One wrinkle shapes the simulation. No stage of a composed machine can be entered with a head at
cell zero, so the simulated machine's first transition would have to ignore its choice bit;
`NTM.delayNTM` prefixes two such steps, doubling the accepting count, which the horizon's own
doubling absorbs exactly (`NTM.delayNTM_char`). A source that starts halted has no accepting path
at all and is handled separately, by a machine that publishes `0`.

## Main results

- `NTM.acceptProb_gt_half_iff` — the threshold as an integer comparison
- `PP_integer_characterization` — `PP` with no rational arithmetic left in it
- `PP_subset_PSPACE_of_counter` — the containment, granted one machine
- `PP_subset_PSPACE_of_tallyMachine` — the same, with the obligation reduced to a machine
  deciding one arithmetic predicate
- `PP_subset_PSPACE` — the containment
- `BPP_subset_PSPACE` — `BPP ⊆ PSPACE`, through `BPP_subset_PP`
-/

@[expose] public section

namespace Complexity

/-- **`PP ⊆ PSPACE`**: count accepting paths by enumerating choice sequences in place. -/
theorem PP_subset_PSPACE : PP ⊆ PSPACE := PP_subset_PSPACE_internal

/-- **`BPP ⊆ PSPACE`**, as the composite `BPP ⊆ PP ⊆ PSPACE`. -/
theorem BPP_subset_PSPACE : BPP ⊆ PSPACE := BPP_subset_PP.trans PP_subset_PSPACE

/-- **`PP` with no rational arithmetic left.** A language of `PP` is decided by comparing twice
the number of accepting choice sequences against their total count `2 ^ T` — a comparison of two
naturals of polynomially many bits, which is what the enumerating machine actually computes. -/
theorem PP_integer_characterization {L : Language} (hL : L ∈ PP) :
    ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ) (m : ℕ),
      tm.AllPathsHaltIn f ∧ f =O (· ^ m) ∧
      ∀ x : List Bool, x ∈ L ↔
        2 ^ f x.length < 2 * tm.acceptCount x (f x.length) :=
  PP_integer_characterization_internal hL


/-- **`PP ⊆ PSPACE`, reduced to the existence of one machine.** For each probabilistic machine
and time bound, exhibit a deterministic machine that keeps a polynomial window and decides the
integer comparison `2 ^ T < 2 · acceptCount`. The rational threshold is already eliminated by
`PP_integer_characterization`, so neither probability nor asymptotics survive in the obligation:
what is left is an enumerator over choice sequences with a binary counter. -/
theorem PP_subset_PSPACE_of_counter
    (h : ∀ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ), tm.AllPathsHaltIn f → (∃ m, f =O (· ^ m)) →
      ∃ (k' : ℕ) (M : TM k') (q : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k' M.Q), M.reaches (M.initCfg x) c' →
          c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', M.reaches (M.initCfg x) c' ∧ M.halted c' ∧
          (2 ^ f x.length < 2 * tm.acceptCount x (f x.length) →
            c'.output.cells 1 = Γ.one) ∧
          (¬ (2 ^ f x.length < 2 * tm.acceptCount x (f x.length)) →
            c'.output.cells 1 = Γ.zero))) :
    PP ⊆ PSPACE :=
  PP_subset_PSPACE_of_counter_internal h



/-- **`PP ⊆ PSPACE`, reduced to a machine deciding one arithmetic predicate.** The sharpest form
of the obligation: exhibit a machine keeping a polynomial window that decides whether the
accepting tally exceeds the rejecting one, counting over a horizon `p |x|` it can evaluate.
Probability, rationals, the quantifier over `Fin T → Bool`, and the protocol's own time function
have all been eliminated — see `NTM.mem_iff_tally_lt_tally_poly` for the chain. -/
theorem PP_subset_PSPACE_of_tallyMachine
    (h : ∀ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ) (p : Polynomial ℕ),
      tm.AllPathsHaltIn f → (∀ n, f n ≤ p.eval n) →
      ∃ (k' : ℕ) (M : TM k') (q : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k' M.Q), M.reaches (M.initCfg x) c' →
          c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', M.reaches (M.initCfg x) c' ∧ M.halted c' ∧
          ((NTM.tally (fun v => !NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length) <
            NTM.tally (fun v => NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length)) → c'.output.cells 1 = Γ.one) ∧
          (¬ (NTM.tally (fun v => !NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length) <
            NTM.tally (fun v => NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length)) → c'.output.cells 1 = Γ.zero))) :
    PP ⊆ PSPACE :=
  PP_subset_PSPACE_of_tallyMachine_internal h


end Complexity

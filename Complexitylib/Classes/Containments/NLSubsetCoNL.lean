/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.L
public import Complexitylib.Classes.Containments.Defs
public import Complexitylib.Classes.Containments.Internal.InductiveCounting
public import Complexitylib.Classes.Containments.Internal.SuccMachine
public import Complexitylib.Classes.Containments.Internal.CountingCert

/-!
# `NL ⊆ coNL`

⚠️ Unreviewed by Bolton

Nondeterministic logarithmic space is closed under complement — the
Immerman–Szelepcsényi theorem.

The proof is inductive counting. Write `r_i` for the number of configurations reachable from the
initial one within `i` steps. Given `r_i`, a nondeterministic logspace machine can verify
`r_(i+1)` by cycling over all configurations and, for each, guessing and checking a short path;
the count certifies that no configuration was missed. Running this to the end yields the exact
number of reachable configurations, and a machine that knows that number can reject exactly when
no accepting configuration is reachable.

## Progress

**The complement is now a certificate.** `NL_complement_certificate` says that an input is
outside the language exactly when the last round of the bounded search can be *listed* with none
of its members accepting — where a list counts as exhausting the round when its entries are
distinct members and there are at least as many of them as the round contains. That is
`inductive_counting_certificate` in the form a machine uses it: a negative fact certified
positively, by a count.

The certificate is built so that a logarithmically bounded machine never holds any of it.

- A list entry is checked by `NL_membership_is_walk`: a code lies in round `i` exactly when some
  sequence of `i` steps from the start reaches it, each step staying put or moving to a successor.
  A machine verifies that holding only the current code and the step index.
- The list itself is guessed one entry at a time and only *counted*; `NL_nonmembership_by_counting`
  is what licenses concluding non-membership from absence once the count is reached.

## What the proof still needs

Only the machine. It has to guess the certificate and check it, which is three nested bounded
loops — over the rounds, over the codes of a round, and over the steps of a walk — with a handful
of logarithmically wide registers: a round index, two counts, the code being tested, the code
being walked, and a step index.

The machine is now to be built **deterministically**. `Complexity.NTM.exists_loadTape` turns a
deterministic machine whose guesses arrive on its last work tape into a nondeterministic one, so
the whole of `Complexitylib.Models.TuringMachine.Subroutines` — `TM.binaryFor`, `TM.binaryEq`,
`TM.binarySucc` and their Hoare contracts — applies unchanged, and the nondeterminism is confined
to a single tape read. `Complexitylib.Models.TuringMachine.GuessAssembly` supplies the parts:
`TM.liftLast` runs an existing subroutine while holding the guess tape still, and
`TM.liftLast_hoareTime` carries its contract across; `TM.guessReadTM` is the one-step primitive
that consumes a guess; and
`TM.guessProtocol_seqTM` / `TM.guessProtocol_loopTM` say the obligation survives composition.

The registers it works on are laid out by `Complexity.codeCodec`: a configuration code as a
fixed-width bitstring, so that a register is a fixed number of cells and the enumeration over
configurations is one binary counter. `Complexity.BitCodec` assembles that layout field by field
and discharges the width and round-trip obligations once, and its decoder is total, so every
bitstring the counter reaches denotes some configuration — the ones outside the image simply
denote configurations no walk reaches.

What remains is the machine itself: a successor check on those codes — decode, apply one
transition of the simulated machine, encode — the three nested loops over rounds, codes, and walk
steps, and the space accounting that keeps every register logarithmically wide.

## Main results

- `NL_complement_characterization` — what the complement of an `NL` language says
- `NL_complement_certificate` — and the certificate that establishes it
- `NL_membership_is_walk` — a round member is reached by a walk a machine can follow
- `NL_nonmembership_by_counting` — absence from a full list is non-membership
- `inductive_counting_certificate` — the counting principle that makes the guessing sound
- `NL_subset_coNL_of_counting` — the containment, granted one machine

## TODO

- Build the counting machine and discharge the hypothesis of `NL_subset_coNL_of_counting`.
  `coNL_subset_NL_of_NL_subset_coNL` then gives the reverse inclusion, so this
  single direction settles `NL = coNL`.
-/

@[expose] public section

namespace Complexity

/-- **`NL ⊆ coNL`** (Immerman–Szelepcsényi): nondeterministic logarithmic space is closed
under complement, by inductive counting of the reachable configurations. -/
def NLSubsetCoNL : Prop := NL ⊆ coNL

/-- **The complement of an `NL` language, spelled out.** An input is outside the language exactly
when every configuration reached by the bounded search of `NL_bounded_reachability`
fails to be accepting. Inductive counting exists to certify this universally quantified
statement nondeterministically. -/
theorem NL_complement_characterization {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (A B : ℕ),
      ∀ x : List Bool, x ∉ L ↔
        ∀ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
          ¬ (tm.halted c ∧ c.output.cells 1 = Γ.one) :=
  NL_complement_characterization_internal hL

/-- **The counting principle behind inductive counting.** A subset of a round of the search that
is at least as large as the round is the whole round. A machine that has verified as many
distinct members of round `i` as the round contains, without meeting `c`, has therefore proved
the negative fact `c ∉ round i` — while storing only the count. -/
theorem inductive_counting_certificate {k : ℕ} (tm : NTM k) (c₀ : Cfg k tm.Q) (i : ℕ)
    {T : Set (Cfg k tm.Q)} (hsub : T ⊆ NTM.reachSet tm c₀ i)
    (hcard : (NTM.reachSet tm c₀ i).ncard ≤ T.ncard) : T = NTM.reachSet tm c₀ i :=
  NTM.reachSet_eq_of_ncard_le tm c₀ i hsub hcard


/-- **A round member is reached by a walk.** A code lies in round `i` exactly when some sequence
of `i` steps from the start reaches it, each step either staying put or moving to a successor.
This is the form the machine verifies: it holds only the current code and the step index, never
the walk. -/
theorem NL_membership_is_walk {k : ℕ} (tm : NTM k) (x : List Bool) (S : ℕ)
    (a₀ : Code tm.Q k x.length S) (i : ℕ) (a : Code tm.Q k x.length S) :
    a ∈ NTM.reachCodes tm x S a₀ i ↔
      ∃ f : ℕ → Code tm.Q k x.length S, f 0 = a₀ ∧ f i = a ∧
        ∀ j < i, f (j + 1) = f j ∨ f (j + 1) ∈ NTM.codeSucc tm x S (f j) :=
  NTM.mem_reachCodes_iff_walk tm x S a₀ i a

/-- **Absence from a full list is non-membership.** Once a machine has counted as many distinct
verified members of a round as the round contains, a code it has not seen is not in the round. -/
theorem NL_nonmembership_by_counting {k : ℕ} {tm : NTM k} {x : List Bool} {S : ℕ}
    {a₀ : Code tm.Q k x.length S} {i : ℕ} {l : List (Code tm.Q k x.length S)}
    (h : NTM.RoundList tm x S a₀ i l) {a : Code tm.Q k x.length S} (ha : a ∉ l) :
    a ∉ NTM.reachCodes tm x S a₀ i :=
  NTM.not_mem_of_roundList h ha

/-- **The complement of an `NL` language, as a certificate.** An input is outside the language
exactly when the last round of the bounded search can be listed with none of its members
accepting. Every quantity is an explicit arithmetic function of the input length, and the list is
consumed one entry at a time — which is what a logarithmically bounded machine can do. -/
theorem NL_complement_certificate {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (C D A B : ℕ),
      ∀ x : List Bool, x ∉ L ↔
        ∃ l : List (Code tm.Q k x.length (logWindow C D x.length)),
          NTM.RoundList tm x (logWindow C D x.length)
              (cfgCode x.length (logWindow C D x.length) (tm.initCfg x))
              (A * (x.length + 1) ^ B) l ∧
            ∀ a ∈ l, ¬ ((decodeCfg x (logWindow C D x.length) a).state = tm.qhalt ∧
              (decodeCfg x (logWindow C D x.length) a).output.cells 1 = Γ.one) :=
  NL_complement_certificate_internal hL

/-- **`NL ⊆ coNL`, reduced to the existence of one machine.** For a log-space machine `tm` — the
space witness is part of the hypothesis — and a polynomial round bound, exhibit a nondeterministic
log-space transducer deciding the *negative* condition, that no configuration the bounded search
reaches is accepting. `inductive_counting_certificate` is the principle that makes that
certifiable by guessing while storing only a count. -/
theorem NL_subset_coNL_of_counting
    (h : ∀ (k : ℕ) (tm : NTM k) (S : ℕ → ℕ) (L₀ : Language) (A B : ℕ),
      tm.DecidesInSpace L₀ S → S =O (fun n => Nat.log 2 n) →
      ∃ (k' : ℕ) (M : NTM k') (C D : ℕ), M.IsTransducer ∧
        M.DecidesInSpace
          {x : List Bool | ∀ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
            ¬ (tm.halted c ∧ c.output.cells 1 = Γ.one)}
          (logWindow C D)) :
    NL ⊆ coNL :=
  NL_subset_coNL_of_counting_internal h

end Complexity

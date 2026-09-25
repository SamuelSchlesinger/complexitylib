# A3 — Guess-and-Verify NTM Design Doc

> **Partially completed — historical design document.** The SAT-specialized
> deterministic verifier, composed guess-and-verify machine, polynomial-time
> analysis, and headline theorem `SAT.L_SAT_mem_NP` are now proved in
> `Complexitylib/SAT/VerifierTM.lean`, `Complexitylib/SAT/GuessVerify.lean`, and
> `Complexitylib/SAT/Headline.lean`. The generic
> `NP.WitnessNTMConstruction` stated below is now proved as
> `NP.witnessNTMConstruction` in `Complexitylib/Classes/NP/WitnessConstruction.lean`.
> Other status and remaining-work notes describe the project when this design
> was written.

**Status:** SAT-specialized composed machine, full setup/pair/verify
correctness spine, uniform `DecidesInTime` theorem for `L_SAT`,
polynomial runtime wrapper, direct conditional theorem
`pairLang R_SAT ∈ P → L_SAT ∈ NP`, and an executable SAT verifier spec
(`SAT.verifyPair`) with exact language characterization
`w ∈ pairLang R_SAT ↔ SAT.verifyPair w = true` implemented; remaining
headline work is the deterministic verifier TM establishing
`pairLang R_SAT ∈ P`
**Branch:** `feat/sat-verifier`
**Target construction interface:** `NP.WitnessNTMConstruction` in
`Complexitylib/Classes/NP/Witness.lean`
**Unblocks:** the guess-and-verify side of `SAT ∈ NP`; the remaining
headline blocker is the SAT-specific verifier-in-`P` theorem (task B)

## 1. Goal

Implement `NP.WitnessNTMConstruction`:

```lean
def WitnessNTMConstruction : Prop :=
    {R : List Bool → List Bool → Prop}
    {p : Polynomial ℕ} {c k : ℕ}
    {M : TM k} {f : ℕ → ℕ}
    (hp : ∀ x y, R x y → y.length ≤ p.eval x.length)
    (hM : M.DecidesInTime (pairLang R) f)
    (hfO : f =O (· ^ c)) :
    ∃ (k' d : ℕ) (N : NTM k') (g : ℕ → ℕ),
      N.DecidesInTime (witnessLang R) g ∧ g =O (· ^ d)
```

i.e.: build an NTM `N` that decides `{x | ∃ y, R x y}` in polynomial time,
given a polynomial-time DTM `M` deciding `pairLang R = {pair x y | R x y}`
and a polynomial witness-length bound.

## 2. Given primitives

From the existing codebase (all proved, no sorries):

- **`pairBuildTM yIdx pIdx : TM k`** (`PairBuildTM.lean`, proved).
  Given input tape holding `x` and work tape `yIdx` holding `y`, writes
  `pair x y` onto work tape `pIdx`. Hoare spec:
  `pairBuildTM_hoareTime` with bound `pairBuildTime |x| |y| = 4·|x| + 2·|y| + 10`.
  Postcondition: `pIdx` head = 1, cell 0 = `▷`, cells 1..|pair| =
  `Γ.ofBool pair[i]`, and all cells after the encoded pair are `□`.
  The helper `TM.tape_eq_initTape_move_right_of_binary` converts that
  strengthened cell/tail postcondition into exact equality with
  `initTape (pair x y).map` moved to cell 1, which is the virtual-input
  shape used by `retargetInput_decidesVirtual_started`; the corollary
  `TM.pairBuildTM_hoareTime_initTape_move_right` packages this directly.
  For phase composition, `TM.pairBuildTM_hoareTime_all_started_initTape_move_right`
  and its `TM.toNTM` lift handle the real post-setup layout where input,
  witness, and blank pair tapes have all already moved from `▷` to cell 1.
- **`retargetInput M : TM (k+1)`** (`Combinators.lean`, proved).
  Theorem `retargetInput_decidesVirtual`: given `M.DecidesInTime L T`, for
  any `z : List Bool` and any real input `realInput`, running
  `retargetInput M` from the initial config *where work tape k holds
  `initTape (z.map Γ.ofBool)`* reaches a halting config in `≤ T |z|` steps,
  outputting `1/0` per `z ∈ L`.
  The helper `retargetInput_decidesVirtual_started` covers the more useful
  post-start configuration where the virtual-input tape head is already at
  cell 1, which is the shape produced by `pairBuildTM`.
  The branch now also exposes `startedCfg_state_eq`, `startedCfg_work_eq`,
  `startedCfg_output_eq`, `startedCfg_input_eq`, `startedCfg_work_eq_init`,
  and `startedCfg_output_eq_init`, which pin down the verifier's forced
  first-step configuration for phase transitions.
  → This gives us "simulate M on whatever is on work tape k, ignoring the
  input tape."
- **`TM.toNTM : TM n → NTM n`** (proved, `TuringMachine.lean:516`).
  Lifts a DTM into an NTM that ignores the choice bit. Both δ₀ and δ₁
  equal the DTM's δ.
- **`BigO.pow_polynomial_bound`** and **`BigO.of_polynomial_bound`**
  (`Asymptotics.lean`, proved). Convert between `f =O (·^c)` and
  `∀ n, f n ≤ p.eval n`.

**What exists now:** a small NTM-side Hoare layer (`NTM.HoareTime`) and
`TM.HoareTime.toNTM`, enough to reuse DTM Hoare triples after lifting a DTM
with `TM.toNTM`. The branch also has `NTM.guessBoundedNTM`, a reusable
bounded witness-guessing subroutine driven by a preloaded unary counter tape,
plus the first counter-consumption invariants. For the SAT-specific route,
`TM.inputLengthPlusOneCounterTM` now materializes the linear bound
`|input| + 1` as a unary counter, with both deterministic and `TM.toNTM`
Hoare-time specs.

**What does not exist:** generic NTM combinators (`unionNTM`, `seqNTM`, …) or a
generic unary `p.eval |x|` setup machine. The SAT-specialized construction now
uses direct `NTM.trace` reasoning over a concrete composed machine.

## 3. High-level architecture

The NTM `N` has **three phases** executed in sequence:

1. **Guess phase.** Nondeterministically write a witness `y` of length
   exactly `p.eval |x|` onto a dedicated work tape (the "witness tape"),
   then advance to the pair phase. One NTM step per guessed bit, plus a
   final "end-of-guess" transition.
2. **Pair phase.** Run the lifted DTM `pairBuildTM yIdx pIdx` (via
   `TM.toNTM`) to build `pair(x, y)` on the pair tape, reading `x` from
   the input tape and `y` from the witness tape.
3. **Verify phase.** Run `toNTM (retargetInput M)`, whose "virtual input"
   is the pair tape. Output whatever M outputs.

Each phase is sequenced by having the halting state of one phase coincide
with the starting state of the next, and by carefully crafting the
transition at the phase boundary so tape heads and contents are in the
right configuration for the next phase.

## 4. Tape layout and arity

Let `k'` be the total number of work tapes. We must budget for:

- M's own `k` work tapes (used internally by M during verification).
- The pair tape (call its index `pIdx`, holds `pair(x, y)` after phase 2).
- The witness tape (call its index `wIdx`, holds `y` after phase 1).

`retargetInput M : TM (k+1)` adds one work tape (index `k`) to M,
treating it as the virtual input tape. So when we wrap it, that work-tape
index must be the pair tape.

**Proposed layout:** `k' = k + 2` work tapes, with

- tapes `0..k-1` — M's internal work tapes.
- tape `k` — the **pair tape** (the virtual input for `retargetInput M`).
- tape `k+1` — the **witness tape** (holds `y` after the guess phase).

With this layout:
- `pIdx := ⟨k,   by omega⟩ : Fin k'`
- `wIdx := ⟨k+1, by omega⟩ : Fin k'`
- `wIdx ≠ pIdx` trivially (needed by `pairBuildTM_hoareTime`).

Phase 2 calls `pairBuildTM wIdx pIdx`, phase 3 treats tape `pIdx` as the
virtual input for M.

## 5. State type

The NTM's state `Q` is a disjoint union of three chunks:

```lean
inductive GuessPhase where
  | bit       -- currently guessing bit i
  | endGuess  -- guess done, transition to pair phase

-- Existing: PairBuildPhase (9 constructors) from pairBuildTM
-- Existing: (retargetInput M).Q ≅ M.Q

def Q : Type := GuessPhase ⊕ PairBuildPhase ⊕ (retargetInput M).Q
```

where:

- `qstart := .inl .bit` (start in guess phase).
- `qhalt  := .inr (.inr (retargetInput M).qhalt)` (halt when M halts).
- The guess-phase's final transition leads to `.inr (.inl .init)`
  (pairBuildTM's start state).
- PairBuildTM's halt state `.done` is remapped to transition into
  `.inr (.inr (retargetInput M).qstart)` — i.e., the guess-phase and
  pair-phase never *actually halt*; they transition into the next
  phase's start state instead.

**Technical wrinkle:** pairBuildTM's "done" state in isolation is its
`qhalt` and no step fires from there. In the composed NTM, δ on this
state must instead transition into the verify phase. Concretely, the
composed δ pattern-matches on the state: for the "done-of-pairBuildTM"
constructor, it computes the transition into the verify phase rather
than delegating to pairBuildTM's δ (which is irrelevant there because
no step fires in the standalone DTM). This is the standard pattern used
by `seqTM` for DTMs.

### Guess-phase transitions

The guess phase uses a single step per witness bit. At state
`.inl .bit` with choice bit `b`:

- **If the witness counter (tracked by the witness tape's head position)
  is `< p.eval |x|`:** write `b` to cell (head) of the witness tape,
  move witness-tape head right, stay in `.inl .bit`.
- **If the head has reached position `p.eval |x| + 1`:** transition to
  `.inl .endGuess`.

But: the state type has no counter. Two options:

**Option A: counter-free, use tape position.** The witness tape's head
position *is* the counter: cell `i+1` holds the guessed `y[i]`. When the
head reads a `□` (blank) at some position, we've reached the end of the
witness tape. But we're writing as we go, so the cell under the head is
always blank right before the write. Distinguishing "last bit of witness"
from "any other bit" requires external info.

**Option B: baked-in counter.** Parameterize the state type by a `Fin (p.eval |x|+1)`
counter. Problem: the polynomial `p` depends on `|x|`, so the state type
would depend on `x`, which is not allowed — `Q` is fixed at NTM
construction, not per-input.

**Option C: unary counter on a second tape.** Add a *guess-counter tape*
initialized with `p.eval |x|` tally marks (these must be produced before
the guess starts, e.g., by copying from the input tape or by computing
`p.eval |x|` in unary). Decrement on each guess step, halt guess when
counter hits zero.

Option C is clean but adds complexity: we need a pre-guess phase that
materializes `p.eval |x|` tally marks on a dedicated tape. Evaluating a
polynomial on `|x|` in unary on a TM is a well-studied primitive but
requires a nontrivial sub-construction.

**Recommended: hybrid Option A+B.** Guess *any* length, then at the
transition to the pair phase, cap witness length at `|x| + p.eval |x|`
*structurally* by bounding the step budget. Concretely, the overall
time bound `g(|x|)` includes `p.eval |x|` for the guess phase; if a
choice sequence tries to guess longer, it runs out of steps and fails
`AllPathsHaltIn`. For acceptance, we only need the *existence* of a
choice sequence that (a) guesses exactly the witness length |y|, (b)
runs pairBuildTM and M to completion within budget.

Let me sharpen this. The guess-phase state machine is:

- `.inl .bit`: on any input, with choice `b`:
  - if `b = false`: write `Γ.blank` (leave blank), move witness head
    left, transition to `.inl .endGuess` (i.e., "end of guess").
    Wait — we can't move a witness head with a blank under it without
    writing something. Let me redesign.

Revised guess-phase design:

- `.inl .writeBit`: on any input, with choice `b`:
  - write `Γ.ofBool b` to the witness tape, move witness head right,
    stay in `.inl .writeBit`.
- `.inl .endGuess`: on any input, with *both* choices, move witness
  head right one more step and transition to `.inl .rewindWitness`.

But we need a way to *enter* `.inl .endGuess`. How does the NTM decide
when to stop guessing? The choice bit selects "guess another bit" vs
"stop guessing":

- `.inl .chooseContinue`: choice bit determines next state.
  - δ₀ (choice = false, "stop"): transition to `.inl .rewindWitness`.
  - δ₁ (choice = true, "continue"): write nothing yet, transition to
    `.inl .writeBit`.
- `.inl .writeBit`: choice bit = witness bit b.
  - δ_b: write `Γ.ofBool b` to witness tape, move witness head right,
    transition back to `.inl .chooseContinue`.
- `.inl .rewindWitness`: DTM-like rewind phase. Move witness head left
  until reading `▷`. Similar structure to `rewindWorkTM` / pairBuildTM's
  rewindP1/P2.

When the witness tape is rewound (head = 0, then right to head = 1 on
the transition), transition to the pair phase's init state.

### Pair-phase and verify-phase transitions

Once in pair phase (`.inr (.inl .init)`), the composed NTM's δ delegates
to pairBuildTM's δ (ignoring the choice bit) until pairBuildTM reaches
its halt state. Then δ at the pairBuildTM-halt state transitions into
the verify phase (`.inr (.inr (retargetInput M).qstart)`).

Verify phase delegates to `(retargetInput M).δ`. It terminates at
M's original halt state.

## 6. Time analysis

Phase-by-phase:

1. **Guess:** `2 · |y| + 1` steps (one write + one choose per bit, plus
   one final stop). For the "right" choice sequence where `|y| ≤ p.eval |x|`,
   this is `≤ 2 · p.eval |x| + 1` steps.
2. **Rewind witness:** `|y| + 1` steps (one per tape cell plus a transition).
3. **Pair:** `4·|x| + 2·|y| + 10` (pairBuildTime).
4. **Verify:** `f (|pair x y|) = f (2·|x| + 2 + |y|)` steps.

Total for the accepting choice sequence, when `|y| ≤ p.eval |x|`:

```
g(|x|) := 2·p.eval|x| + 1 + p.eval|x| + 1 + 4·|x| + 2·p.eval|x| + 10 + f(2·|x| + 2 + p.eval|x|)
       ≤ c₁ · p.eval|x| + c₂ · |x| + f(c₃ · (|x| + p.eval|x|))
```

Since `f ≤ polynomial_of_c` (by `BigO.pow_polynomial_bound` on `hfO`),
and `p` is a polynomial, composing polynomials yields a polynomial.
Total bound: `g` is polynomially bounded, so `g =O (·^d)` for
`d := degree of composite` (via `BigO.of_polynomial_bound`).

**All-paths-halt requirement:** we need to choose `g(|x|)` such that
*every* choice sequence of length `g(|x|)` halts. This is where the
guess-phase design matters — the composed NTM must halt no matter what
choices are made. We achieve this by structuring the guess phase so that:

- if the choice sequence ever picks `chooseContinue → false` (stop), we
  enter rewind + pair + verify with whatever witness was guessed so far;
- if the choice sequence *never* picks stop, the machine runs out of
  steps before reaching the pair phase — but this violates
  `AllPathsHaltIn`.

Workaround: cap the guess-phase by structure. Add a "kill counter"
state `.inl .chooseContinue` that *forcibly* transitions to stop after
`2·p.eval|x| + 1` attempts. But again, the state type can't depend on
`|x|`. Alternative: add a counter-tape, as in Option C above.

**Cleanest fix:** bound the guess-phase length *externally* by the step
budget, and in the acceptance/`AllPathsHaltIn` proof, handle two cases:

- Case A (accepting, `x ∈ witnessLang R`): there exists `y`, `|y| ≤ p.eval |x|`,
  with `R x y`. Pick choices that guess `y` then stop. Machine halts
  in `g(|x|)` steps, outputs 1.
- Case B (non-accepting, `x ∉ witnessLang R`): for *every* choice
  sequence, either
  - the guess phase stops early with some `y'`, then pair+verify runs to
    halt; since `¬ R x y'`, M outputs 0.
  - the guess phase never stops — need to force halt here.

To force halt in Case B's infinite-guess subcase, the guess phase must
*structurally* cap. Without a per-input counter, the only mechanism is
**to have the guess phase unconditionally advance a bounded counter
that's encoded in the *tape contents* rather than the *state type*.**

**Final decision: Option C — use a counter tape.** Add one more tape
for the unary counter. This requires a pre-guess phase that writes
`p.eval |x|` tally marks, then the guess phase decrements the counter
per bit. When the counter hits zero, the guess phase is forced to stop.

So: `k' = k + 3` total work tapes (M's `k` + pair + witness + counter).

### Counter-tape construction

The counter tape starts empty. Before the guess phase, we need to
evaluate `p(|x|)` in unary on the counter tape. This is a polynomial
evaluation in unary, which requires:

- Computing `|x|` in unary (copy from input tape: one cell per input bit).
- Multiplication in unary (for `|x|^k` terms): `|x|^k` unary cells is
  `|x|^k` tape, which is polynomial.
- Addition in unary: trivial concatenation.

This is all standard TM stuff, but nontrivial. Alternatively, we can
sidestep polynomial evaluation entirely by computing an upper bound:

**Simplification:** replace `p.eval |x|` with `|x|^d + d` for some fixed
`d` from `hp` + `BigO.pow_polynomial_bound`. A unary upper bound
`|x|^d + d` can be laid down on the counter tape by `d` rounds of
"for each cell of `x`, copy the entire current counter tape." This is
still nontrivial.

**Further simplification (possibly used):** observe that any polynomial
`p` is dominated by `(|x| + 1)^d` for some `d`. In unary, `(|x| + 1)^d`
can be computed by `d - 1` multiplication passes, each of which is
itself a DTM subroutine.

→ This sub-construction is large enough to merit its own design doc
(call it **A3.1 — Unary Polynomial Evaluator**). It will likely
dominate the LOC of A3.

## 7. Proof strategy

Three layers of proof obligation:

### 7a. `AllPathsHaltIn g`

For every `x` and every choice sequence `choices : Fin (g |x|) → Bool`,
the final state after `g |x|` steps is `qhalt`.

Structure: phase-by-phase analysis.

- Guess phase halts deterministically once the counter hits zero, *regardless
  of choices*. Reason: counter decreases by 1 per step, counter-zero
  → transition to rewind. Steps ≤ `p.eval |x| · 2 + 1` (two steps per
  bit: write + choose).
  *Alternative:* choice bit picks stop → transition immediately.
  Either way, bounded.
- Rewind witness: DTM-like. Steps ≤ `|y'| + 1` where `|y'|` is the
  actual guessed length (≤ `p.eval |x|`).
- Pair: bounded by pairBuildTime.
- Verify: bounded by `f`.

Summed: `g(|x|)` as above.

### 7b. Acceptance direction (`x ∈ L → AcceptsInTime x (g |x|)`)

Given `y` with `R x y` and `|y| ≤ p.eval |x|`, construct the choice
sequence that:

1. Guesses `y`: alternates `chooseContinue := true, writeBit := y[i]`
   for i = 0..|y|-1, then `chooseContinue := false`. This takes
   `2·|y| + 1` steps.
2. Pads remaining steps with arbitrary bits (all zeros).

Show that this choice sequence drives the machine through the three
phases, each leaving the tapes in the configuration required by the
next phase, and ends with `output.cells 1 = Γ.one`.

This decomposes via three simulation lemmas:

- **Guess-simulates:** starting from `N.initCfg x`, after `2·|y| + 1`
  steps with the right choices, the config has state `.inl .rewindWitness`
  (or the appropriate initial state), witness tape holds `y`, pair tape
  is empty, other tapes unchanged.
- **Pair-simulates:** from the guess-phase-final config, after
  `pairBuildTime |x| |y| + 1` steps (one transition step + pairBuildTM's
  own runtime), the config has state `.inr (.inr (retargetInput M).qstart)`,
  pair tape holds `pair(x, y)`, other tapes unchanged.
  **This uses `pairBuildTM_hoareTime` via a DTM→NTM lifting lemma.**
- **Verify-simulates:** from the pair-phase-final config, after `≤ f(|pair x y|)`
  steps, machine halts with `output.cells 1 = Γ.one` (since `pair x y ∈ pairLang R`).
  **This uses `retargetInput_decidesVirtual` via the same lifting.**

Each simulation lemma requires a **DTM-inside-NTM simulation lemma**,
along the lines of:

```lean
lemma toNTM_trace_eq_iterate_step (tm : TM n) (c : Cfg n tm.Q) (t : ℕ)
    (choices : Fin t → Bool) :
    (tm.toNTM).trace t choices c = tm.iterateStep t c
```

which would reduce NTM trace reasoning about a lifted DTM into DTM
`reaches`/`reachesIn` reasoning. The currently available
`TM.HoareTime.toNTM` covers the Hoare-triple form of this need; more
specialized phase-simulation lemmas may still be useful when assembling the
full composed NTM.

### 7c. Non-acceptance direction (`x ∉ L → ¬ AcceptsInTime x (g |x|)`)

For every choice sequence, after `g |x|` steps, `output.cells 1 ≠ Γ.one`.
Equivalent: every choice sequence ends with `output.cells 1 = Γ.zero`.

Case-split on what the guess phase produces:

- Guess produces some `y'` of length ≤ `p.eval |x|` (possibly < actual
  witness length). Then pair tape holds `pair(x, y')`. M decides
  `pair x y' ∈ pairLang R`. Since `x ∉ witnessLang R`, there's *no* `y`
  with `R x y`, so in particular `¬ R x y'`, so `pair x y' ∉ pairLang R`,
  so M outputs 0.

That's it — if `AllPathsHaltIn` (7a) is proved, then every path halts,
guess produces some `y'`, verify rejects.

## 8. Subtask breakdown

Remaining work, in dependency order:

1. **A3.0 (done)** — Add `NTM.HoareTime` / `NTM.Hoare` analogues in
   `Hoare/Defs.lean`. Pre/post predicates abstracted over choice
   sequences. Not strictly necessary if I'm willing to inline, but
   ~200 LOC up front saves ~1000 later.
2. **A3.1 (partially done)** — DTM-in-NTM simulation lemma:
   `toNTM_trace_eq_reachesIn` (roughly). Lifts DTM Hoare triples to
   NTM-trace reasoning. The branch now has `TM.HoareTime.toNTM`.
3. **A3.2 (SAT-specific slice started)** — Unary bound setup.
   The generic `p.eval |x|` evaluator is still open, but the SAT-specialized
   machine `TM.inputLengthPlusOneCounterTM` now writes the needed
   `|input| + 1` counter and has a full Hoare/correctness theorem plus
   `TM.toNTM` lift.
4. **A3.3 (done for the bounded guess subroutine)** — Guess-phase NTM +
   Hoare triple. The branch now defines `NTM.guessBoundedNTM` and proves
   the continue/write invariant, rewind correctness, immediate-stop
   branches, the recursive all-path bounded halting theorem, and the
   Hoare-style wrappers `NTM.guessBoundedNTM_hoareTime` and
   `NTM.guessBoundedNTM_hoareTime_with_cell0`. It also proves the matching
   completeness theorem
   `NTM.guessBoundedNTM_choose_generates_witness`: every target suffix
   within the unary counter bound is produced by some choice sequence. The
   public all-path and generation APIs preserve the witness tape's left-end
   marker. `Tape.hasBinaryString_hasOutput` bridges completed witnesses to
   the standard cell-content predicate, and
   `Tape.hasBinaryString_eq_initTape_move_right` /
   `Tape.hasBoundedBinaryString_eq_initTape_move_right` convert guessed
   witnesses into the exact initialized tape shape consumed by `pairBuildTM`;
   `NTM.guessBoundedNTM_hoareTime_initTape_move_right_with_frames` packages
   that exact witness postcondition together with preservation of the real
   input, output, and every non-witness/non-counter work tape that is already
   past `▷`.
   The branch also has trace-level preservation lemmas for the guess phase:
   `NTM.guessBoundedNTM_trace_preserves_input`,
   `NTM.guessBoundedNTM_trace_preserves_output`, and
   `NTM.guessBoundedNTM_trace_preserves_other_work`. These are the facts
   needed to thread the real input, pair tape, verifier work tapes, and
   output through guessing. Remaining integration work is now sequencing/setup
   and verifier composition.
5. **A3.4 (started)** — Composed NTM: state type, δ/δ₀, phase-transition glue.
   The pair-builder side now has `TM.pairBuild_init_step_started` for the
   partially-started layout and `TM.pairBuild_init_step_all_started` for the
   actual post-setup layout where even the pair tape has already idled to
   cell 1. The corresponding started-tape Hoare theorem and `TM.toNTM` lift
   are proved. The branch also has `TM.rewindInputTM` with deterministic,
   rich, and `TM.toNTM` Hoare-time specs, so the counter phase's end-of-input
   head position can be restored before pair building. The SAT-specific
   composed machine skeleton now lives in `Complexitylib/SAT/GuessVerify.lean`:
   `SAT.satGuessVerifyNTM M` sequences counter setup, input rewind, bounded
   guessing, pair construction, and verifier simulation over the concrete
   `k + 3` tape layout. It also defines the pair/witness/counter indices and
   proves both state-only and full tape-level one-step lemmas for the four
   phase handoffs.
6. **A3.5 (mostly done)** — Phase simulation lemmas.
   The composed machine now has one-step and prefix trace simulations for all
   five phases: counter setup, input rewind, bounded guessing, pair building,
   and verifier simulation. The verifier phase is factored as
   `SAT.satVerifyPhaseTM M`; `SAT.satVerifyInnerCfg` projects that phase back
   to an ordinary verifier configuration, and
   `SAT.satVerifyPhaseTM_trace_one_project` /
   `SAT.satVerifyPhaseTM_trace_project_prefix` prove one-step and multi-step
   projection to `M.toNTM` when the pair tape is stable under
   `readBackWrite`. The phase-level simulation spine is in place.
7. **A3.6 (done for the SAT-specialized construction)** — `AllPathsHaltIn`
   proof.
   The branch now has first-halt exit lemmas for every setup phase:
   `SAT.satGuessVerify_counter_trace_exit`,
   `SAT.satGuessVerify_rewindInput_trace_exit`,
   `SAT.satGuessVerify_guess_trace_exit`, and
   `SAT.satGuessVerify_pair_trace_exit`. These bridge the prefix simulations
   to the next phase when the corresponding subroutine reaches its local
   `done` state, including the full tape-level boundary transform. The generic
   helper `NTM.exists_first_halt_time_of_trace_halted` and Hoare corollaries
   `NTM.HoareTime.exists_first_halt_time` /
   `NTM.HoareTime.exists_first_halt_time_with_post` now package the “some
   first halt time within the Hoare bound” argument and carry the Hoare
   postcondition back to that first halted prefix. The SAT module uses those helpers in
   `SAT.satGuessVerify_counter_init_exits`,
   `SAT.satGuessVerify_rewindInput_exits`,
   `SAT.satGuessVerify_guess_exits`, and
   `SAT.satGuessVerify_pair_exits`; these phase exits now expose the counter
   tape, exact input cells, universal non-counter work-tape frames, output
   frame, rewound exact input tape, exact guessed witness tape, preserved blank
   pair tape, and exact pair tape invariants needed by the next phases.
   `SAT.satGuessVerify_guess_exits_with_frames` now packages the
   arbitrary-choice guess exit with preservation of the real input, blank pair
   tape, output, and verifier work frame.
   Additional integration lemmas now package the most important handoffs:
   `SAT.satGuessVerify_rewindInput_exits_with_frames_exact_input` turns the
   counter/rewrite input-cell facts into the exact `initTape x` shape expected
   by pair building, and
   `SAT.satGuessVerify_guess_generates_with_pair_frame` lifts the guess-phase
   completeness theorem to the composed SAT boundary while preserving the pair
   tape; `SAT.satGuessVerify_guess_generates_with_input_pair_frame` also keeps
   the exact started input tape for the pair phase. The verifier side now has
   `SAT.satVerifyPhaseTM_halts_of_inner_trace_halts` plus
   `SAT.satGuessVerify_verify_halts_of_inner_trace_halts`, transferring
   halting from the projected `M.toNTM` trace back to the composed SAT
   machine. The former manual verifier-phase pair-tape guard is now discharged
   from a clean-tape invariant via
   `SAT.satVerifyPhaseTM_pair_guard_of_clean`,
   `SAT.satGuessVerify_verify_halts_of_inner_trace_halts_clean`, and
   `SAT.satPair_cells_ne_start_of_initTape_ofBool_move_right`.
   The first composition layer is also proved:
   `SAT.satGuessVerify_halts_after_prefix`,
   `SAT.satGuessVerify_accepts_after_prefix`,
   `SAT.satGuessVerify_counter_exit_then_suffix_halts`,
   `SAT.satGuessVerify_rewindInput_exit_then_suffix_halts`,
   `SAT.satGuessVerify_guess_exit_then_suffix_halts`,
   `SAT.satGuessVerify_halts_after_verify_prefix`,
   `SAT.satGuessVerify_accepts_after_verify_prefix`,
   `SAT.satGuessVerify_pair_exit_then_verify_halts`, and
   `SAT.satGuessVerify_pair_exits_then_verify_halts` combine a pair-phase exit
   with a halting projected verifier suffix. The accepting-output path is now
   mirrored by `SAT.satGuessVerify_verify_accepts_of_inner_trace_accepts_clean`,
   `SAT.satGuessVerify_pair_exit_then_verify_accepts`, and
   `SAT.satGuessVerify_pair_start_accepts_of_decidesInTime`. The post-pair
   verifier frame is now exposed by
   `SAT.satGuessVerify_pair_exits_with_verifier_frames`, backed by
   `TM.pairBuildTM_trace_preserves_output` and
   `TM.pairBuildTM_trace_preserves_other_work`. The bridge
   `SAT.satVerifyInnerCfg_eq_startedCfg` identifies that framed verifier
   configuration with `M`'s post-start configuration on `pair x y`, and
   `SAT.verifier_started_trace_halts_of_decidesInTime` /
   `SAT.verifier_started_trace_decides_of_decidesInTime` supply the concrete
   verifier suffix from `M.DecidesInTime`.
   The SAT-specific uniform time helpers
   `SAT.satGuessVerifySetupTime`, `SAT.satVerifierWindowTime`, and
   `SAT.satGuessVerifyTime` now package the fixed `|x|`-only bound needed by
   `NTM.DecidesInTime`; `SAT.satVerifierWindowTime_bounds_pair` handles the
   non-monotone verifier bound by taking a finite maximum over all witness
   lengths up to `|x|+1`. The pair/verifier suffix now has an all-path bound:
   `SAT.satGuessVerify_pair_start_halts_within_bound_of_decidesInTime` shows
   that every remaining choice sequence halts once setup has produced any
   bounded witness with blank verifier frames.
   The upstream setup is now composed too:
   `SAT.satGuessVerify_rewind_then_guess_generates_pair` packages rewind+guess
   into a pair-phase start, `SAT.satGuessVerify_setup_generates_pair` runs
   counter+rewind+guess from the real initial configuration while preserving the
   blank verifier frame, and
   `SAT.satGuessVerify_init_generates_witness_halts_of_decidesInTime` gives the
   end-to-end completeness-halting spine from `satGuessVerifyNTM.initCfg`, and
   `SAT.satGuessVerify_init_generates_witness_accepts_of_decidesInTime` upgrades
   it to accepting output when `pair x y ∈ L`, using a real deciding verifier.
   The wrappers
   `SAT.satGuessVerify_acceptsInTime_of_mem_LSAT_of_decidesInTime` and
   `SAT.satGuessVerify_accepts_of_mem_LSAT_of_decidesInTime` expose the
   yes-instance half directly for `L_SAT`. The all-path halting theorem is
   now packaged as
   `SAT.satGuessVerify_allPathsHaltIn_of_decidesInTime`.
8. **A3.7 (done for the SAT-specialized construction)** — Acceptance +
   non-acceptance proofs.
   The rejecting direction is now carried by
   `SAT.satGuessVerify_trace_decides_for_some_setup_witness_of_decidesInTime`,
   which extracts the bounded witness produced by any full setup trace and
   records the final output bit as a correct decision for `pair x y`. From
   that, `SAT.satGuessVerify_not_acceptsInTime_of_not_mem_LSAT_of_decidesInTime`
   rules out accepting runs on inputs outside `L_SAT`, and
   `SAT.satGuessVerify_decidesInTime_of_decidesInTime` packages the
   SAT-specialized machine as a full `NTM.DecidesInTime` proof for `L_SAT`
   under the uniform bound `satGuessVerifyTime`.
9. **A3.8 (done for the SAT-specialized construction)** — Polynomial time
   bound via `Asymptotics`.
   `SAT.satGuessVerifyTime_polynomial_bound` now turns a verifier bound
   `f =O (· ^ c)` into an explicit polynomial upper bound on the uniform
   SAT runtime, and `SAT.satGuessVerifyTime_bigO_of_bigO` packages that as a
   polynomial-growth theorem. With this asymptotic wrapper in place,
   `SAT.L_SAT_in_NP_of_verifierP_direct` directly proves
   `pairLang R_SAT ∈ P → L_SAT ∈ NP` from the concrete machine in
   `SAT/GuessVerify.lean`.
10. **A3.9 (remaining)** — Deterministic verifier TM plus optional generic
    interface assembly.
    The branch now has the exact SAT verifier specification in
    `SAT/Verifier.lean`: tokenization, CNF decoding, executable checking,
    decoder soundness (`CNF.decode?_sound`), and the exact characterization
    `SAT.verifyPair_eq_true_iff_mem_pairLang`. The remaining SAT-specific
    proof work is therefore a cleaner task: build a deterministic TM that
    computes this fixed Boolean verifier in polynomial time. The TM support
    side also moved forward: `TM.retargetInput_hoareTime` now lifts ordinary
    Hoare triples to virtual-input runs, `TM.copyInputToWorkTM_started_hoareTime`
    packages linear-time started copying, and
    `TM.retargetInput_copyInputToWorkTM_started_hoareTime` gives a ready-made
    virtual-input copy primitive for the upcoming verifier pipeline. In
    addition, `Classes/NP/PairSplitTM.lean` now defines the deterministic
    inverse staging machine `TM.pairSplitCoreTM`, together with exact
    `pair`-indexing lemmas (`pair_get_left_first`, `pair_get_left_second`,
    `pair_get_sep_zero`, `pair_get_sep_one`, `pair_get_right`) and the first
    real correctness spine for that machine: local `scanX`/`afterFalse`/
    `writeTrue` transition lemmas, two-step doubled-bit lemmas for `00`,
    `11`, and separator `01`, plus an exact `.copyY` suffix theorem that
    copies an input segment to the `y` tape and halts in `|y| + 1` steps.
    That front half is now composed all the way through: the file proves the
    `x`-prefix loop, the full valid-input started-state theorem
    `pairSplitCoreTM_from_scanX_initTape_move_right`, and the `.init`
    entry theorem `pairSplitCoreTM_from_init_initTape_move_right` with the
    advertised runtime `pairSplitCoreTime`. So the splitter is no longer the
    missing piece; the next SAT-verifier work is to add the deterministic
    evaluation phase that consumes the staged `x`/`y` tapes. The generic
    `WitnessNTMConstruction` interface is still open, but no longer the
    shortest path to the SAT headline theorem.

Since then, `SAT/VerifierTM.lean` has gained the first concrete verifier-side
machine theorem: `satLengthCheckTM_started_hoareTime`, a deterministic
linear-time checker for the witness side condition `|α| ≤ B` when `α` is on a
started input tape and `B` is stored as a unary counter. To support the next
composition layer, `Models/TuringMachine/Subroutines.lean` and
`Subroutines/Internal.lean` now also provide `TM.copyWorkToWorkTM` and
`copyWorkToWorkTM_started_hoareTime`, so staged Boolean work tapes can be
copied between verifier phases without re-proving ad hoc scan loops. In
addition, `CounterSubroutines.lean` now exports the started-input counter
builder `inputLengthPlusOneCounterTM_started_hoareTime`, plus the stronger
`inputLengthPlusOneCounterTM_started_tracksInput_hoareTime`, which also
records the final input cells/head after scanning. `Subroutines/Internal.lean`
now also provides `clearWorkTM_started_rich_hoareTime` plus the new
`copyWorkToWorkTM_started_rich_hoareTime`, so both clearing and copying a
started Boolean work tape are available in the same frame-preserving Hoare
style as the other setup subroutines. `RetargetInternal.lean` / `SAT/VerifierTM.lean`
lift both the counter builder and the SAT length checker to work-tape form via
`retargetInput_inputLengthPlusOneCounterTM_started_hoareTime`,
`retargetInput_inputLengthPlusOneCounterTM_started_tracksInput_hoareTime`, and
`retargetInput_satLengthCheckTM_started_hoareTime`. `SAT/VerifierTM.lean` now
goes further on both verifier-side subphases. On the counter side, the file
now defines the actual verifier-facing three-work-tape counter slice
`satCounter3TM` with theorem `satCounter3TM_started_hoareTime`: tape `2`
supplies the staged formula bits, tape `0` receives the unary counter
`|z| + 1`, tape `1` is preserved exactly, and the output tape remains the
started blank tape. On the witness-length side, the file defines the
passive-preserving two-work-tape checker `satLengthCheckPassiveTM` with theorem
`satLengthCheckPassiveTM_started_hoareTime`, and then retargets that to the
actual verifier-facing three-work-tape slice `satLengthCheck3TM` with theorem
`satLengthCheck3TM_started_hoareTime`. So the branch now has both real
verifier-side 3-tape slices in place: the counter phase and the length-check
phase. `VerifierTM.lean` now also adds the stable-real-input wrapper
`satCounter3TM_started_stableInput_hoareTime`, so the counter slice can be
used cleanly inside larger `seqTM` proofs without redoing the retargeted-input
frame argument each time. It also defines the first explicit tail composition
surface `satWitnessLengthTailTM` / `satWitnessLengthTailTime`, covering the
"rewind staged witness tapes, then run the 3-tape length check" suffix.
The next clean SAT target is still the full composition theorem for that tail,
and then the earlier prefix that rewinds/clears/copies into it, before moving
on to the CNF evaluator.
To support that without committing to an extra permanent scratch tape,
`Models/TuringMachine/Subroutines.lean` /
`Subroutines/Internal.lean` now also provide `TM.blankWorkTM` and
`blankWorkTM_started_hoareTime`: a linear-time primitive that erases a started
Boolean work tape while preserving the head bound information needed for a
following rewind. That gives the verifier a clean way to recycle the staged
`z` tape as later virtual-input scratch.

Estimated LOC: 2000–3000, comparable to the full combinators file plus
pairBuildTM.

## 9. Open questions

- **Unary poly evaluator feasibility.** Is it simpler to just use a
  counter that counts *in binary* and decrements? Binary counters are
  simpler to *maintain* (O(1) amortized per decrement, log n cells) but
  requires reading/writing multi-cell values per step, which needs more
  states. Unary is single-cell per step but needs polynomial tape
  setup. Need to prototype.
- **Can we avoid the counter tape entirely?** If instead we relax the
  step bound — say, set `g(|x|) := c · p.eval|x|` and structurally bound
  the guess phase to stop after `p.eval|x|` steps by *having it halt
  unconditionally on step overflow via the state machine*. But the state
  machine has no memory beyond Q; the counter *must* be on a tape.
- **State type size.** `GuessPhase ⊕ PairBuildPhase ⊕ M.Q` is fine as
  long as `M.Q` is a `Fintype` (which it is). Lean's `Fintype` instance
  for `Sum` is automatic.
- **`DecidableEq` for the state type.** Sum of decidable-eq types is
  decidable-eq; automatic.
- **Alphabet** — pairBuildTM writes `Γw ⊆ Γ` (no `▷`). The guess phase
  only writes `Γ.zero`/`Γ.one` to the witness tape. Counter tape writes
  tally marks (use `Γ.one`) + blanks. All within `Γw`.
- **Interaction with `retargetInput`'s readBackWrite.** `retargetInput`
  simulates M by reading the virtual-input tape and *writing back what
  it read* so the cells are preserved. This is already handled inside
  `retargetInput` — we just need the pair tape to be initialized
  correctly before the verify phase.

## 10. Recommendation

Next, finish task B: the deterministic TM implementing `SAT.verifyPair` in
polynomial time, which now directly yields `pairLang R_SAT ∈ P` via the
equivalence in `SAT/Verifier.lean`, and therefore the branch headline theorem
via `SAT.L_SAT_in_NP_of_verifierP_direct`. The generic witness interface can be
revisited afterward as cleanup/generalization work.

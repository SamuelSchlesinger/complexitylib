/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.GuessTape

/-!
# Guessing in designated states

`Complexitylib.Models.TuringMachine.GuessTape` pairs `NTM.ofGuess M` with `NTM.choiceTM`, which
forces `M` to consume a guess at *every* step. No machine assembled from
`Complexitylib.Models.TuringMachine.Combinators` does that: the handoff step of `TM.seqTM`, and
every step of a subroutine that has no interest in the guesses, leaves the tape's head where it
is. This file drops that requirement.

A machine here nominates a set of **advancing states**. In an advancing state it consumes the
cell under the guess head and moves that head on; in every other state it neither consults the
guess tape nor moves its head. Between the two lies the whole deterministic subroutine library,
usable unchanged.

The price is that the guess tape's head and the step counter part company: at step `i` the head
sits at the **cursor**, the number of advancing steps so far. `NTM.ofGuess M` still consumes one
choice per step, so the correspondence between a loaded tape and a choice sequence is no longer
the identity — it is the cursor. `NTM.exists_guessTape` is what makes it work in the direction a
soundness proof needs: *every* choice sequence is realized by some loaded tape, because the
choices made at non-advancing steps are the ones the machine never looks at.

## Main definitions

- `TM.traceD` — run a deterministic machine for a fixed number of steps, halting in place
- `TM.GuessProtocol` — advance and consume in the nominated states, hold elsewhere
- `NTM.guessBit` — the bit the machine reads at a given step

## Main results

- `NTM.dropChoice_stepCfg` — one step of `M` is one step of `NTM.ofGuess M` along the bit read
- `NTM.dropChoice_traceD` — and a run is a trace along the bits read
- `TM.traceD_of_reachesIn`, `TM.traceD_add`, `TM.traceD_of_reachesIn_halted` — a run of a fixed
  length is the deterministic trace, traces compose, and a halted trace stays put
- `NTM.exists_guessTape` — every choice sequence comes from a loaded guess tape
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Run a deterministic machine for `T` steps, staying put once halted. The deterministic
counterpart of `NTM.trace`. -/
def traceD (M : TM n) : ℕ → Cfg n M.Q → Cfg n M.Q
  | 0, c => c
  | T + 1, c => if c.state = M.qhalt then c else M.traceD T (M.stepCfg c)

@[simp] theorem traceD_zero (M : TM n) (c : Cfg n M.Q) : M.traceD 0 c = c := rfl

theorem traceD_succ_of_not_halted (M : TM n) (T : ℕ) {c : Cfg n M.Q}
    (h : c.state ≠ M.qhalt) : M.traceD (T + 1) c = M.traceD T (M.stepCfg c) := by
  rw [traceD, ite_eq_right h]

theorem traceD_of_halted (M : TM n) (T : ℕ) {c : Cfg n M.Q} (h : c.state = M.qhalt) :
    M.traceD T c = c := by
  cases T with
  | zero => rfl
  | succ T => rw [traceD, ite_eq_left h]

/-- A run of `T + 1` steps is a run of `T` steps followed by one more. -/
theorem traceD_succ_back (M : TM n) : ∀ (T : ℕ) (c : Cfg n M.Q),
    M.traceD (T + 1) c =
      if (M.traceD T c).state = M.qhalt then M.traceD T c else M.stepCfg (M.traceD T c) := by
  intro T
  induction T with
  | zero =>
      intro c
      by_cases h : c.state = M.qhalt
      · rw [traceD_of_halted M _ h, traceD_zero, ite_eq_left h]
      · rw [traceD_succ_of_not_halted M 0 h, traceD_zero, traceD_zero, ite_eq_right h]
  | succ T ih =>
      intro c
      by_cases h : c.state = M.qhalt
      · rw [traceD_of_halted M _ h, traceD_of_halted M _ h, ite_eq_left h]
      · rw [traceD_succ_of_not_halted M (T + 1) h, traceD_succ_of_not_halted M T h, ih]

/-- A fixed-length run is a `reachesIn` run, stopped early exactly when the machine halts. -/
theorem reachesIn_traceD (M : TM n) (T : ℕ) (c : Cfg n M.Q) :
    ∃ t ≤ T, M.reachesIn t c (M.traceD T c) ∧ (t < T → M.halted (M.traceD T c)) := by
  induction T generalizing c with
  | zero => exact ⟨0, le_rfl, reachesIn.zero, by omega⟩
  | succ T ih =>
      by_cases h : c.state = M.qhalt
      · exact ⟨0, Nat.zero_le _, by rw [traceD_of_halted M _ h]; exact reachesIn.zero,
          fun _ => by rw [traceD_of_halted M _ h]; exact h⟩
      · obtain ⟨t, hle, hreach, hstop⟩ := ih (M.stepCfg c)
        refine ⟨t + 1, by omega, ?_, fun _ => ?_⟩
        · rw [traceD_succ_of_not_halted M T h]
          exact reachesIn.step (step_of_not_halted M h) hreach
        · rw [traceD_succ_of_not_halted M T h]
          exact hstop (by omega)

variable {k : ℕ}

/-- The part of a transition that survives forgetting the guess tape. -/
def visible {Q : Type} (r : Q × (Fin (k + 1) → Γw) × Γw × Dir3 × (Fin (k + 1) → Dir3) × Dir3) :
    Q × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  (r.1, fun j => r.2.1 j.castSucc, r.2.2.1, r.2.2.2.1, fun j => r.2.2.2.2.1 j.castSucc,
    r.2.2.2.2.2)

/-- **The guess protocol.** In an advancing state the machine consumes the cell under the guess
head and moves that head on; in every other state it holds the head still and nothing visible
depends on what the cell holds. The guess tape's contents are never altered. -/
structure GuessProtocol (M : TM (k + 1)) (Adv : M.Q → Bool) : Prop where
  /-- The guess cell is always written back unchanged. -/
  write : ∀ (q : M.Q), q ≠ M.qhalt → ∀ (iHead : Γ) (wHeads : Fin (k + 1) → Γ) (oHead : Γ),
    (M.δ q iHead wHeads oHead).2.1 (Fin.last k) = readBackWrite (wHeads (Fin.last k))
  /-- The guess head advances in advancing states and holds still elsewhere. -/
  dir : ∀ (q : M.Q), q ≠ M.qhalt → ∀ (iHead : Γ) (wHeads : Fin (k + 1) → Γ) (oHead : Γ),
    wHeads (Fin.last k) ≠ Γ.start →
    (M.δ q iHead wHeads oHead).2.2.2.2.1 (Fin.last k) =
      if Adv q then Dir3.right else Dir3.stay
  /-- Outside the advancing states the guess is not consulted. -/
  indep : ∀ (q : M.Q), q ≠ M.qhalt → ¬ Adv q →
    ∀ (iHead : Γ) (ww : Fin k → Γ) (oHead : Γ) (g g' : Γ),
    visible (M.δ q iHead (Fin.snoc ww g) oHead) = visible (M.δ q iHead (Fin.snoc ww g') oHead)

/-- **A run of a fixed length is the deterministic trace.** A machine's step is a function, so
the configuration reached in exactly `t` steps is `TM.traceD t`. -/
theorem traceD_of_reachesIn (M : TM n) : ∀ (t : ℕ) {c c' : Cfg n M.Q},
    M.reachesIn t c c' → M.traceD t c = c' := by
  intro t
  induction t with
  | zero =>
      intro c c' h
      cases h
      rfl
  | succ t ih =>
      intro c c' h
      cases h with
      | step hstep hrest =>
          have hne : c.state ≠ M.qhalt := by
            intro hc
            simp [TM.step, hc] at hstep
          rw [traceD_succ_of_not_halted M t hne]
          have hcfg := hstep
          rw [TM.step_of_not_halted M hne] at hcfg
          rw [Option.some.inj hcfg]
          exact ih hrest

/-- **Traces compose.** -/
theorem traceD_add (M : TM n) : ∀ (a b : ℕ) (c : Cfg n M.Q),
    M.traceD (a + b) c = M.traceD b (M.traceD a c) := by
  intro a
  induction a with
  | zero => intro b c; rw [Nat.zero_add, traceD_zero]
  | succ a ih =>
      intro b c
      by_cases h : c.state = M.qhalt
      · rw [traceD_of_halted M _ h, traceD_of_halted M _ h, traceD_of_halted M _ h]
      · rw [show a + 1 + b = (a + b) + 1 by omega, traceD_succ_of_not_halted M (a + b) h,
          traceD_succ_of_not_halted M a h, ih]

/-- **Once halted, a longer trace stays put.** -/
theorem traceD_of_reachesIn_halted (M : TM n) {t T : ℕ} (hle : t ≤ T) {c c' : Cfg n M.Q}
    (h : M.reachesIn t c c') (hhalt : M.halted c') : M.traceD T c = c' := by
  obtain ⟨d, rfl⟩ : ∃ d, T = t + d := ⟨T - t, by omega⟩
  rw [traceD_add, traceD_of_reachesIn M t h, traceD_of_halted M d hhalt]

end TM

namespace NTM

variable {k : ℕ}

private theorem snoc_init_self' {α : Type} (f : Fin (k + 1) → α) :
    Fin.snoc (fun j => f j.castSucc) (f (Fin.last k)) = f :=
  Fin.snoc_init_self f

open TM in
/-- The transition of `NTM.ofGuess M` is the visible part of `M`'s. -/
theorem ofGuess_δ (M : TM (k + 1)) (b : Bool) (q : M.Q) (iHead : Γ) (ww : Fin k → Γ)
    (oHead : Γ) :
    (ofGuess M).δ b q iHead ww oHead =
      TM.visible (M.δ q iHead (Fin.snoc ww (Γ.ofBool b)) oHead) := rfl

/-- **One step of `M` is one step of `NTM.ofGuess M` along the bit under the guess head.** -/
theorem dropChoice_stepCfg (M : TM (k + 1)) {c : Cfg (k + 1) M.Q} {b : Bool}
    (hread : (c.work (Fin.last k)).read = Γ.ofBool b) :
    dropChoice (M.stepCfg c) = stepCfg (ofGuess M) b (dropChoice c) := by
  have hsnoc : Fin.snoc (fun i : Fin k => (c.work i.castSucc).read) (Γ.ofBool b)
      = fun i => (c.work i).read := by
    rw [← hread]
    exact snoc_init_self' (fun i => (c.work i).read)
  refine Cfg.ext ?_ ?_ ?_ ?_ <;>
    simp only [dropChoice, TM.stepCfg, stepCfg, ofGuess, hsnoc]

/-- Run a nondeterministic machine forward, taking the `i`-th choice at step `i`. Unlike
`NTM.trace`, which consumes its choices from the front, this indexes them absolutely, which is
what a statement about "the step at which a guess was consumed" needs. -/
def nrunAt (N : NTM k) (choices : ℕ → Bool) (c : Cfg k N.Q) : ℕ → Cfg k N.Q
  | 0 => c
  | i + 1 =>
    let cᵢ := nrunAt N choices c i
    if cᵢ.state = N.qhalt then cᵢ else stepCfg N (choices i) cᵢ

@[simp] theorem nrunAt_zero (N : NTM k) (choices : ℕ → Bool) (c : Cfg k N.Q) :
    nrunAt N choices c 0 = c := rfl

theorem nrunAt_succ (N : NTM k) (choices : ℕ → Bool) (c : Cfg k N.Q) (i : ℕ) :
    nrunAt N choices c (i + 1) =
      if (nrunAt N choices c i).state = N.qhalt then nrunAt N choices c i
      else stepCfg N (choices i) (nrunAt N choices c i) := rfl

theorem nrunAt_of_halted (N : NTM k) (choices : ℕ → Bool) {c : Cfg k N.Q}
    (h : c.state = N.qhalt) (i : ℕ) : nrunAt N choices c i = c := by
  induction i with
  | zero => rfl
  | succ i ih => erw [nrunAt_succ, ih, ite_eq_left h]

theorem nrunAt_succ_front (N : NTM k) (choices : ℕ → Bool) {c : Cfg k N.Q}
    (h : c.state ≠ N.qhalt) (i : ℕ) :
    nrunAt N choices c (i + 1)
      = nrunAt N (fun j => choices (j + 1)) (stepCfg N (choices 0) c) i := by
  induction i with
  | zero =>
      erw [nrunAt_succ]
      simp only [nrunAt_zero]
      erw [ite_eq_right h]
  | succ i ih => erw [nrunAt_succ, ih, nrunAt_succ]

/-- The absolutely-indexed run is `NTM.trace`. -/
theorem trace_eq_nrunAt (N : NTM k) (choices : ℕ → Bool) :
    ∀ (T : ℕ) (c : Cfg k N.Q),
      N.trace T (fun i => choices i.val) c = nrunAt N choices c T := by
  intro T
  induction T generalizing choices with
  | zero => intro c; rfl
  | succ T ih =>
      intro c
      by_cases h : c.state = N.qhalt
      · rw [trace, ite_eq_left h, nrunAt_of_halted N choices h]
      · rw [trace_succ_of_not_halted N T _ h, nrunAt_succ_front N choices h]
        exact ih (fun j => choices (j + 1)) _

/-- The bit the machine reads off its guess tape at step `i`. -/
def guessBit (M : TM (k + 1)) (c : Cfg (k + 1) M.Q) (i : ℕ) : Bool :=
  decide (((M.traceD i c).work (Fin.last k)).read = Γ.one)

/-- A step preserves the guess tape and moves its head at most one cell right, so a tape holding
bits for `T + 1` cells still holds them for `T`. -/
theorem boolFrom_stepCfg (M : TM (k + 1)) {Adv : M.Q → Bool} (hP : TM.GuessProtocol M Adv)
    {T : ℕ} {c : Cfg (k + 1) M.Q} (hq : c.state ≠ M.qhalt)
    (h : (c.work (Fin.last k)).BoolFrom (T + 1)) :
    ((M.stepCfg c).work (Fin.last k)).BoolFrom T := by
  have hread : (c.work (Fin.last k)).read ≠ Γ.start := h.read_ne_start
  have hw : (M.stepCfg c).work (Fin.last k)
      = (c.work (Fin.last k)).writeAndMove (TM.readBackWrite (c.work (Fin.last k)).read)
          (if Adv c.state then Dir3.right else Dir3.stay) := by
    show (c.work (Fin.last k)).writeAndMove ((M.δ c.state c.input.read
        (fun i => (c.work i).read) c.output.read).2.1 (Fin.last k))
        ((M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.1
          (Fin.last k)) = _
    rw [hP.write _ hq, hP.dir _ hq _ _ _ hread]
  rw [hw, TM.writeAndMove_readBack _ hread]
  split
  · exact h.move_right
  · exact h.mono (by omega)

/-- **A run of `M` is a trace of `NTM.ofGuess M` along the bits it reads.** -/
theorem dropChoice_traceD (M : TM (k + 1)) {Adv : M.Q → Bool} (hP : TM.GuessProtocol M Adv) :
    ∀ (T : ℕ) (c : Cfg (k + 1) M.Q), (c.work (Fin.last k)).BoolFrom T →
      dropChoice (M.traceD T c)
        = (ofGuess M).trace T (fun i => guessBit M c i.val) (dropChoice c) := by
  intro T
  induction T with
  | zero => intro c _; rfl
  | succ T ih =>
      intro c hbool
      by_cases hhalt : c.state = M.qhalt
      · rw [TM.traceD_of_halted M _ hhalt, trace]
        simp [dropChoice, hhalt, ofGuess]
      · obtain ⟨b, hb⟩ := hbool.read
        have hbit : guessBit M c 0 = b := by
          rw [guessBit, TM.traceD_zero, hb]
          cases b <;> decide
        have hstep : stepCfg (ofGuess M) (guessBit M c 0) (dropChoice c)
            = dropChoice (M.stepCfg c) := by
          rw [hbit]
          exact (dropChoice_stepCfg M hb).symm
        have hshift : ∀ i : ℕ, guessBit M c (i + 1) = guessBit M (M.stepCfg c) i := by
          intro i
          rw [guessBit, guessBit, TM.traceD_succ_of_not_halted M i hhalt]
        rw [TM.traceD_succ_of_not_halted M T hhalt,
          trace_succ_of_not_halted (ofGuess M) T _ (by simpa [dropChoice] using hhalt)]
        dsimp only
        rw [hstep]
        rw [ih (M.stepCfg c) (boolFrom_stepCfg M hP hhalt hbool)]
        congr 1
        funext i
        exact (hshift i.val).symm

/-! ## Every choice sequence comes from a loaded tape -/

/-- Outside the advancing states the choice bit does not matter. -/
theorem stepCfg_indep (M : TM (k + 1)) {Adv : M.Q → Bool} (hP : TM.GuessProtocol M Adv)
    {c : Cfg k M.Q} (hq : c.state ≠ M.qhalt) (h : ¬ Adv c.state) (b b' : Bool) :
    stepCfg (ofGuess M) b c = stepCfg (ofGuess M) b' c := by
  have hind := hP.indep c.state hq h c.input.read (fun i => (c.work i).read) c.output.read
    (Γ.ofBool b) (Γ.ofBool b')
  simp only [stepCfg, ofGuess_δ, hind]

/-- Attach a guess tape to a configuration. -/
def attach {Q : Type} (d : Cfg k Q) (τ : Tape) : Cfg (k + 1) Q where
  state := d.state
  input := d.input
  work := Fin.snoc d.work τ
  output := d.output

@[simp] theorem attach_work_last {Q : Type} (d : Cfg k Q) (τ : Tape) :
    (attach d τ).work (Fin.last k) = τ := by
  simp [attach]

@[simp] theorem dropChoice_attach {Q : Type} (d : Cfg k Q) (τ : Tape) :
    dropChoice (attach d τ) = d := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext i
  simp [dropChoice, attach]

@[simp] theorem attach_state {Q : Type} (d : Cfg k Q) (τ : Tape) :
    (attach d τ).state = d.state := rfl

theorem loadCfg_eq_attach (M : TM (k + 1)) (x : List Bool) (g : ℕ → Bool) :
    loadCfg M x g = attach ((ofGuess M).initCfg x) (loadTape g) := by
  refine Cfg.ext rfl rfl ?_ rfl
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [loadCfg, attach]
  · intro j
    simp [loadCfg, attach]

/-- The largest index below `T` at which `P` holds, or `0` if there is none. -/
def searchIdx (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | T + 1 => if P T then T else searchIdx P T

theorem searchIdx_eq {P : ℕ → Bool} {T i : ℕ} (hi : i < T) (hP : P i = true)
    (huniq : ∀ j, P j = true → j = i) : searchIdx P T = i := by
  induction T with
  | zero => omega
  | succ T ih =>
      rw [searchIdx]
      by_cases h : P T = true
      · rw [ite_eq_left h]
        exact huniq T h
      · rw [ite_eq_right h]
        refine ih ?_
        rcases Nat.lt_or_ge i T with h' | h'
        · exact h'
        · exact absurd ((show i = T by omega) ▸ hP) h

section Cursor

variable {k : ℕ} (M : TM (k + 1)) (Adv : M.Q → Bool) (choices : ℕ → Bool) (d : Cfg k M.Q)

/-- Whether the nondeterministic run consumes a guess at step `i`. -/
def consumes (i : ℕ) : Bool :=
  !(@decide ((nrunAt (ofGuess M) choices d i).state = M.qhalt) (M.decEq _ _)) &&
    Adv (nrunAt (ofGuess M) choices d i).state

/-- Where the guess head sits after `i` steps: one cell on for every guess consumed. -/
def cursor : ℕ → ℕ
  | 0 => 1
  | i + 1 => cursor i + (if consumes M Adv choices d i then 1 else 0)

theorem one_le_cursor (i : ℕ) : 1 ≤ cursor M Adv choices d i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => rw [cursor]; omega

theorem cursor_le_succ (i : ℕ) :
    cursor M Adv choices d i ≤ cursor M Adv choices d (i + 1) := by
  rw [cursor]; omega

theorem cursor_mono : ∀ {i j : ℕ}, i ≤ j →
    cursor M Adv choices d i ≤ cursor M Adv choices d j := by
  intro i j
  induction j with
  | zero => intro h; rw [Nat.le_zero.mp h]
  | succ j ih =>
      intro h
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (cursor_le_succ M Adv choices d j)
      · have hij : i = j + 1 := by omega
        subst hij
        exact le_rfl

theorem cursor_lt_of_consumes {i j : ℕ} (hij : i < j) (hi : consumes M Adv choices d i = true) :
    cursor M Adv choices d i < cursor M Adv choices d j := by
  refine lt_of_lt_of_le ?_ (cursor_mono M Adv choices d hij)
  rw [cursor, ite_eq_left hi]
  omega

theorem cursor_inj_of_consumes {i j : ℕ} (hi : consumes M Adv choices d i = true)
    (hj : consumes M Adv choices d j = true)
    (h : cursor M Adv choices d i = cursor M Adv choices d j) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (cursor_lt_of_consumes M Adv choices d hlt hi))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (cursor_lt_of_consumes M Adv choices d hgt hj))

/-- **The guess string that realizes a choice sequence.** Cell `p + 1` holds the choice made at
the step whose cursor is `p + 1`; cells no advancing step ever reads hold whatever falls out. -/
def guessOf (T : ℕ) (p : ℕ) : Bool :=
  choices (searchIdx (fun i =>
    consumes M Adv choices d i && decide (cursor M Adv choices d i = p + 1)) T)

theorem guessOf_eq {T i : ℕ} (hi : i < T) (hc : consumes M Adv choices d i = true) :
    guessOf M Adv choices d T (cursor M Adv choices d i - 1) = choices i := by
  have hpos := one_le_cursor M Adv choices d i
  rw [guessOf, searchIdx_eq hi (by simp [hc]; omega) ?_]
  intro j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
  exact cursor_inj_of_consumes M Adv choices d hj.1 hc (by omega)

/-- A step moves the guess head on exactly in the advancing states. -/
theorem work_last_stepCfg' {Adv' : M.Q → Bool} (hP : TM.GuessProtocol M Adv')
    (c : Cfg (k + 1) M.Q) (hq : c.state ≠ M.qhalt)
    (hread : (c.work (Fin.last k)).read ≠ Γ.start) :
    (M.stepCfg c).work (Fin.last k)
      = (c.work (Fin.last k)).move (if Adv' c.state then Dir3.right else Dir3.stay) := by
  have hw : (M.stepCfg c).work (Fin.last k)
      = (c.work (Fin.last k)).writeAndMove (TM.readBackWrite (c.work (Fin.last k)).read)
          (if Adv' c.state then Dir3.right else Dir3.stay) := by
    show (c.work (Fin.last k)).writeAndMove ((M.δ c.state c.input.read
        (fun i => (c.work i).read) c.output.read).2.1 (Fin.last k))
        ((M.δ c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.1
          (Fin.last k)) = _
    rw [hP.write _ hq, hP.dir _ hq _ _ _ hread]
  rw [hw, TM.writeAndMove_readBack _ hread]

/-- **Every choice sequence is realized by a loaded guess tape.** Running `M` on the tape
`NTM.guessOf` builds reproduces, step for step, the path of `NTM.ofGuess M` along `choices`: the
guesses land where the advancing steps read them, and the bits the machine never looks at are
free. -/
theorem traceD_guessOf {Adv : M.Q → Bool} (hP : TM.GuessProtocol M Adv) (T : ℕ) :
    ∀ i ≤ T,
      dropChoice (M.traceD i (attach d (loadTape (guessOf M Adv choices d T))))
          = nrunAt (ofGuess M) choices d i ∧
        (M.traceD i (attach d (loadTape (guessOf M Adv choices d T)))).work (Fin.last k)
          = ⟨cursor M Adv choices d i, (loadTape (guessOf M Adv choices d T)).cells⟩ := by
  intro i
  induction i with
  | zero =>
      intro _
      refine ⟨by erw [nrunAt_zero, TM.traceD_zero, dropChoice_attach], ?_⟩
      show (attach d (loadTape (guessOf M Adv choices d T))).work (Fin.last k) = _
      rw [attach_work_last]
      rfl
  | succ i ih =>
      intro hle
      obtain ⟨ihd, ihw⟩ := ih (by omega)
      have hilt : i < T := by omega
      set g := guessOf M Adv choices d T with hg
      set c₀ := attach d (loadTape g) with hc₀
      set cᵢ := M.traceD i c₀ with hcᵢ
      have hstate : cᵢ.state = (nrunAt (ofGuess M) choices d i).state := by
        rw [← ihd]; rfl
      by_cases hhalt : cᵢ.state = M.qhalt
      · have hcons : consumes M Adv choices d i = false := by
          simp [consumes, ← hstate, hhalt]
        have hnhalt : (nrunAt (ofGuess M) choices d i).state = (ofGuess M).qhalt := by
          rw [← hstate]; exact hhalt
        refine ⟨?_, ?_⟩
        · erw [TM.traceD_succ_back, ite_eq_left hhalt, ihd, nrunAt_succ, ite_eq_left hnhalt]
        · erw [TM.traceD_succ_back, ite_eq_left hhalt, ihw, cursor, hcons]
          simp
      · have hcells : (cᵢ.work (Fin.last k)).read
            = Γ.ofBool (g (cursor M Adv choices d i - 1)) := by
          have hpos := one_le_cursor M Adv choices d i
          rw [ihw]
          show (loadTape g).cells (cursor M Adv choices d i) = _
          have hc := loadTape_cells_succ g (cursor M Adv choices d i - 1)
          rwa [show cursor M Adv choices d i - 1 + 1 = cursor M Adv choices d i by omega] at hc
        have hne : (cᵢ.work (Fin.last k)).read ≠ Γ.start := by
          rw [hcells]; exact Γ.ofBool_ne_start _
        have hstep : M.traceD (i + 1) c₀ = M.stepCfg cᵢ := by
          erw [TM.traceD_succ_back, ite_eq_right hhalt]
        have hnstep : nrunAt (ofGuess M) choices d (i + 1)
            = stepCfg (ofGuess M) (choices i) (nrunAt (ofGuess M) choices d i) := by
          erw [nrunAt_succ, ite_eq_right (by rw [← hstate]; exact hhalt)]
        by_cases hadv : Adv cᵢ.state
        · have hcons : consumes M Adv choices d i = true := by
            simp [consumes, ← hstate, hhalt, hadv]
          have hbit : g (cursor M Adv choices d i - 1) = choices i :=
            guessOf_eq M Adv choices d hilt hcons
          refine ⟨?_, ?_⟩
          · rw [hstep, hnstep, ← ihd]
            exact dropChoice_stepCfg M (by rw [hcells, hbit])
          · rw [hstep, work_last_stepCfg' M hP cᵢ hhalt hne, ite_eq_left hadv, ihw, cursor, hcons]
            rfl
        · have hcons : consumes M Adv choices d i = false := by
            simp [consumes, ← hstate, hadv]
          refine ⟨?_, ?_⟩
          · rw [hstep, hnstep, ← ihd]
            rw [dropChoice_stepCfg M hcells]
            exact stepCfg_indep M hP hhalt hadv _ _
          · rw [hstep, work_last_stepCfg' M hP cᵢ hhalt hne, ite_eq_right hadv, ihw, cursor, hcons]
            rfl

end Cursor

/-- **A path of `NTM.ofGuess M` is a run of `M` on a loaded guess tape.** This is the transfer a
nondeterministic construction is built on: design and verify `M` deterministically, with its
guesses arriving on the last work tape, and read the result off here as a statement about the
paths of `NTM.ofGuess M`. Unlike `NTM.ofGuess_trace` it asks nothing of `M` between guesses, so
`M` may be assembled from the ordinary deterministic combinators. -/
theorem exists_loadTape (M : TM (k + 1)) {Adv : M.Q → Bool} (hP : TM.GuessProtocol M Adv)
    (x : List Bool) (T : ℕ) (choices : Fin T → Bool) :
    ∃ (g : ℕ → Bool) (c' : Cfg (k + 1) M.Q) (t : ℕ), t ≤ T ∧
      M.reachesIn t (loadCfg M x g) c' ∧ (t < T → M.halted c') ∧
      dropChoice c' = (ofGuess M).trace T choices ((ofGuess M).initCfg x) := by
  classical
  set ch : ℕ → Bool := fun i => if h : i < T then choices ⟨i, h⟩ else false with hch
  refine ⟨guessOf M Adv ch ((ofGuess M).initCfg x) T,
    M.traceD T (loadCfg M x (guessOf M Adv ch ((ofGuess M).initCfg x) T)), ?_⟩
  obtain ⟨t, hle, hreach, hstop⟩ :=
    TM.reachesIn_traceD M T (loadCfg M x (guessOf M Adv ch ((ofGuess M).initCfg x) T))
  refine ⟨t, hle, hreach, hstop, ?_⟩
  have hmain := (traceD_guessOf M ch ((ofGuess M).initCfg x) hP T T le_rfl).1
  have hfun : (ofGuess M).trace T (fun i => ch i.val) ((ofGuess M).initCfg x)
      = (ofGuess M).trace T choices ((ofGuess M).initCfg x) := by
    congr 1
    funext i
    simp [hch, i.isLt]
  rw [loadCfg_eq_attach, ← hfun, trace_eq_nrunAt]
  exact hmain

end NTM

end Complexity

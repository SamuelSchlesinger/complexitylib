/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Computability.Languages.SyntacticMonoid
public import Mathlib.Computability.DFA
public import Complexitylib.Classes.Containments
public import Complexitylib.Classes.L
import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner

/-!
# Regular languages in Complexitylib's classes

Every language that is regular in the sense shared by Mathlib and CSLib
(`Language.IsRegular`: accepted by a finite deterministic automaton) is decided
by Complexitylib's finite-state scanner `TM.scannerTM`, which runs the
automaton left to right over the input. The scanner halts in `n + 2` steps, has
no work tapes, never moves its input head past the first blank after the input,
and never moves its output head past the verdict cell. It therefore decides the
language in time `n + 2` and in zero auxiliary space under
`Cfg.WithinDecisionSpace`, and, since its output head never moves left, it is a
transducer. Regular languages thus lie in `DTIME(n + 2)`, `P`, `DSPACE(0)`,
and `L`.

CSLib's characterizations of regularity then transfer these memberships to
the languages of finite nondeterministic automata, of finite two-way
nondeterministic automata, of regular expressions, and to preimages of subsets
of finite monoids under homomorphisms from the free monoid on `Bool`.

## Main results

- `Complexity.TM.scannerTM_decidesInSpace` — the scanner decides in space `0`
- `Complexity.TM.scannerTM_isTransducer` — the scanner is a transducer
- `Complexity.mem_DTIME_of_isRegular` — regular languages are in `DTIME(n + 2)`
- `Complexity.mem_P_of_isRegular` — regular languages are in `P`
- `Complexity.mem_DSPACE_zero_of_isRegular` — regular languages are in
  `DSPACE(0)`
- `Complexity.mem_L_of_isRegular` — regular languages are in `L`
- `Complexity.mem_P_of_nfa`, `Complexity.mem_L_of_nfa` — CSLib's finite
  nondeterministic automata
- `Complexity.mem_P_of_twoWayNA`, `Complexity.mem_L_of_twoWayNA` — CSLib's
  finite two-way nondeterministic automata
- `Complexity.mem_P_of_finite_monoid`, `Complexity.mem_L_of_finite_monoid` —
  languages recognized by finite monoids
- `Complexity.mem_L_of_regex` — languages of regular expressions

CSLib's closure properties of regular languages (union, intersection,
complement, concatenation, Kleene star, reversal, inverse homomorphic images)
combine with `mem_L_of_isRegular` to give `L`-membership of the resulting
languages directly.
-/

public section

namespace Complexity

namespace TM

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reachable-configuration invariant of the scanner: the input tape is never
modified; in the start state both heads are at cell 0; in a scan state the
input head is at most one past the input and the output head sits on the
verdict cell, which does not hold `▷`; after halting the input head is at most
one past the input and the output head is at most at the verdict cell. -/
private theorem scannerTM_reaches_inv
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw) (x : List Bool)
    {c : Cfg 0 (scannerTM s₀ scanStep finalOutput).Q}
    (h : (scannerTM s₀ scanStep finalOutput).reaches
      ((scannerTM s₀ scanStep finalOutput).initCfg x) c) :
    c.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      (c.state = ScannerPhase.start → c.input.head = 0 ∧ c.output.head = 0 ∧
        c.output.cells 1 ≠ Γ.start) ∧
      (∀ s, c.state = ScannerPhase.scan s → c.input.head ≤ x.length + 1 ∧
        c.output.head = 1 ∧ c.output.cells 1 ≠ Γ.start) ∧
      (c.state = ScannerPhase.done → c.input.head ≤ x.length + 1 ∧ c.output.head ≤ 1) := by
  induction h with
  | refl =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro _; exact ⟨rfl, rfl, by simp [Tape.init]⟩
    · intro s hs; simp [scannerTM] at hs
    · intro hs; simp [scannerTM] at hs
  | tail _ hstep ih =>
    rename_i c₁ c₂ _
    obtain ⟨hcells, hstart, hscan, hdone⟩ := ih
    rcases hq : c₁.state with _ | s | _
    · obtain ⟨hih, hoh, hoc⟩ := hstart hq
      simp only [TM.stepRel, TM.step, hq, scannerTM, reduceCtorEq, ↓reduceIte] at hstep
      obtain rfl := Option.some.inj hstep
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Tape.move] using hcells
      · intro h; cases h
      · intro s' _
        refine ⟨?_, ?_, ?_⟩
        · simp [Tape.move, hih]
        · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]
        · simpa [Tape.writeAndMove, Tape.move, Tape.write, hoh] using hoc
      · intro h; cases h
    · obtain ⟨hih, hoh, hoc⟩ := hscan s hq
      have hne : c₁.output.read ≠ Γ.start := by simpa [Tape.read, hoh] using hoc
      have hodir : idleDir c₁.output.read = Dir3.stay := by simp [idleDir, hne]
      by_cases hb : c₁.input.read = Γ.blank
      · simp only [TM.stepRel, TM.step, hq, scannerTM, reduceCtorEq, ↓reduceIte, hb,
          hodir] at hstep
        obtain rfl := Option.some.inj hstep
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Tape.move_cells]; exact hcells
        · intro h; cases h
        · intro s' h; cases h
        · intro _
          refine ⟨?_, ?_⟩
          · simpa [Tape.move, idleDir] using hih
          · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hoh]
      · simp only [TM.stepRel, TM.step, hq, scannerTM, reduceCtorEq, ↓reduceIte, hb,
          hodir] at hstep
        obtain rfl := Option.some.inj hstep
        have hlt : c₁.input.head ≤ x.length := by
          by_contra hgt
          apply hb
          have : c₁.input.head = x.length + 1 := by omega
          simp only [Tape.read, hcells, this]
          exact Tape.init_ofBool_cells_ge x x.length le_rfl
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [Tape.move] using hcells
        · intro h; cases h
        · intro s' _
          refine ⟨?_, ?_, ?_⟩
          · simp [Tape.move]; omega
          · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hoh]
          · rw [tape_readBackWrite_preserves c₁.output _ (Or.inr hne)]; exact hoc
        · intro h; cases h
    · simp [TM.stepRel, TM.step, hq, scannerTM] at hstep

/-- The scanner never moves its output head left, so it is a transducer. -/
theorem scannerTM_isTransducer
    (s₀ : S) (scanStep : S → Bool → S) (finalOutput : S → Γw) :
    (scannerTM s₀ scanStep finalOutput).IsTransducer := by
  have hidle : ∀ g, idleDir g ≠ Dir3.left := fun g => by
    unfold idleDir; split <;> simp
  intro q iHead wHeads oHead
  cases q with
  | start => simp [scannerTM]
  | scan s =>
    simp only [scannerTM]
    split
    · exact hidle _
    · exact hidle _
  | done => exact hidle _

/-- **The scanner runs in zero auxiliary space.** Whenever a language `L` is
characterized by a decision predicate `accept : S → Bool` applied to the fold,
the scanner decides `L` in space `0` under `Cfg.WithinDecisionSpace`: it has no
work tapes, its input head never passes the first blank after the input, and
its output head never passes the verdict cell. -/
theorem scannerTM_decidesInSpace
    (s₀ : S) (scanStep : S → Bool → S) (accept : S → Bool)
    {L : Language}
    (hL : ∀ x, x ∈ L ↔ accept (x.foldl scanStep s₀) = true) :
    TM.DecidesInSpace
      (scannerTM s₀ scanStep (fun s => if accept s then .one else .zero))
      L (fun _ => 0) := by
  refine ⟨fun x c hc => ?_, fun x => ?_⟩
  · obtain ⟨-, hstart, hscan, hdone⟩ := scannerTM_reaches_inv _ _ _ x hc
    refine ⟨⟨fun i => i.elim0, ?_⟩, ?_⟩ <;> rcases hq : c.state with _ | s | _
    · simp [(hstart hq).1]
    · exact (hscan s hq).1
    · exact (hdone hq).1
    · simp [(hstart hq).2.1]
    · simp [(hscan s hq).2.1]
    · exact (hdone hq).2
  · obtain ⟨c', t, -, hreach, hhalt, hmem, hnmem⟩ :=
      scannerTM_decidesInTime s₀ scanStep accept hL x
    exact ⟨c', reaches_of_reachesIn hreach, hhalt, hmem, hnmem⟩

end TM

/-- A regular language is decided by a single zero-work-tape transducer that
runs in time `n + 2` and in zero auxiliary space: the finite-state scanner
running a deterministic automaton for the language. -/
private theorem exists_scanner_of_isRegular {A : Language} (hA : Language.IsRegular A) :
    ∃ tm : TM 0, tm.IsTransducer ∧ tm.DecidesInTime A (fun n => n + 2) ∧
      tm.DecidesInSpace A (fun _ => 0) := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := hA
  have hL : ∀ x, x ∈ M.accepts ↔ decide (x.foldl M.step M.start ∈ M.accept) = true :=
    fun x => by
      rw [decide_eq_true_iff]
      exact Iff.rfl
  exact ⟨_, TM.scannerTM_isTransducer _ _ _,
    TM.scannerTM_decidesInTime M.start M.step (fun s => decide (s ∈ M.accept)) hL,
    TM.scannerTM_decidesInSpace M.start M.step (fun s => decide (s ∈ M.accept)) hL⟩

/-- **Regular languages are decidable in linear time.** Every language that is
regular in the sense shared by Mathlib and CSLib (accepted by a finite
deterministic automaton) is decided in `n + 2` steps by the finite-state
scanner that runs the automaton. -/
theorem mem_DTIME_of_isRegular {A : Language} (hA : Language.IsRegular A) :
    A ∈ DTIME (fun n => n + 2) := by
  obtain ⟨tm, -, htime, -⟩ := exists_scanner_of_isRegular hA
  exact ⟨0, tm, fun n => n + 2, htime, BigO.refl _⟩

/-- **Regular languages are in `P`.** -/
theorem mem_P_of_isRegular {A : Language} (hA : Language.IsRegular A) : A ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ (mem_DTIME_of_isRegular hA)⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

/-- **Regular languages are decidable in zero auxiliary space.** Every regular
language is decided by the finite-state scanner, which uses no work tape and
keeps its input and output heads within the free region of
`Cfg.WithinDecisionSpace`. -/
theorem mem_DSPACE_zero_of_isRegular {A : Language} (hA : Language.IsRegular A) :
    A ∈ DSPACE (fun _ => 0) := by
  obtain ⟨tm, -, -, hspace⟩ := exists_scanner_of_isRegular hA
  exact ⟨0, tm, fun _ => 0, hspace, BigO.refl _⟩

/-- **Regular languages lie in every space class.** Zero auxiliary space is
`O(S)` for every bound `S`. -/
theorem mem_DSPACE_of_isRegular {A : Language} (hA : Language.IsRegular A)
    (S : ℕ → ℕ) : A ∈ DSPACE S :=
  DSPACE_mono (BigO.of_le fun _ => Nat.zero_le _) (mem_DSPACE_zero_of_isRegular hA)

/-- **Regular languages are in `L`.** The finite-state scanner is a transducer
deciding the language in zero auxiliary space. -/
theorem mem_L_of_isRegular {A : Language} (hA : Language.IsRegular A) : A ∈ L := by
  obtain ⟨tm, htrans, -, hspace⟩ := exists_scanner_of_isRegular hA
  exact ⟨0, tm, fun _ => 0, htrans, hspace, BigO.of_le fun _ => Nat.zero_le _⟩

/-! ### CSLib automata and algebraic characterizations -/

/-- **Finite nondeterministic automata decide in polynomial time.** Every
language accepted by a finite nondeterministic automaton from CSLib's automata
library is in `P`: CSLib's subset construction makes it regular, and the
scanner runs the resulting deterministic automaton. -/
theorem mem_P_of_nfa {State : Type} [Finite State]
    (nfa : Cslib.Automata.NA.FinAcc State Bool) :
    (Cslib.Automata.Acceptor.language nfa : Language) ∈ P :=
  mem_P_of_isRegular
    (Cslib.Language.IsRegular.iff_nfa.mpr ⟨State, inferInstance, nfa, rfl⟩)

/-- **Finite nondeterministic automata decide in logarithmic space.** Every
language accepted by a finite nondeterministic automaton from CSLib's automata
library is in `L`. -/
theorem mem_L_of_nfa {State : Type} [Finite State]
    (nfa : Cslib.Automata.NA.FinAcc State Bool) :
    (Cslib.Automata.Acceptor.language nfa : Language) ∈ L :=
  mem_L_of_isRegular
    (Cslib.Language.IsRegular.iff_nfa.mpr ⟨State, inferInstance, nfa, rfl⟩)

/-- **Two-way automata decide in polynomial time.** Every language accepted by
a finite two-way nondeterministic automaton from CSLib is in `P`: CSLib proves
such languages regular. -/
theorem mem_P_of_twoWayNA {State : Type} [Finite State]
    (a : Cslib.Automata.TwoWayNA State Bool) :
    (Cslib.Automata.Acceptor.language a : Language) ∈ P :=
  mem_P_of_isRegular
    (Cslib.Language.IsRegular.iff_twoWayNA.mpr ⟨State, inferInstance, a, rfl⟩)

/-- **Two-way automata decide in logarithmic space.** Every language accepted
by a finite two-way nondeterministic automaton from CSLib is in `L`. -/
theorem mem_L_of_twoWayNA {State : Type} [Finite State]
    (a : Cslib.Automata.TwoWayNA State Bool) :
    (Cslib.Automata.Acceptor.language a : Language) ∈ L :=
  mem_L_of_isRegular
    (Cslib.Language.IsRegular.iff_twoWayNA.mpr ⟨State, inferInstance, a, rfl⟩)

/-- **Finite-monoid recognizable languages are in `P`.** The preimage of any
subset of a finite monoid under a monoid homomorphism from the free monoid on
`Bool` is in `P`: CSLib proves such preimages regular. -/
theorem mem_P_of_finite_monoid {M : Type*} [Monoid M] [Finite M]
    (f : FreeMonoid Bool →* M) (s : Set M) :
    ((f ∘ FreeMonoid.ofList) ⁻¹' s : Language) ∈ P :=
  mem_P_of_isRegular (Language.IsRegular.of_finite_monoid f s)

/-- **Finite-monoid recognizable languages are in `L`.** The preimage of any
subset of a finite monoid under a monoid homomorphism from the free monoid on
`Bool` is in `L`. -/
theorem mem_L_of_finite_monoid {M : Type*} [Monoid M] [Finite M]
    (f : FreeMonoid Bool →* M) (s : Set M) :
    ((f ∘ FreeMonoid.ofList) ⁻¹' s : Language) ∈ L :=
  mem_L_of_isRegular (Language.IsRegular.of_finite_monoid f s)

/-- **Regular expressions match in logarithmic space.** The language matched
by any regular expression over `Bool` is in `L`, since CSLib proves it
regular. -/
theorem mem_L_of_regex (r : RegularExpression Bool) :
    (r.matches' : Language) ∈ L :=
  mem_L_of_isRegular Cslib.Language.IsRegular.regex

end Complexity

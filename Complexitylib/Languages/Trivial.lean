/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.P
public import Complexitylib.Classes.Containments
public import Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# Trivial languages: `∅` and `Set.univ`

The two easiest languages to decide, along with their complexity. Both are
decided by `writeTM` — a machine that writes a fixed symbol to the output
tape and halts in constant time — and therefore belong to every standard
complexity class.

## Main definitions

- `Language.empty` — alias for `∅`.
- `Language.univ`  — alias for `Set.univ`.

## Main results

- `empty_in_DTIME`, `univ_in_DTIME` — both are in `DTIME (fun _ => 3)`.
- `empty_mem_P`, `univ_mem_P`
- `empty_mem_NP`, `univ_mem_NP`
- `empty_mem_BPP`, `univ_mem_BPP`
- `empty_mem_PSPACE`, `univ_mem_PSPACE`
- `empty_mem_EXP`, `univ_mem_EXP`
-/

@[expose] public section

namespace Complexity

open Complexity

namespace Language

/-- The empty language (no strings accepted). -/
abbrev empty : Language := (∅ : Set (List Bool))

/-- The universal language (all strings accepted). -/
abbrev univ : Language := Set.univ

end Language

namespace TM

variable {n : ℕ}

/-- `Tape.init []` is the canonical output-tape initial value: cell 0 is `▷`,
    every other cell is `□`, and the head is at position 0. This is exactly
    the well-formedness precondition of `writeTM_hoareTime` with `B = 0`. -/
theorem Tape.init_nil_wf :
    (Tape.init []).cells 0 = Γ.start ∧
    (∀ j, j ≥ 1 → (Tape.init []).cells j ≠ Γ.start) ∧
    (Tape.init []).head ≤ 0 := by
  refine ⟨rfl, fun j hj => ?_, le_refl _⟩
  have hj' : j ≠ 0 := by omega
  simp [Tape.init, hj']

/-- **`writeTM` halts on every input in 3 steps with `sym` on output cell 1.**

    Specialization of `writeTM_hoareTime` (`B = 0`) to the initial
    configuration, packaged in the exact form required by `DecidesInTime`. -/
theorem writeTM_decidesInTime_const (sym : Γw) (x : List Bool) :
    ∃ c' t, t ≤ 3 ∧
      (writeTM (n := n) sym).reachesIn t ((writeTM sym).initCfg x) c' ∧
      (writeTM sym).halted c' ∧
      c'.output.cells 1 = sym.toΓ := by
  obtain ⟨c', t, hle, hreach, hhalt, hpost⟩ :=
    writeTM_hoareTime (n := n) sym 0
      (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
      Tape.init_nil_wf
  exact ⟨c', t, by omega, hreach, hhalt, hpost⟩

end TM

/-- **The empty language is decidable in constant time.** `writeZeroTM` always
    writes `0` to output cell 1 and halts in at most 3 steps. -/
theorem empty_in_DTIME : Language.empty ∈ DTIME (fun _ => 3) := by
  refine ⟨0, TM.writeZeroTM, fun _ => 3, ?_, BigO.refl _⟩
  intro x
  obtain ⟨c', t, hle, hreach, hhalt, hout⟩ :=
    TM.writeTM_decidesInTime_const (n := 0) .zero x
  refine ⟨c', t, hle, hreach, hhalt, ?_, ?_⟩
  · intro h; exact absurd h (by simp)
  · intro _; simpa using hout

/-- **The universal language is decidable in constant time.** `writeOneTM`
    always writes `1` to output cell 1 and halts in at most 3 steps. -/
theorem univ_in_DTIME : Language.univ ∈ DTIME (fun _ => 3) := by
  refine ⟨0, TM.writeOneTM, fun _ => 3, ?_, BigO.refl _⟩
  intro x
  obtain ⟨c', t, hle, hreach, hhalt, hout⟩ :=
    TM.writeTM_decidesInTime_const (n := 0) .one x
  refine ⟨c', t, hle, hreach, hhalt, ?_, ?_⟩
  · intro _; simpa using hout
  · intro h; exact absurd (Set.mem_univ x) h

-- ════════════════════════════════════════════════════════════════════════
-- Derived class memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`∅ ∈ P`.** -/
theorem empty_mem_P : Language.empty ∈ P :=
  Set.mem_iUnion.mpr ⟨0, DTIME_mono (BigO.const_le_pow 3 0) empty_in_DTIME⟩

/-- **`Set.univ ∈ P`.** -/
theorem univ_mem_P : Language.univ ∈ P :=
  Set.mem_iUnion.mpr ⟨0, DTIME_mono (BigO.const_le_pow 3 0) univ_in_DTIME⟩

/-- **`∅ ∈ NP`.** -/
theorem empty_mem_NP : Language.empty ∈ NP := P_subset_NP empty_mem_P

/-- **`Set.univ ∈ NP`.** -/
theorem univ_mem_NP : Language.univ ∈ NP := P_subset_NP univ_mem_P

/-- **`∅ ∈ BPP`.** -/
theorem empty_mem_BPP : Language.empty ∈ BPP := P_subset_BPP empty_mem_P

/-- **`Set.univ ∈ BPP`.** -/
theorem univ_mem_BPP : Language.univ ∈ BPP := P_subset_BPP univ_mem_P

/-- **`∅ ∈ PSPACE`.** -/
theorem empty_mem_PSPACE : Language.empty ∈ PSPACE := P_subset_PSPACE empty_mem_P

/-- **`Set.univ ∈ PSPACE`.** -/
theorem univ_mem_PSPACE : Language.univ ∈ PSPACE := P_subset_PSPACE univ_mem_P

/-- **`∅ ∈ EXP`.** -/
theorem empty_mem_EXP : Language.empty ∈ EXP := P_subset_EXP empty_mem_P

/-- **`Set.univ ∈ EXP`.** -/
theorem univ_mem_EXP : Language.univ ∈ EXP := P_subset_EXP univ_mem_P

/-- **`∅ ∈ PP`.** -/
theorem empty_mem_PP : Language.empty ∈ PP := P_subset_PP empty_mem_P

/-- **`Set.univ ∈ PP`.** -/
theorem univ_mem_PP : Language.univ ∈ PP := P_subset_PP univ_mem_P

/-- **`∅ ∈ NEXP`.** -/
theorem empty_mem_NEXP : Language.empty ∈ NEXP := P_subset_NEXP empty_mem_P

/-- **`Set.univ ∈ NEXP`.** -/
theorem univ_mem_NEXP : Language.univ ∈ NEXP := P_subset_NEXP univ_mem_P

end Complexity

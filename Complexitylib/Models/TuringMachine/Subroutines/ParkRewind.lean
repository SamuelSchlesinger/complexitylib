/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Subroutines.RewindList
public import Complexitylib.Models.TuringMachine.Combinators.Internal.SeqChain

/-!
# Putting every head back where a stage expects it

A simulated machine leaves its heads wherever its run ended — possibly on the left marker, since
a machine may halt immediately after stepping left onto it. Everything downstream wants heads
parked past the marker, and the tapes a stage will read again want them back at cell one.

`TM.parkRewindTM` does both: one parking step for every tape, then a rewind of the input tape and
of each named work tape. It is the stage that separates a simulation from whatever reads its
results.

## Main results

- `TM.parkRewindTM` — park everything, then rewind the input and the named work tapes
- `TM.parkRewindTM_hoareTime` — its contract, through fully pinned tape states
- `TM.parkRewindWorkTM`, `TM.parkRewindWorkTM_hoareTime` — the same for the work tapes alone,
  leaving the input head where the stage left it
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Park every head past the marker, then rewind the input tape and the named work tapes to
cell one. -/
def parkRewindTM (targets : List (Fin n)) : TM n :=
  seqTM skipTM (bigSeqTM [rewindInputTM, bigSeqTM (targets.map rewindWorkTM)])

/-- A tape with its marker only at cell zero, parked at `max head 1`. -/
def parkTape (t : Tape) : Tape := ⟨max t.head 1, t.cells⟩

/-- Parking a tape whose head is already off the left marker changes nothing. -/
theorem parkTape_eq_self {t : Tape} (h : 1 ≤ t.head) : parkTape t = t := by
  cases t
  simp only [parkTape, Tape.mk.injEq, and_true]
  exact max_eq_left h

theorem parkTape_parked {t : Tape} (h : Tape.StartInvariant t) : Parked (parkTape t) :=
  ⟨le_max_right _ _, fun j hj => h.2 j hj⟩

theorem rewound_parked {t : Tape} (h : Tape.StartInvariant t) :
    Parked (⟨1, t.cells⟩ : Tape) :=
  ⟨le_refl 1, fun j hj => h.2 j hj⟩

/-- **The cleanup stage's contract.** Every head ends parked; the input tape and the named work
tapes end at cell one, with their contents untouched. Only `Tape.StartInvariant` is asked of the
starting tapes — a head may still be sitting on the marker, which is exactly the state a halted
simulation can leave behind. -/
theorem parkRewindTM_hoareTime (targets : List (Fin n)) (hnodup : targets.Nodup) (B : ℕ)
    (hB : 1 ≤ B) (I₀ : Tape) (W₀ : Fin n → Tape) (O₀ : Tape)
    (hI : Tape.StartInvariant I₀) (hW : ∀ i, Tape.StartInvariant (W₀ i))
    (hO : Tape.StartInvariant O₀)
    (hIB : I₀.head ≤ B) (hWB : ∀ j, j ∈ targets → (W₀ j).head ≤ B) :
    (parkRewindTM targets).HoareTime
      (fun inp work out => inp = I₀ ∧ work = W₀ ∧ out = O₀)
      (fun inp work out => inp = (⟨1, I₀.cells⟩ : Tape) ∧
        work = (fun j => if j ∈ targets then (⟨1, (W₀ j).cells⟩ : Tape) else parkTape (W₀ j)) ∧
        out = parkTape O₀)
      (1 + 1 + (2 * (max (B + 2) (targets.length * (B + 3) + 1) + 1) + 1)) := by
  classical
  set W1 : Fin n → Tape := fun j => parkTape (W₀ j) with hW1def
  set W3 : Fin n → Tape :=
    fun j => if j ∈ targets then (⟨1, (W₀ j).cells⟩ : Tape) else parkTape (W₀ j) with hW3def
  set I1 : Tape := parkTape I₀ with hI1def
  set I2 : Tape := (⟨1, I₀.cells⟩ : Tape) with hI2def
  set O1 : Tape := parkTape O₀ with hO1def
  have hW1P : ∀ j, Parked (W1 j) := fun j => parkTape_parked (hW j)
  have hW3P : ∀ j, Parked (W3 j) := by
    intro j
    simp only [hW3def]
    split
    · exact rewound_parked (hW j)
    · exact parkTape_parked (hW j)
  have hI1P : Parked I1 := parkTape_parked hI
  have hI2P : Parked I2 := rewound_parked hI
  have hO1P : Parked O1 := parkTape_parked hO
  set b := max (B + 2) (targets.length * (B + 3) + 1) with hbdef
  -- Stage one: park every head.
  have hpark : (skipTM (n := n)).HoareTime
      (fun inp work out => inp = I₀ ∧ work = W₀ ∧ out = O₀)
      (fun inp work out => inp = I1 ∧ work = W1 ∧ out = O1) 1 := by
    refine (parkAll_hoareTime I₀ W₀ O₀ hI hW hO).strengthen_post ?_
    rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, funext hw, ho⟩
  -- The transition into stage two is the identity on parked tapes.
  have htrans : ∀ inp work out, (inp = I1 ∧ work = W1 ∧ out = O1) →
      (transitionInput inp = I1 ∧ (fun i => transitionTape (work i)) = W1 ∧
        transitionTape out = O1) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨transitionInput_eq_self hI1P.read_ne_start,
      funext fun i => transitionTape_eq_self (hW1P i).read_ne_start,
      transitionTape_eq_self hO1P.read_ne_start⟩
  -- Stages two and three: rewind the input, then the named work tapes.
  have hrest : (bigSeqTM [rewindInputTM, bigSeqTM (targets.map rewindWorkTM)]).HoareTime
      (fun inp work out => inp = I1 ∧ work = W1 ∧ out = O1)
      (fun inp work out => inp = I2 ∧ work = W3 ∧ out = O1) (2 * (b + 1) + 1) := by
    refine (bigSeqTM_hoareTime_pinned_gen [rewindInputTM, bigSeqTM (targets.map rewindWorkTM)]
      (fun k => if k = 0 then I1 else I2) (fun k => if k ≤ 1 then W1 else W3)
      (fun _ => O1) b ?_ ?_ (fun _ => hO1P) ?_).consequence
      (fun _ _ _ h => h) (fun _ _ _ h => h) (le_refl _)
    · intro k
      split
      · exact hI1P
      · exact hI2P
    · intro k i
      split
      · exact hW1P i
      · exact hW3P i
    · intro k hk
      match k, hk with
      | 0, _ =>
        show (rewindInputTM (n := n)).HoareTime _ _ _
        refine ((rewindInputTM_hoareTime_frame (n := n) B
          (P := fun inp work out => inp.cells = I₀.cells ∧ work = W1 ∧ out = O1)
          ?_).consequence ?_ ?_ (le_max_left _ _))
        · rintro inp work out inp' work' out' ⟨hc, hw, ho⟩ hc' _ hkeep hout'
          exact ⟨hc'.trans hc, hkeep.trans hw, hout'.trans ho⟩
        · rintro inp work out ⟨rfl, rfl, rfl⟩
          exact ⟨hI.1, fun j hj => hI.2 j hj, by
              show max I₀.head 1 ≤ B
              omega,
            hO1P.read_ne_start, hO1P.1,
            fun i => ⟨(hW1P i).read_ne_start, (hW1P i).1⟩, rfl, rfl, rfl⟩
        · rintro inp work out ⟨hh, hc, hw, ho⟩
          exact ⟨Tape.ext hh hc, hw, ho⟩
      | 1, _ =>
        show (bigSeqTM (targets.map rewindWorkTM)).HoareTime _ _ _
        refine ((rewindList_hoareTime targets hnodup B I2 W1 O1 hI2P hO1P hW1P ?_).strengthen_post
          ?_).mono_bound (le_max_right _ _)
        · intro j hj
          refine ⟨(hW j).1, ?_⟩
          show max (W₀ j).head 1 ≤ B
          have := hWB j hj
          omega
        · rintro inp work out ⟨rfl, rfl, hin, hout⟩
          refine ⟨rfl, funext fun j => ?_, rfl⟩
          by_cases hj : j ∈ targets
          · rw [hin j hj]
            show (⟨1, (W1 j).cells⟩ : Tape) = W3 j
            simp only [hW3def, ite_eq_left hj]
            rfl
          · rw [hout j hj]
            show W1 j = W3 j
            simp only [hW3def, ite_eq_right hj]
            rfl
  exact seqTM_hoareTime skipTM _ hpark htrans hrest

/-- Park every head past the marker, then rewind only the named work tapes. The input tape keeps
its head — a stage whose input head is itself part of the state being simulated cannot afford to
have it rewound. -/
def parkRewindWorkTM (targets : List (Fin n)) : TM n :=
  seqTM skipTM (bigSeqTM (targets.map rewindWorkTM))

/-- **The work-only cleanup stage's contract.** The named work tapes end at cell one with their
contents untouched; every other head ends merely parked. -/
theorem parkRewindWorkTM_hoareTime (targets : List (Fin n)) (hnodup : targets.Nodup) (B : ℕ)
    (hB : 1 ≤ B) (I₀ : Tape) (W₀ : Fin n → Tape) (O₀ : Tape)
    (hI : Tape.StartInvariant I₀) (hW : ∀ i, Tape.StartInvariant (W₀ i))
    (hO : Tape.StartInvariant O₀) (hWB : ∀ j, j ∈ targets → (W₀ j).head ≤ B) :
    (parkRewindWorkTM targets).HoareTime
      (fun inp work out => inp = I₀ ∧ work = W₀ ∧ out = O₀)
      (fun inp work out => inp = parkTape I₀ ∧
        work = (fun j => if j ∈ targets then (⟨1, (W₀ j).cells⟩ : Tape) else parkTape (W₀ j)) ∧
        out = parkTape O₀)
      (1 + 1 + (targets.length * (B + 3) + 1)) := by
  classical
  set W1 : Fin n → Tape := fun j => parkTape (W₀ j) with hW1def
  set W3 : Fin n → Tape :=
    fun j => if j ∈ targets then (⟨1, (W₀ j).cells⟩ : Tape) else parkTape (W₀ j) with hW3def
  have hW1P : ∀ j, Parked (W1 j) := fun j => parkTape_parked (hW j)
  have hI1P : Parked (parkTape I₀) := parkTape_parked hI
  have hO1P : Parked (parkTape O₀) := parkTape_parked hO
  have hpark : (skipTM (n := n)).HoareTime
      (fun inp work out => inp = I₀ ∧ work = W₀ ∧ out = O₀)
      (fun inp work out => inp = parkTape I₀ ∧ work = W1 ∧ out = parkTape O₀) 1 := by
    refine (parkAll_hoareTime I₀ W₀ O₀ hI hW hO).strengthen_post ?_
    rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, funext hw, ho⟩
  have htrans : ∀ inp work out, (inp = parkTape I₀ ∧ work = W1 ∧ out = parkTape O₀) →
      (transitionInput inp = parkTape I₀ ∧ (fun i => transitionTape (work i)) = W1 ∧
        transitionTape out = parkTape O₀) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨transitionInput_eq_self hI1P.read_ne_start,
      funext fun i => transitionTape_eq_self (hW1P i).read_ne_start,
      transitionTape_eq_self hO1P.read_ne_start⟩
  have hrest : (bigSeqTM (targets.map rewindWorkTM)).HoareTime
      (fun inp work out => inp = parkTape I₀ ∧ work = W1 ∧ out = parkTape O₀)
      (fun inp work out => inp = parkTape I₀ ∧ work = W3 ∧ out = parkTape O₀)
      (targets.length * (B + 3) + 1) := by
    refine (rewindList_hoareTime targets hnodup B (parkTape I₀) W1 (parkTape O₀)
      hI1P hO1P hW1P ?_).strengthen_post ?_
    · intro j hj
      refine ⟨(hW j).1, ?_⟩
      show max (W₀ j).head 1 ≤ B
      have := hWB j hj
      omega
    · rintro inp work out ⟨rfl, rfl, hin, hout⟩
      refine ⟨rfl, funext fun j => ?_, rfl⟩
      by_cases hj : j ∈ targets
      · rw [hin j hj]
        show (⟨1, (W1 j).cells⟩ : Tape) = W3 j
        simp only [hW3def, ite_eq_left hj]
        rfl
      · rw [hout j hj, hW3def, hW1def]
        simp only [ite_eq_right hj]
  exact seqTM_hoareTime skipTM _ hpark htrans hrest

end TM

end Complexity

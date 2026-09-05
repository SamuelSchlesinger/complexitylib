/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHLayout
public import Complexitylib.Classes.Containments.Internal.TallyLoopIndexed
public import Complexitylib.Classes.Containments.Internal.WitnessEnum

/-!
# What the enumerator's tapes rest in between iterations

⚠️ Unreviewed by Bolton

The counting loop's state names three registers; every other tape has to be back at a known
resting value when an iteration ends, or the next one cannot be entered. For the witness
enumerator that bank is *not* the same at every index: the witness tape advances with the counter,
which is why the loop rule this machine uses is the indexed one.

Everything else rests where it started — the input copy rewound, the horizon in place, the wipe's
height register loaded, and every scratch tape blank.

## Main results

- `PolyExists.strTape` — a rewound tape holding a bitstring, and that it is parked
- `PolyExists.enumRest` — the resting bank at a given count, and its values at the named indices
- `PolyExists.enumRest_parked`, `PolyExists.enumRest_head` — what the loop rule asks of it
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- A rewound tape holding a bitstring. -/
def strTape (l : List Bool) : Tape := (Tape.init (l.map Γ.ofBool)).move Dir3.right

@[simp] theorem strTape_head (l : List Bool) : (strTape l).head = 1 := rfl

theorem strTape_hasBinaryString (l : List Bool) : (strTape l).HasBinaryString l :=
  Tape.init_move_right_hasBinaryString l

/-- **A tape holding a bitstring is parked**: its head is off the left marker and no cell past
the marker holds one. -/
theorem strTape_parked (l : List Bool) : TM.Parked (strTape l) := by
  have h : (strTape l).HasBinaryString l := strTape_hasBinaryString l
  refine ⟨by rw [show (strTape l).head = 1 from h.1], fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hb : i < l.length
  · rw [h.2.1 i hb]
    cases l[i] <;> simp [Γ.ofBool]
  · rw [h.2.2 i (by omega)]
    simp

theorem strTape_startInvariant (l : List Bool) : Tape.StartInvariant (strTape l) :=
  (TM.startInvariant_initOfBool l).move Dir3.right

theorem regTape_parked (v : ℕ) : TM.Parked (TM.regTape v) := by
  refine ⟨le_of_eq rfl, fun j hj => ?_⟩
  show (if j = 0 then Γ.start else if j ≤ v then Γ.one else Γ.blank) ≠ Γ.start
  rw [ite_eq_right (by omega)]
  split <;> decide

theorem regTape_startInvariant (v : ℕ) : Tape.StartInvariant (TM.regTape v) := by
  refine ⟨rfl, fun j hj => ?_⟩
  show (if j = 0 then Γ.start else if j ≤ v then Γ.one else Γ.blank) ≠ Γ.start
  rw [ite_eq_right (by omega)]
  split <;> decide

/-- **The resting bank at a given count.** The input copy and the horizon are where the prologue
put them, the wipe's height register is loaded, the witness is the one the count denotes, and
every scratch tape is blank. -/
def enumRest (k : ℕ) (x : List Bool) (N H : ℕ) (v : ℕ) : Fin (enumTapes k) → Tape := fun i =>
  if i = xIdx k then strTape x
  else if i = wIdx k then strTape (dropTop v)
  else if i = nIdx k then natTape N
  else if i = regIdx k then TM.regTape H
  else TM.blankTape

@[simp] theorem enumRest_x (k : ℕ) (x : List Bool) (N H v : ℕ) :
    enumRest k x N H v (xIdx k) = strTape x := by
  rw [enumRest, ite_eq_left rfl]

@[simp] theorem enumRest_w (k : ℕ) (x : List Bool) (N H v : ℕ) :
    enumRest k x N H v (wIdx k) = strTape (dropTop v) := by
  obtain ⟨hxw, -⟩ := enumIdx_distinct k
  rw [enumRest, ite_eq_right (fun h => hxw h.symm), ite_eq_left rfl]

@[simp] theorem enumRest_n (k : ℕ) (x : List Bool) (N H v : ℕ) :
    enumRest k x N H v (nIdx k) = natTape N := by
  have hxn : nIdx k ≠ xIdx k := fun h => by
    have h' := congrArg Fin.val h
    simp only [nIdx, xIdx] at h'
    omega
  have hwn : nIdx k ≠ wIdx k := fun h => by
    have h' := congrArg Fin.val h
    simp only [nIdx, wIdx] at h'
    omega
  rw [enumRest, ite_eq_right hxn, ite_eq_right hwn, ite_eq_left rfl]

/-- **The bank is parked at every index**, which is what the loop rule asks of the tapes its
state does not name. -/
theorem enumRest_parked (k : ℕ) (x : List Bool) (N H v : ℕ) (i : Fin (enumTapes k)) :
    TM.Parked (enumRest k x N H v i) := by
  rw [enumRest]
  split
  · exact strTape_parked x
  · split
    · exact strTape_parked _
    · split
      · exact natTape_parked N
      · split
        · exact regTape_parked H
        · exact TM.blankTape_parked

/-- **Every resting tape is at cell one**, which is what makes the loop's window one iteration
wide. -/
theorem enumRest_head (k : ℕ) (x : List Bool) (N H v : ℕ) (i : Fin (enumTapes k)) :
    (enumRest k x N H v i).head ≤ 1 := by
  rw [enumRest]
  split
  · exact le_of_eq rfl
  · split
    · exact le_of_eq rfl
    · split
      · exact le_of_eq (Tape.init_move_right_hasBinaryNat N).2.1
      · split
        · exact le_of_eq rfl
        · exact le_of_eq rfl

end PolyExists

end Complexity

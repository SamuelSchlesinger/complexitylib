/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyLookup

/-!
# Glue facts: phase outputs vs the interpreted step

Small bridges used when matching the body's phase outputs against
`TMDesc.toTM.step`:

* a well-formed tape reads `▷` exactly at the origin, so the peek flags
  and the interpreter's sanitization conditions coincide;
* `simRead` of the live shadow read recovers the simulated read exactly;
* parsed entries' targets are in range, so the interpreter's `min`-clamp is
  the identity on them.
-/


public section

namespace Complexity

namespace TM.UTMBody

/-- A well-formed tape reads `▷` exactly at cell 0. -/
theorem read_start_iff {t : Tape} (h : t.StartInvariant) :
    t.read = Γ.start ↔ t.head = 0 := by
  constructor
  · intro hr
    by_contra hne
    exact h.2 t.head (by omega) hr
  · intro hh
    rw [Tape.read, hh]
    exact h.1

/-- The simulated read, reconstructed from the honest flag and the live
    shadow read, is exactly the simulated tape's read. -/
theorem simRead_flag_eq {sim utm : Tape} (h : VShift sim utm)
    (hwf : sim.StartInvariant) :
    simRead (decide (sim.head = 0)) utm.read = sim.read := by
  by_cases hz : sim.head = 0
  · rw [simRead, decide_eq_true hz, ite_eq_left rfl, Tape.read, hz]
    exact hwf.1.symm
  · rw [simRead, decide_eq_false hz, ite_eq_right Bool.false_ne_true]
    exact h.read_eq (by omega)

/-- Every entry produced by `parseEntry` has an in-range target, so the
    interpreter's `min`-clamp is the identity on it. -/
theorem parseEntry_q'_lt {w : ℕ} {seg : List Γw} {e : DescEntry}
    (hp : parseEntry w seg = some e) : e.act.q' < 2 ^ w := by
  unfold parseEntry at hp
  dsimp only at hp
  by_cases hlen : (seg.filterMap symBit?).length < 2 * w + 16
  · rw [ite_eq_left hlen] at hp
    exact absurd hp (by simp)
  · rw [ite_eq_right hlen] at hp
    simp only [Option.some.injEq] at hp
    subst hp
    dsimp only
    exact lt_of_lt_of_le (Nat.fromBits_lt_pow_length _)
      (Nat.pow_le_pow_right (by omega) (by rw [List.length_take]; omega))

/-- Writing back the read symbol (the interpreter's default action) and
    moving is just the move, on a well-formed tape. -/
theorem writeAndMove_readback_eq_move {t : Tape} (hwf : t.StartInvariant) (d : Dir3) :
    t.writeAndMove (TMDesc.readback t.read).toΓ d = t.move d := by
  show (t.write _).move d = t.move d
  congr 1
  unfold Tape.write
  split
  · rfl
  · next hne =>
    have hr : t.read ≠ Γ.start := hwf.2 t.head (by omega)
    have hread : (TMDesc.readback t.read).toΓ = t.read := by
      cases h : t.read <;> simp_all [TMDesc.readback, Γw.toΓ]
    rw [hread]
    show ({ t with cells := Function.update t.cells t.head (t.cells t.head) } : Tape) = t
    rw [Function.update_eq_self]

/-- The value slice copied to scratch, restricted to its first `w` cells,
    is the segment's new-state field. -/
theorem valueSlice_take (seg : List Γw) (w : ℕ) :
    ((seg.drop (w + 6)).take (w + 10)).take w = (seg.drop (w + 6)).take w := by
  rw [List.take_take]
  congr 1
  omega

/-- Scratch cells holding the value slice decode, at the action offsets, to
    the segment's action bits. -/
theorem scratch_cellBit_eq_segBit {t : Tape} {seg : List Γw} {w k : ℕ}
    (hk : k < 10) (hlen : 2 * w + 16 ≤ seg.length)
    (h : t.HoldsExact ((seg.drop (w + 6)).take (w + 10))) :
    cellBit (t.cells (1 + w + k)) = segBit seg (2 * w + 6 + k) := by
  have hidx : w + k < ((seg.drop (w + 6)).take (w + 10)).length := by
    rw [List.length_take, List.length_drop]
    omega
  have hcell : t.cells (1 + w + k)
      = (((seg.drop (w + 6)).take (w + 10))[w + k]).toΓ := by
    rw [show 1 + w + k = (w + k) + 1 by omega]
    exact Tape.HoldsExact.cells_lt h hidx
  have hseg_idx : 2 * w + 6 + k < seg.length := by omega
  rw [hcell, segBit_eq hseg_idx]
  have hg : (List.take (w + 10) (List.drop (w + 6) seg))[w + k]'hidx
      = seg[2 * w + 6 + k]'hseg_idx := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    omega
  rw [hg]

end TM.UTMBody

end Complexity

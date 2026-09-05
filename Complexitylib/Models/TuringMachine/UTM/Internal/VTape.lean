/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Virtual tapes: the +1 shift representation

The `δ_right_of_start` discipline forces every head reading `▷` to move
right on every step, so a simulated head resting at cell 0 cannot be
shadowed at the same position across many UTM steps. Instead the universal
machine stores each simulated tape shifted one cell right on one of its own
work tapes:

* simulated cell `j` lives at UTM cell `j + 1`;
* UTM cell 1 is permanently `□` (it shadows the simulated `▷`, which cannot
  be written);
* simulated head `p` is shadowed at UTM head `p + 1 ≥ 1` — never on `▷`,
  hence stable across steps and phase transitions.

Under this shift the one-sided tape dynamics correspond exactly:

* a simulated right/left/stay move is the same physical move one cell up
  (left moves from simulated position 0 never occur in sanitized dynamics);
* a simulated write at position `p ≥ 1` is the same write at `p + 1`;
* a simulated write at position 0 is a structural no-op, shadowed by
  writing `□` over the permanent `□` at UTM cell 1;
* "simulated head on `▷`" ⟺ "UTM head at cell 1", detectable by a left-peek.

## Main definitions

- `VShift sim utm` — the shift correspondence
- `Tape.StartInvariant` — cell 0 is `▷` and nowhere else (preserved by all writes)

## Main results

- `VShift.read_eq` / `VShift.read_blank` — reads under the shift
- `VShift.writeAndMove` — one full simulated tape action corresponds
- `VShift.init` — the initial correspondence
-/


@[expose] public section

namespace Complexity

-- ════════════════════════════════════════════════════════════════════════
-- Exact tape contents
-- ════════════════════════════════════════════════════════════════════════

/-- The tape holds exactly `syms` after `▷`: cell `i+1` is `syms[i]` for
    `i < |syms|` and `□` beyond. Used for the UTM's state, description, and
    scratch tapes, whose contents are fully determined. -/
def Tape.HoldsExact (t : Tape) (syms : List Γw) : Prop :=
  t.cells 0 = Γ.start ∧
  ∀ i : ℕ, t.cells (i + 1) = if h : i < syms.length then (syms[i]).toΓ else Γ.blank

namespace Tape.HoldsExact

theorem startInvariant {t : Tape} {syms : List Γw} (h : t.HoldsExact syms) : t.StartInvariant := by
  refine ⟨h.1, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [h.2 i]
  split
  · next => cases syms[i] <;> simp [Γw.toΓ]
  · simp

/-- Cells within the contents. -/
theorem cells_lt {t : Tape} {syms : List Γw} (h : t.HoldsExact syms)
    {i : ℕ} (hi : i < syms.length) : t.cells (i + 1) = (syms[i]).toΓ := by
  rw [h.2 i, dite_eq_left hi]

/-- Cells beyond the contents are blank. -/
theorem cells_ge {t : Tape} {syms : List Γw} (h : t.HoldsExact syms)
    {i : ℕ} (hi : syms.length ≤ i) : t.cells (i + 1) = Γ.blank := by
  rw [h.2 i, dite_eq_right (by omega)]

/-- The all-blank (cleared) tape characterization. -/
theorem nil_iff {t : Tape} :
    t.HoldsExact [] ↔ t.cells 0 = Γ.start ∧ ∀ i : ℕ, t.cells (i + 1) = Γ.blank := by
  constructor
  · exact fun h => ⟨h.1, fun i => cells_ge h (Nat.zero_le i)⟩
  · exact fun ⟨h0, h1⟩ => ⟨h0, fun i => by rw [h1 i]; simp⟩

/-- A freshly initialized (empty) tape holds `[]`. -/
theorem init_nil : (Tape.init []).HoldsExact [] := by
  refine ⟨by simp [Tape.init], fun i => ?_⟩
  simp [Tape.init]

end Tape.HoldsExact

namespace TM

/-- The **shift correspondence**: `utm` stores `sim` shifted one cell
    right, with `□` shadowing the simulated `▷` at UTM cell 1, and the head
    one cell up. -/
def VShift (sim utm : Tape) : Prop :=
  utm.cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
    else sim.cells (k - 1)) ∧
  utm.head = sim.head + 1

namespace VShift

theorem head_eq {sim utm : Tape} (h : VShift sim utm) : utm.head = sim.head + 1 := h.2

theorem head_pos {sim utm : Tape} (h : VShift sim utm) : 1 ≤ utm.head := by
  rw [h.2]; omega

/-- Away from the simulated origin, the shadow reads the simulated symbol. -/
theorem read_eq {sim utm : Tape} (h : VShift sim utm) (hp : 1 ≤ sim.head) :
    utm.read = sim.read := by
  rw [Tape.read, Tape.read, h.1, h.2]
  simp only [show sim.head + 1 ≠ 0 by omega, ite_false,
    show sim.head + 1 ≠ 1 by omega, ite_false, Nat.add_sub_cancel]

/-- At the simulated origin, the shadow reads the permanent `□`. -/
theorem read_blank {sim utm : Tape} (h : VShift sim utm) (hp : sim.head = 0) :
    utm.read = Γ.blank := by
  rw [Tape.read, h.1, h.2, hp]
  simp

/-- The shadow never reads `▷` (given the simulated tape is well-formed). -/
theorem read_ne_start {sim utm : Tape} (h : VShift sim utm) (hsim : sim.StartInvariant) :
    utm.read ≠ Γ.start := by
  rcases Nat.eq_zero_or_pos sim.head with hp | hp
  · rw [h.read_blank hp]; simp
  · rw [h.read_eq hp]
    exact hsim.2 sim.head hp

/-- The shadow's cells beyond 1 never hold `▷` (given the simulated tape is
    well-formed). -/
theorem startInvariant {sim utm : Tape} (h : VShift sim utm) (hsim : sim.StartInvariant) :
    utm.StartInvariant := by
  constructor
  · rw [h.1]; simp
  · intro j hj
    rw [h.1]
    simp only [show j ≠ 0 by omega, ite_false]
    by_cases hj1 : j = 1
    · simp [hj1]
    · simp only [hj1, ite_false]
      exact hsim.2 (j - 1) (by omega)

/-- Moves correspond, provided a left move never happens at the simulated
    origin (sanitized dynamics guarantee this). -/
theorem move {sim utm : Tape} (h : VShift sim utm) (d : Dir3)
    (hd : sim.head = 0 → d = Dir3.right) :
    VShift (sim.move d) (utm.move d) := by
  refine ⟨?_, ?_⟩
  · cases d <;> simpa [Tape.move] using h.1
  · cases d with
    | right => simp [Tape.move, h.2]
    | stay => exact h.2
    | left =>
      rcases Nat.eq_zero_or_pos sim.head with hp | hp
      · exact absurd (hd hp) (by simp)
      · simp only [Tape.move, h.2]
        omega

/-- Writes away from the simulated origin correspond. -/
theorem write {sim utm : Tape} (h : VShift sim utm) (s : Γw) (hp : 1 ≤ sim.head) :
    VShift (sim.write s.toΓ) (utm.write s.toΓ) := by
  have hh : utm.head = sim.head + 1 := h.2
  refine ⟨?_, by rw [Tape.write_head, Tape.write_head]; exact hh⟩
  unfold Tape.write
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  funext k
  show Function.update utm.cells utm.head s.toΓ k
    = if k = 0 then Γ.start else if k = 1 then Γ.blank
      else Function.update sim.cells sim.head s.toΓ (k - 1)
  by_cases hk : k = utm.head
  · subst hk
    rw [Function.update_self, hh]
    simp only [show sim.head + 1 ≠ 0 by omega, ite_false,
      show sim.head + 1 ≠ 1 by omega, ite_false]
    rw [Nat.add_sub_cancel, Function.update_self]
  · rw [Function.update_of_ne hk, h.1]
    by_cases hk0 : k = 0
    · simp [hk0]
    · by_cases hk1 : k = 1
      · simp [hk1]
      · simp only [hk0, hk1, ite_false]
        rw [Function.update_of_ne (by rw [hh] at hk; omega)]

/-- A simulated write at the origin is a no-op; the shadow writes `□` over
    the permanent `□` at cell 1 — also a no-op on cells. -/
theorem write_origin {sim utm : Tape} (h : VShift sim utm) (hp : sim.head = 0) :
    VShift sim (utm.write Γ.blank) := by
  have hh : utm.head = sim.head + 1 := h.2
  refine ⟨?_, by rw [Tape.write_head]; exact hh⟩
  unfold Tape.write
  rw [ite_eq_right (by omega)]
  funext k
  show Function.update utm.cells utm.head Γ.blank k
    = if k = 0 then Γ.start else if k = 1 then Γ.blank else sim.cells (k - 1)
  by_cases hk : k = utm.head
  · subst hk
    rw [Function.update_self, hh, hp]
    simp
  · rw [Function.update_of_ne hk, h.1]

/-- **One full simulated tape action corresponds**: writing `s` and moving
    `d` on the simulated tape is shadowed by writing
    `if at-origin then □ else s` and moving `d`, provided the sanitized
    direction discipline (`▷ ⇒ right`) holds. -/
theorem writeAndMove {sim utm : Tape} (h : VShift sim utm) (s : Γw) (d : Dir3)
    (hd : sim.head = 0 → d = Dir3.right) :
    VShift (sim.writeAndMove s.toΓ d)
      (utm.writeAndMove (if sim.head = 0 then Γ.blank else s.toΓ) d) := by
  rcases Nat.eq_zero_or_pos sim.head with hp | hp
  · rw [ite_eq_left hp]
    have hw : sim.write s.toΓ = sim := by unfold Tape.write; rw [ite_eq_left hp]
    show VShift ((sim.write s.toΓ).move d) ((utm.write Γ.blank).move d)
    rw [hw]
    exact (h.write_origin hp).move d hd
  · rw [ite_eq_right (by omega)]
    exact (h.write s hp).move d
      (fun h0 => absurd (by rwa [Tape.write_head] at h0) (by omega))

/-- The initial correspondence: the simulated initial tape (contents `l`)
    is shadowed by `▷ □ l ⋯` with head at cell 1. -/
theorem init (l : List Γ) :
    VShift (Tape.init l)
      ⟨1, fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
        else ((l[k - 2]?).getD Γ.blank)⟩ := by
  refine ⟨?_, rfl⟩
  funext k
  by_cases hk0 : k = 0
  · simp [hk0]
  · by_cases hk1 : k = 1
    · simp [hk1]
    · simp only [hk0, hk1, ite_false, Tape.init,
        show k - 1 ≠ 0 by omega, show k - 1 - 1 = k - 2 by omega]

end VShift

end TM

end Complexity

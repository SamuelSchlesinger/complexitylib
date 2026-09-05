/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Tape.Encoding
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

/-!
# Tape cursors for the streaming circuit evaluator

The evaluator repeatedly rewinds, indexes, and extends canonical binary tapes.
`BinaryCursor` keeps the complete canonical cell contents fixed while exposing
the current zero-based read position. This is intentionally internal: the
neutral endpoint and suffix predicates remain the public tape API.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- A zero-based cursor into a tape with exact canonical binary contents. The
position may also equal the string length, in which case the cursor reads the
first trailing blank. -/
def BinaryCursor (t : Tape) (bits : List Bool) (position : ℕ) : Prop :=
  position ≤ bits.length ∧
  t.head = position + 1 ∧
  t.cells = (Tape.init (bits.map Γ.ofBool)).cells

/-- The boundary state reached after rewinding a canonical binary tape onto
its left-end marker. -/
def BinaryAtMarker (t : Tape) (bits : List Bool) : Prop :=
  t.head = 0 ∧ t.cells = (Tape.init (bits.map Γ.ofBool)).cells

namespace BinaryCursor

/-- An appendable binary prefix is a cursor at its first trailing blank once
its left marker is known. -/
theorem ofHasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) (h₀ : t.cells 0 = Γ.start) :
    BinaryCursor t bits bits.length :=
  ⟨le_rfl, h.1, h.cells_eq_init h₀⟩

/-- Exact canonical cells and a head at cell one form the position-zero
cursor. -/
theorem atFirstBit {t : Tape} {bits : List Bool}
    (hhead : t.head = 1)
    (hcells : t.cells = (Tape.init (bits.map Γ.ofBool)).cells) :
    BinaryCursor t bits 0 :=
  ⟨Nat.zero_le _, by omega, hcells⟩

/-- A binary cursor carries the standard unique-left-marker invariant. -/
theorem startInvariant {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) : t.StartInvariant := by
  unfold Tape.StartInvariant
  rw [h.2.2]
  simpa [Tape.StartInvariant] using Tape.StartInvariant.init_ofBool bits

/-- A binary cursor is always parked away from the left-end marker. -/
theorem read_ne_start {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) : t.read ≠ Γ.start :=
  h.startInvariant.read_ne_start (by rw [h.2.1]; omega)

/-- The controller's preserve action leaves a cursor tape unchanged. -/
theorem preserve {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) :
    t.writeAndMove (TM.readBackWrite t.read) (TM.idleDir t.read) = t := by
  rw [TM.writeAndMove_readBack t h.read_ne_start]
  simp [TM.idleDir, h.read_ne_start, Tape.move]

/-- The controller's right action changes only the cursor head. -/
theorem applyMoveRight {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) :
    t.writeAndMove (TM.readBackWrite t.read) Dir3.right =
      t.move Dir3.right :=
  TM.writeAndMove_readBack t h.read_ne_start Dir3.right

/-- The controller's guarded-left action is an ordinary left move for a
binary cursor. -/
theorem applyMoveLeft {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) :
    t.writeAndMove (TM.readBackWrite t.read) (TM.moveLeftDir t.read) =
      t.move Dir3.left := by
  rw [TM.writeAndMove_readBack t h.read_ne_start]
  simp [TM.moveLeftDir, h.read_ne_start]

/-- The guarded-left action from position zero enters the left-marker state
used by every controller rewind. -/
theorem toMarker {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits 0) :
    BinaryAtMarker
      (t.writeAndMove (TM.readBackWrite t.read) (TM.moveLeftDir t.read)) bits := by
  rw [h.applyMoveLeft]
  refine ⟨?_, ?_⟩
  · simp [Tape.move, h.2.1]
  · simpa [Tape.move_cells] using h.2.2

/-- Reading a cursor strictly inside the string returns that indexed bit. -/
theorem read_of_lt {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) (hlt : position < bits.length) :
    t.read = Γ.ofBool (bits[position]'hlt) := by
  rw [Tape.read, h.2.1, h.2.2]
  exact Tape.init_ofBool_cells_lt bits position hlt

/-- A cursor at the frontier reads the first trailing blank. -/
theorem read_frontier {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits bits.length) :
    t.read = Γ.blank := by
  rw [Tape.read, h.2.1, h.2.2]
  exact Tape.init_ofBool_cells_ge bits bits.length le_rfl

/-- A position-zero cursor exposes the neutral completed-string contract. -/
theorem hasBinaryString {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits 0) : t.HasBinaryString bits := by
  refine ⟨by simpa using h.2.1, ?_, ?_⟩
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_ge bits i hi

/-- A position-zero cursor exposes the whole string as its remaining suffix. -/
theorem hasBinarySuffix {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits 0) : t.HasBinarySuffix bits :=
  h.hasBinaryString.hasBinarySuffix

/-- Moving right advances an in-bounds cursor and preserves its contents. -/
theorem moveRight {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) (hlt : position < bits.length) :
    BinaryCursor (t.move Dir3.right) bits (position + 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · simp [Tape.move, h.2.1]
  · simpa [Tape.move_cells] using h.2.2

/-- Moving left retreats a positive cursor and preserves its contents. -/
theorem moveLeft {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) (hpos : 0 < position) :
    BinaryCursor (t.move Dir3.left) bits (position - 1) := by
  refine ⟨(Nat.sub_le position 1).trans h.1, ?_, ?_⟩
  · simp [Tape.move, h.2.1]
    omega
  · simpa [Tape.move_cells] using h.2.2

/-- A frontier cursor exposes the existing appendable-prefix contract. -/
theorem hasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits bits.length) :
    t.HasBinaryPrefix bits := by
  refine ⟨h.2.1, ?_, ?_⟩
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_ge bits i hi

/-- Writing at the frontier and moving right appends one bit and leaves a new
frontier cursor. -/
theorem append {t : Tape} {bits : List Bool} (bit : Bool)
    (h : BinaryCursor t bits bits.length) :
    BinaryCursor (t.writeAndMove (Γ.ofBool bit) Dir3.right)
      (bits ++ [bit]) (bits ++ [bit]).length := by
  have hprefix := h.hasBinaryPrefix
  have hprefix' := Tape.hasBinaryPrefix_write_bit bit hprefix
  have hzero' := Tape.hasBinaryPrefix_write_bit_cell0 bit hprefix h.startInvariant.1
  exact ofHasBinaryPrefix hprefix' hzero'

/-- Writable-alphabet form of `append`, matching the controller transition
exactly. -/
theorem appendWritable {t : Tape} {bits : List Bool} (bit : Bool)
    (h : BinaryCursor t bits bits.length) :
    BinaryCursor (t.writeAndMove (Γw.ofBool bit).toΓ Dir3.right)
      (bits ++ [bit]) (bits ++ [bit]).length := by
  rw [Γw.ofBool_toΓ]
  exact h.append bit

end BinaryCursor

namespace BinaryAtMarker

/-- A canonical marker state reads the unique left-end marker. -/
theorem read_start {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) : t.read = Γ.start := by
  rw [Tape.read, h.1, h.2]
  simp

/-- A canonical marker state carries the standard tape invariant. -/
theorem startInvariant {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) : t.StartInvariant := by
  unfold Tape.StartInvariant
  rw [h.2]
  simpa [Tape.StartInvariant] using Tape.StartInvariant.init_ofBool bits

/-- Writing back at the immutable marker and moving right is exactly an
ordinary right move. -/
theorem applyMoveRight {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) :
    t.writeAndMove (TM.readBackWrite t.read) Dir3.right =
      t.move Dir3.right := by
  show (t.write (TM.readBackWrite t.read)).move Dir3.right = _
  rw [Tape.write, ite_eq_left h.1]

/-- The controller's marker bounce returns to the position-zero cursor. -/
theorem returnToFirstBit {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) :
    BinaryCursor
      (t.writeAndMove (TM.readBackWrite t.read) Dir3.right) bits 0 := by
  rw [h.applyMoveRight]
  apply BinaryCursor.atFirstBit
  · simp [Tape.move, h.1]
  · simpa [Tape.move_cells] using h.2

end BinaryAtMarker

end Internal

end Machine

end CircuitCode

end Complexity

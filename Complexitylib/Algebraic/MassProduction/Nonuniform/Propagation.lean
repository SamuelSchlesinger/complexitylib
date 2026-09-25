/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression

/-!
# Linear-size segmented propagation

Given source bits and links between consecutive records, this circuit
computes `value[i] = source[i] OR (link[i] AND value[i-1])`, with a false
initial value. Earlier values are shared circuit wires. Exactly two charged
gates are used per record, independent of the lengths of equal-key runs.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Propagation

/-- The propagated value after processing a prefix of the records. -/
def value (source link : Nat → Bool) : Nat → Bool
  | 0 => false
  | count + 1 => source count || (link count && value source link count)

/-- Source bits occupy the first input block. -/
def sourceInput (input : Fin (count + count) → Bool) (index : Nat) : Bool :=
  if bound : index < count then input (Fin.castAdd count ⟨index, bound⟩) else false

/-- Link bits occupy the second input block. -/
def linkInput (input : Fin (count + count) → Bool) (index : Nat) : Bool :=
  if bound : index < count then input (Fin.natAdd count ⟨index, bound⟩) else false

/-- Two shared gates per processed record, preceded by one free false
constant. The program always reads the original fixed-size input array. -/
def program (count : Nat) : (processed : Nat) → processed ≤ count →
    Program DeMorgan.signature (count + count) (1 + 2 * processed)
  | 0, _ => .gate .empty { op := .false, wires := Fin.elim0 }
  | processed + 1, fits =>
      let previous := program count processed (by omega)
      let linked := previous.gate {
        op := .and
        wires := fun argument => if argument.val = 0 then
          Wire.input (Fin.natAdd count ⟨processed, by omega⟩)
          else Wire.gate ⟨2 * processed, by omega⟩ }
      linked.gate {
        op := .or
        wires := fun argument => if argument.val = 0 then
          Wire.input (Fin.castAdd count ⟨processed, by omega⟩)
          else Wire.gate (Fin.last (1 + 2 * processed)) }

set_option backward.isDefEq.respectTransparency false in
/-- The program's even-numbered gate after each prefix is its propagated
value; in particular the zero-prefix gate is false. -/
theorem program_eval
    (input : Fin (count + count) → Bool)
    (processed : Nat) (fits : processed ≤ count)
    (prefixCount : Nat) (prefixLe : prefixCount ≤ processed) :
    (program count processed fits).eval DeMorgan.interpretation input
        ⟨2 * prefixCount, by omega⟩ = value (sourceInput input) (linkInput input) prefixCount := by
  induction processed generalizing prefixCount with
  | zero =>
      have : prefixCount = 0 := by omega
      subst prefixCount
      rfl
  | succ processed ih =>
      by_cases last : prefixCount = processed + 1
      · subst prefixCount
        have lastIndex : (⟨2 * (processed + 1), by omega⟩ : Fin (1 + 2 * (processed + 1))) =
            Fin.last (1 + 2 * processed + 1) := by
          apply Fin.ext
          change 2 * (processed + 1) = 1 + 2 * processed + 1
          omega
        rw [lastIndex, program, Program.eval_gate_last]
        simp only [Line.eval, DeMorgan.interpretation]
        simp only [Function.comp_apply, Nat.one_ne_zero, ↓reduceIte,
          Wire.input, Wire.gate, Fin.addCases_left, Fin.addCases_right,
          Program.eval_gate_last, Line.eval, DeMorgan.interpretation]
        rw [ih (by omega) processed (by omega)]
        simp only [value, sourceInput, linkInput, dite_eq_left (by omega : processed < count)]
      · have prefixEarlier : prefixCount ≤ processed := by omega
        have oldIndex : (⟨2 * prefixCount, by omega⟩ : Fin (1 + 2 * (processed + 1))) =
            (⟨2 * prefixCount, by omega⟩ : Fin (1 + 2 * processed)).castSucc.castSucc := rfl
        rw [oldIndex, program, Program.eval_gate_castSucc, Program.eval_gate_castSucc]
        exact ih (by omega) prefixCount prefixEarlier

/-- Every processed record contributes one AND and one OR gate. -/
theorem program_cost (count processed : Nat) (fits : processed ≤ count) :
    (program count processed fits).cost DeMorgan.standardCost = 2 * processed := by
  induction processed with
  | zero => rfl
  | succ processed ih =>
      simp only [program, Program.cost_gate, DeMorgan.standardCost_and,
        DeMorgan.standardCost_or, ih]
      omega

/-- All propagated values, in the same order as the input records. -/
def circuit (count : Nat) : Circuit DeMorgan.signature (count + count) (1 + 2 * count) count where
  program := program count count le_rfl
  outputs := fun index => Wire.gate ⟨2 * (index.val + 1), by omega⟩

/-- The concrete circuit implements the segmented recurrence. -/
theorem circuit_eval (input : Fin (count + count) → Bool) (index : Fin count) :
    (circuit count).eval DeMorgan.interpretation input index =
      value (sourceInput input) (linkInput input) (index.val + 1) := by
  simp only [circuit, Circuit.eval, Function.comp_apply, Program.trace_gateWire]
  exact program_eval input count le_rfl (index.val + 1) index.isLt

/-- The exact charged size is linear in the number of records. -/
theorem circuit_cost (count : Nat) :
    (circuit count).cost DeMorgan.standardCost = 2 * count :=
  program_cost count count le_rfl

/-- A propagated true bit has a source connected to the current position
by an uninterrupted interval of true links. -/
theorem value_eq_true_iff (source link : Nat → Bool) (count : Nat) :
    value source link count = true ↔
      ∃ start, start < count ∧ source start = true ∧
        ∀ index, start < index → index < count → link index = true := by
  induction count with
  | zero => simp [value]
  | succ count ih =>
      simp only [value, Bool.or_eq_true, Bool.and_eq_true, ih]
      constructor
      · rintro (last | ⟨linked, start, startBefore, starts, links⟩)
        · exact ⟨count, by omega, last, by intro index lower upper; omega⟩
        · refine ⟨start, by omega, starts, ?_⟩
          intro index lower upper
          by_cases atLast : index = count
          · simpa only [atLast] using linked
          · exact links index lower (by omega)
      · rintro ⟨start, startBefore, starts, links⟩
        by_cases atLast : start = count
        · exact Or.inl (atLast ▸ starts)
        · exact Or.inr ⟨links count (by omega) (by omega), start, by omega, starts,
            fun index lower upper => links index lower (by omega)⟩

end Algebraic.MassProduction.Nonuniform.Propagation

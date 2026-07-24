/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonProbeQuery.Defs
import Complexitylib.Circuits.BarringtonTokenQuery.Internal
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Internal

/-!
# Direct Barrington queries through a formula-code oracle -- proof internals
-/

namespace Complexity

namespace FormulaCode

namespace BitOracle

theorem segmentRootToken?_ofList_encodeTokenStream_context_internal
    (before after : List Token) (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : (before ++ tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    segmentRootToken?
        (ofList (encodeTokenStream (before ++ tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
      (tokens formula).getLast? := by
  have hpositive : 0 < formula.size := by
    cases formula <;> simp [BoolFormula.size]
  rw [segmentRootToken?]
  rw [show formula.size = (formula.size - 1) + 1 by omega]
  simp only [TokenSegment.root?, Option.bind_eq_bind, Option.bind_some]
  have hglobal : before.length + (formula.size - 1) <
      (before ++ tokens formula ++ after).length := by
    simp
    omega
  rw [tokenValueAt?_ofList_encodeTokenStream_internal _ bitFuel _ hheader
    hglobal hbound]
  rw [← List.getElem?_eq_getElem hglobal]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  rw [show before.length + (formula.size - 1) - before.length =
    formula.size - 1 by omega]
  rw [List.getLast?_eq_getElem?]
  simp

end BitOracle

end FormulaCode

theorem barringtonProbeSlotOccupancy_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula)
    (bitFuel : ℕ)
    (hheader :
      (before ++ FormulaCode.tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ FormulaCode.tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    barringtonProbeSlotsNonempty fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
          barringtonCompileSlotsNonempty fuel formula ∧
      ∀ slot,
        barringtonCompileProbeSlotOccupied fuel
            (FormulaCode.BitOracle.ofList
              (FormulaCode.encodeTokenStream
                (before ++ FormulaCode.tokens formula ++ after)))
            bitFuel ⟨before.length, formula.size⟩ slot =
          barringtonCompileSlotOccupied fuel formula slot := by
  induction fuel generalizing before after formula with
  | zero =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot ⊢ <;>
        simp [barringtonProbeSlotsNonempty,
          barringtonCompileProbeSlotOccupied,
          barringtonCompileSlotsNonempty, barringtonCompileSlotOccupied,
          hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonProbeSlotsNonempty,
            barringtonCompileProbeSlotOccupied,
            barringtonCompileSlotsNonempty, barringtonCompileSlotOccupied,
            hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonProbeSlotsNonempty,
            barringtonCompileProbeSlotOccupied,
            barringtonCompileSlotsNonempty, barringtonCompileSlotOccupied,
            hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonProbeSlotsNonempty,
            barringtonCompileProbeSlotOccupied,
            barringtonCompileSlotsNonempty, barringtonCompileSlotOccupied,
            hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchild := ih before (FormulaCode.Token.neg :: after) formula
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchild' := hchild
          simp [List.append_assoc] at hchild'
          have hchildFunction := funext hchild'.2
          simp [barringtonProbeSlotsNonempty,
            barringtonCompileProbeSlotOccupied,
            barringtonCompileSlotsNonempty, barringtonCompileSlotOccupied,
            FormulaCode.tokens, BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot, hchild'.1,
            hchildFunction]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
            left
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.conj :: after) right
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          have hleftFunction := funext hleft'.2
          have hrightFunction := funext hright'.2
          simp [barringtonProbeSlotsNonempty,
            barringtonCompileProbeSlotOccupied,
            barringtonCompileSlotsNonempty, barringtonCompileSlotOccupied,
            FormulaCode.tokens, BoolFormula.size, List.append_assoc,
            hroot, hchildren', hleft'.1, hleftFunction, hright'.1,
            hrightFunction]
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
            left
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.disj :: after) right
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          have hleftFunction := funext hleft'.2
          have hrightFunction := funext hright'.2
          simp [barringtonProbeSlotsNonempty,
            barringtonCompileProbeSlotOccupied,
            barringtonCompileSlotsNonempty, barringtonCompileSlotOccupied,
            FormulaCode.tokens, BoolFormula.size, List.append_assoc,
            hroot, hchildren', hleft'.1, hleftFunction, hright'.1,
            hrightFunction]

theorem barringtonProbeOccupiedScans_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula)
    (bitFuel : ℕ) (target : Equiv.Perm (Fin 5))
    (hheader :
      (before ++ FormulaCode.tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ FormulaCode.tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    barringtonProbeFirstOccupiedScan? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
          barringtonFirstOccupiedSlot? fuel formula ∧
      barringtonProbeLastOccupiedScan? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
          barringtonLastOccupiedSlot? fuel formula := by
  have hoccupancy := barringtonProbeSlotOccupancy_correct_context_internal
    fuel before after formula bitFuel hheader hbound
  have hprobeFormula := funext hoccupancy.2
  have hformulaSchedule : barringtonCompileSlotOccupied fuel formula =
      fun slot => (BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot).isSome := by
    funext slot
    exact barringtonCompileSlotOccupied_correct_internal fuel formula target
      slot |>.trans (congrArg Option.isSome
        (barringtonCompileSlot?_correct_internal fuel formula target slot))
  have hprobeSchedule := hprobeFormula.trans hformulaSchedule
  constructor
  · rw [barringtonProbeFirstOccupiedScan?, hprobeSchedule,
      ← barringtonCompileSlots_length_internal fuel formula target]
    rw [BPSlots.firstTrueSlot?_instruction_internal]
    exact (barringtonOccupiedSlots_correct_internal fuel formula target).1.symm
  · rw [barringtonProbeLastOccupiedScan?, hprobeSchedule,
      ← barringtonCompileSlots_length_internal fuel formula target]
    rw [BPSlots.lastTrueSlot?_instruction_internal]
    exact (barringtonOccupiedSlots_correct_internal fuel formula target).2.symm

theorem barringtonCompileProbeScannedSlot?_correct_context_internal
    (fuel : ℕ) (before after : List FormulaCode.Token)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5)) (slot : ℕ)
    (hheader :
      (before ++ FormulaCode.tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ FormulaCode.tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeScannedSlot? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ target slot =
      barringtonCompileSlot? fuel formula target slot := by
  induction fuel generalizing before after formula target slot with
  | zero =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot ⊢ <;>
        simp [barringtonCompileProbeScannedSlot?, barringtonCompileSlot?,
          hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeScannedSlot?, barringtonCompileSlot?,
            hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeScannedSlot?, barringtonCompileSlot?,
            hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeScannedSlot?, barringtonCompileSlot?,
            hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hscans :=
            barringtonProbeOccupiedScans_correct_context_internal fuel before
              (FormulaCode.Token.neg :: after) formula bitFuel target⁻¹
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hquery :
              barringtonCompileProbeScannedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.neg formula) ++ after)))
                  bitFuel ⟨before.length, formula.size⟩ target⁻¹ =
                barringtonCompileSlot? fuel formula target⁻¹ := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before (FormulaCode.Token.neg :: after) formula target⁻¹
                querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hquery
          have hscans' := hscans
          simp [List.append_assoc] at hscans'
          simp [barringtonCompileProbeScannedSlot?, barringtonCompileSlot?,
            FormulaCode.tokens, BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot, hquery, hscans'.2]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftQuery :
              barringtonCompileProbeScannedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.conj left right) ++
                        after)))
                  bitFuel ⟨before.length, left.size⟩
                    (barringtonLeft target) =
                barringtonCompileSlot? fuel left
                  (barringtonLeft target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
                left (barringtonLeft target) querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightQuery :
              barringtonCompileProbeScannedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.conj left right) ++
                        after)))
                  bitFuel ⟨before.length + left.size, right.size⟩
                    (barringtonRight target) =
                barringtonCompileSlot? fuel right
                  (barringtonRight target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.conj :: after) right
                (barringtonRight target) querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileProbeScannedSlot?, barringtonCompileSlot?,
            FormulaCode.tokens, BoolFormula.size, List.append_assoc,
            hroot, hchildren', hleftQuery, hrightQuery]
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftScans :=
            barringtonProbeOccupiedScans_correct_context_internal fuel before
              (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
              left bitFuel target
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightScans :=
            barringtonProbeOccupiedScans_correct_context_internal fuel
              (before ++ FormulaCode.tokens left)
              (FormulaCode.Token.disj :: after) right bitFuel target
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleftScans' := hleftScans
          have hrightScans' := hrightScans
          simp [List.append_assoc] at hleftScans' hrightScans'
          have hleftQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileProbeScannedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.disj left right) ++
                        after)))
                  bitFuel ⟨before.length, left.size⟩ childTarget =
                barringtonCompileSlot? fuel left childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
                left childTarget querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileProbeScannedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.disj left right) ++
                        after)))
                  bitFuel ⟨before.length + left.size, right.size⟩
                    childTarget =
                barringtonCompileSlot? fuel right childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.disj :: after) right childTarget querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileProbeScannedSlot?, barringtonCompileSlot?,
            FormulaCode.tokens, BoolFormula.size, List.append_assoc,
            hroot, hchildren', hleftScans'.2,
            hrightScans'.1, hrightScans'.2, hleftQuery, hrightQuery]

theorem barringtonProbeOccupiedSlots_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula)
    (bitFuel : ℕ)
    (hheader :
      (before ++ FormulaCode.tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ FormulaCode.tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    barringtonProbeFirstOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
          barringtonTokensFirstOccupiedSlot? fuel
            (FormulaCode.tokens formula) ∧
      barringtonProbeLastOccupiedSlot? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ =
          barringtonTokensLastOccupiedSlot? fuel
            (FormulaCode.tokens formula) := by
  induction fuel generalizing before after formula with
  | zero =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot <;>
        simp [barringtonProbeFirstOccupiedSlot?,
          barringtonProbeLastOccupiedSlot?,
          barringtonTokensFirstOccupiedSlot?,
          barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
          BoolFormula.size, List.append_assoc, hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchild := ih before (FormulaCode.Token.neg :: after) formula
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchild' :
              barringtonProbeFirstOccupiedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.neg formula) ++ after)))
                  bitFuel ⟨before.length, formula.size⟩ =
                    barringtonTokensFirstOccupiedSlot? fuel
                      (FormulaCode.tokens formula) ∧
                barringtonProbeLastOccupiedSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.neg formula) ++ after)))
                  bitFuel ⟨before.length, formula.size⟩ =
                    barringtonTokensLastOccupiedSlot? fuel
                      (FormulaCode.tokens formula) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchild
          simp [FormulaCode.tokens, List.append_assoc] at hchild'
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot,
            hchild'.1, hchild'.2]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
            left
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.conj :: after) right
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleft'.1, hright'.1]
          exact ⟨rfl, rfl⟩
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
            left
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.disj :: after) right
            (by simpa [FormulaCode.tokens, List.append_assoc] using hheader)
            (by simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          simp [barringtonProbeFirstOccupiedSlot?,
            barringtonProbeLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleft'.1, hright'.1]

theorem barringtonCompileProbeSlot?_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula)
    (bitFuel : ℕ) (target : Equiv.Perm (Fin 5)) (slot : ℕ)
    (hheader :
      (before ++ FormulaCode.tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ FormulaCode.tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeSlot? fuel
        (FormulaCode.BitOracle.ofList
          (FormulaCode.encodeTokenStream
            (before ++ FormulaCode.tokens formula ++ after)))
        bitFuel ⟨before.length, formula.size⟩ target slot =
      barringtonCompileTokensSlot? fuel
        (FormulaCode.tokens formula) target slot := by
  induction fuel generalizing before after formula target slot with
  | zero =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot ⊢ <;>
        simp [barringtonCompileProbeSlot?,
          barringtonCompileTokensSlot?, hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.BitOracle.segmentRootToken?_ofList_encodeTokenStream_context_internal
          before after formula bitFuel hheader hbound
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hoccupied :=
            barringtonProbeOccupiedSlots_correct_context_internal fuel before
              (FormulaCode.Token.neg :: after) formula bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hquery :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.neg formula) ++ after)))
                  bitFuel ⟨before.length, formula.size⟩ target⁻¹ =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens formula) target⁻¹ := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before (FormulaCode.Token.neg :: after) formula target⁻¹
                querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hquery
          have hoccupied' := hoccupied
          simp [List.append_assoc] at hoccupied'
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot, hquery,
            hoccupied'.2]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftQuery :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.conj left right) ++
                        after)))
                  bitFuel ⟨before.length, left.size⟩
                    (barringtonLeft target) =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens left) (barringtonLeft target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
                left (barringtonLeft target) querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightQuery :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.conj left right) ++
                        after)))
                  bitFuel ⟨before.length + left.size, right.size⟩
                    (barringtonRight target) =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens right) (barringtonRight target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.conj :: after) right
                (barringtonRight target) querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleftQuery, hrightQuery]
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hchildren' :
              FormulaCode.BitOracle.encodedBinaryChildren?
                (FormulaCode.BitOracle.ofList
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++
                      after)))
                bitFuel ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftOccupied :=
            barringtonProbeOccupiedSlots_correct_context_internal fuel before
              (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
              left bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightOccupied :=
            barringtonProbeOccupiedSlots_correct_context_internal fuel
              (before ++ FormulaCode.tokens left)
              (FormulaCode.Token.disj :: after) right bitFuel
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hheader)
              (by
                simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hleftOccupied' := hleftOccupied
          have hrightOccupied' := hrightOccupied
          simp [List.append_assoc] at hleftOccupied' hrightOccupied'
          have hleftQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.disj left right) ++
                        after)))
                  bitFuel ⟨before.length, left.size⟩ childTarget =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens left) childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
                left childTarget querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          have hrightQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileProbeSlot? fuel
                  (FormulaCode.BitOracle.ofList
                    (FormulaCode.encodeTokenStream
                      (before ++ FormulaCode.tokens (.disj left right) ++
                        after)))
                  bitFuel ⟨before.length + left.size, right.size⟩ childTarget =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens right) childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.disj :: after) right childTarget querySlot
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hheader)
                (by
                  simpa [FormulaCode.tokens, List.append_assoc] using hbound)
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileProbeSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleftOccupied'.2,
            hrightOccupied'.1, hrightOccupied'.2,
            hleftQuery, hrightQuery]

end Complexity

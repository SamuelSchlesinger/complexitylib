/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCopy

/-!
# Unrestricted depth-three lower bound: tape erase

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeErase.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeErase

open Turing TapeMultiProgram

/-- Control states of the erase routine. -/
inductive State where
  | start
  | scan
  | erase
  | install
  | done
  deriving DecidableEq, Inhabited

instance : Fintype State where
  elems := {.start, .scan, .erase, .install, .done}
  complete := by
    intro state
    cases state <;> simp

/-- Transition function of the erase routine. -/
def code (r : TapeRegister) : TapeMultiProgram State
  | .start, h => move r .right .scan h
  | .scan, h =>
      match (h r).1 with
      | .bit _ => move r .right .scan h
      | .endMark => jump .erase h
      | _ => none
  | .erase, h =>
      if (h r).1 = .home then move r .right .install h
      else writeMove r blankSymbol .left .erase h
  | .install, h => writeMove r (cleanAtom .endMark) .left .done h
  | .done, _ => none

theorem step_start (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol) :
    (code r).step (cfg .start (Function.update T r S)) =
      some (cfg .scan (Function.update T r (S.move .right))) := by
  have h := TapeMultiProgram.step_move (code r) .start .scan (Function.update T r S)
    r .right (by rfl)
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_right] using h

theorem step_scan_bit (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (b : Bool) (hS : S.head = rawInputSymbol b) :
    (code r).step (cfg .scan (Function.update T r S)) =
      some (cfg .scan (Function.update T r (S.move .right))) := by
  have h := TapeMultiProgram.step_move (code r) .scan .scan (Function.update T r S)
    r .right (by simp [code, heads, hS, rawInputSymbol, cleanAtom])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_right] using h

theorem step_scan_end (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (hS : S.head = cleanAtom .endMark) :
    (code r).step (cfg .scan (Function.update T r S)) =
      some (cfg .erase (Function.update T r S)) := by
  exact TapeMultiProgram.step_jump (code r) .scan .erase (Function.update T r S)
    (by simp [code, heads, hS, cleanAtom])

theorem step_erase_symbol (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (hS : S.head.1 ≠ .home) :
    (code r).step (cfg .erase (Function.update T r S)) =
      some (cfg .erase (Function.update T r ((S.write blankSymbol).move .left))) := by
  have h := TapeMultiProgram.step_writeMove (code r) .erase .erase
    (Function.update T r S) r blankSymbol .left (by simp [code, heads, hS])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_left] using h

theorem step_erase_home (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (hS : S.head.1 = .home) :
    (code r).step (cfg .erase (Function.update T r S)) =
      some (cfg .install (Function.update T r (S.move .right))) := by
  have h := TapeMultiProgram.step_move (code r) .erase .install
    (Function.update T r S) r .right (by simp [code, heads, hS])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_right] using h

theorem step_install (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol) :
    (code r).step (cfg .install (Function.update T r S)) =
      some (cfg .done (Function.update T r
        ((S.write (cleanAtom .endMark)).move .left))) := by
  have h := TapeMultiProgram.step_writeMove (code r) .install .done
    (Function.update T r S) r (cleanAtom .endMark) .left (by rfl)
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_left] using h

theorem mk₂_append_blanks (L R : List TapeSymbol) (n : ℕ) :
    Tape.mk₂ L (R ++ List.replicate n blankSymbol) = Tape.mk₂ L R := by
  have h : ListBlank.mk (R ++ List.replicate n blankSymbol) = ListBlank.mk R := by
    apply Quotient.sound'
    exact Or.inr ⟨n, by simp only [default_tapeSymbol]⟩
  exact congrArg (Tape.mk' (ListBlank.mk L)) h

theorem runs_scan (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (L : List TapeSymbol) :
    RunsIn (code r).step
      (cfg .scan (Function.update T r
        (Tape.mk₂ L (encodeInput bits ++ [cleanAtom .endMark]))))
      (cfg .erase (Function.update T r
        (Tape.mk₂ ((encodeInput bits).reverse ++ L) [cleanAtom .endMark])))
      (bits.length + 1) := by
  induction bits generalizing L with
  | nil =>
      have h := RunsIn.single (step_scan_end r T (Tape.mk₂ L [cleanAtom .endMark]) rfl)
      simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
        List.length_nil, Nat.zero_add] using h
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_scan_bit r T
        (Tape.mk₂ L (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .endMark]))) b rfl)
      simp only [TapeWord.move_right_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol b :: L)
      simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_finish (r : TapeRegister) (T : TapeTapes) (n : ℕ) :
    RunsIn (code r).step
      (cfg .erase (Function.update T r
        (Tape.mk₂ [] (cleanAtom .home :: blankSymbol :: List.replicate n blankSymbol))))
      (cfg .done (Function.update T r (wordTape []))) 2 := by
  have hfirst := RunsIn.single (step_erase_home r T
    (Tape.mk₂ [] (cleanAtom .home :: blankSymbol :: List.replicate n blankSymbol)) rfl)
  simp only [TapeWord.move_right_mk₂_cons] at hfirst
  have hlast := RunsIn.single (step_install r T
    (Tape.mk₂ [cleanAtom .home] (blankSymbol :: List.replicate n blankSymbol)))
  simp only [TapeCopy.write_mk₂, List.tail_cons, TapeWord.move_left_mk₂_cons] at hlast
  have ht : Tape.mk₂ [] (cleanAtom .home :: cleanAtom .endMark ::
      List.replicate n blankSymbol) = wordTape [] := by
    exact mk₂_append_blanks [] [cleanAtom .home, cleanAtom .endMark] n
  rw [ht] at hlast
  exact hfirst.trans hlast

theorem runs_erase_back (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (a : TapeSymbol) (n : ℕ) (ha : a.1 ≠ .home) :
    RunsIn (code r).step
      (cfg .erase (Function.update T r
        (Tape.mk₂ (encodeInput bits ++ [cleanAtom .home])
          (a :: List.replicate n blankSymbol))))
      (cfg .done (Function.update T r (wordTape []))) (bits.length + 3) := by
  induction bits generalizing a n with
  | nil =>
      have hfirst := RunsIn.single (step_erase_symbol r T
        (Tape.mk₂ [cleanAtom .home] (a :: List.replicate n blankSymbol)) ha)
      simp only [TapeCopy.write_mk₂, List.tail_cons, TapeWord.move_left_mk₂_cons] at hfirst
      simpa only [encodeInput, List.map_nil, List.nil_append, List.length_nil,
        Nat.zero_add] using hfirst.trans (runs_finish r T n)
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_erase_symbol r T
        (Tape.mk₂ (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .home]))
          (a :: List.replicate n blankSymbol)) ha)
      simp only [TapeCopy.write_mk₂, List.tail_cons, TapeWord.move_left_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol b) (n + 1) (by simp [rawInputSymbol, cleanAtom])
      simp only [List.replicate_succ] at hrest
      simpa only [encodeInput, List.map_cons, List.cons_append, List.length_cons,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_erase (r : TapeRegister) (T : TapeTapes) (bits : List Bool) :
    RunsIn (code r).step
      (cfg .start (Function.update T r (wordTape bits)))
      (cfg .done (Function.update T r (wordTape []))) (2 * bits.length + 5) := by
  have hstart := RunsIn.single (step_start r T (wordTape bits))
  have hscan := runs_scan r T bits [cleanAtom .home]
  have hback := runs_erase_back r T bits.reverse (cleanAtom .endMark) 0
    (by simp [cleanAtom])
  have hreverse : encodeInput bits.reverse = (encodeInput bits).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.length_reverse, List.replicate_zero] at hback
  have hstart' : RunsIn (code r).step
      (cfg .start (Function.update T r (wordTape bits)))
      (cfg .scan (Function.update T r
        (Tape.mk₂ [cleanAtom .home] (encodeInput bits ++ [cleanAtom .endMark])))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_nil,
      List.reverse_nil, List.nil_append] using hstart
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hstart'.trans hscan).trans hback

@[simp] theorem step_done (r : TapeRegister) (T : TapeTapes) :
    (code r).step (cfg .done T) = none := rfl

end TapeErase
end DepthThreeLowerBound

end Complexity

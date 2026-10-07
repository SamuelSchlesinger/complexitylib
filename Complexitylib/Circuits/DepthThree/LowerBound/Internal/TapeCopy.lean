/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeMultiRoutines
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeWordRewind

/-!
# Unrestricted depth-three lower bound: tape copy

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeCopy.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6

namespace DepthThreeLowerBound
namespace TapeCopy

open Turing TapeMultiProgram

/-- Control states of the copy routine. -/
inductive State where
  | start
  | scan
  | rewind
  | done
  deriving DecidableEq, Inhabited

instance : Fintype State where
  elems := {.start, .scan, .rewind, .done}
  complete := by
    intro state
    cases state <;> simp

/-- Replace the values at two selected registers, giving priority to the first. -/
def onPair {α : Type uDepth1} (src dst : TapeRegister) (base : TapeRegister → α)
    (s d : α) : TapeRegister → α :=
  fun r => if r = src then s else if r = dst then d else base r

@[simp] theorem onPair_src {α : Type uDepth2} (src dst : TapeRegister)
    (base : TapeRegister → α) (s d : α) : onPair src dst base s d src = s := by
  simp [onPair]

@[simp] theorem onPair_dst {α : Type uDepth3} {src dst : TapeRegister} (hne : src ≠ dst)
    (base : TapeRegister → α) (s d : α) : onPair src dst base s d dst = d := by
  simp [onPair, Ne.symm hne]

theorem onPair_other {α : Type uDepth4} (src dst : TapeRegister)
    (base : TapeRegister → α) (s d : α) (r : TapeRegister)
    (hs : r ≠ src) (hd : r ≠ dst) : onPair src dst base s d r = base r := by
  simp [onPair, hs, hd]

/-- Write the two selected tape heads and move them together. -/
def emit {Q : Type uDepth5} (src dst : TapeRegister) (q : Q) (h : TapeHeads)
    (s d : TapeSymbol) (m : HeadMove) : Option (Q × TapeHeads × TapeMoves) :=
  some (q, onPair src dst h s d, onPair src dst stayMoves m m)

/-- Transition function of the copy routine. -/
def code (src dst : TapeRegister) : TapeMultiProgram State
  | .start, h => emit src dst .scan h (h src) (h dst) .right
  | .scan, h =>
      match (h src).1 with
      | .bit b => emit src dst .scan h (h src) (rawInputSymbol b) .right
      | .endMark => emit src dst .rewind h (h src) (cleanAtom .endMark) .stay
      | _ => none
  | .rewind, h =>
      if (h src).1 = .home then emit src dst .done h (h src) (h dst) .stay
      else emit src dst .rewind h (h src) (h dst) .left
  | .done, _ => none

theorem step_emit {Q : Type uDepth6} (P : TapeMultiProgram Q)
    {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (q q' : Q)
    (s d : TapeSymbol) (m : HeadMove)
    (h : P q (heads (onPair src dst T S D)) =
      emit src dst q' (heads (onPair src dst T S D)) s d m) :
    P.step (cfg q (onPair src dst T S D)) =
      some (cfg q' (onPair src dst T (m.apply (S.write s)) (m.apply (D.write d)))) := by
  have he := multiTapeStep_eq_some (c := cfg q (onPair src dst T S D))
    (code := P) h
  change P.step (cfg q (onPair src dst T S D)) =
    some (multiTapeUpdate (cfg q (onPair src dst T S D)) q'
      (onPair src dst (heads (onPair src dst T S D)) s d)
      (onPair src dst stayMoves m m)) at he
  rw [he]
  congr 1
  apply congrArg (cfg q')
  funext r
  by_cases hs : r = src
  · subst r
    simp [cfg, onPair]
  · by_cases hd : r = dst
    · subst r
      simp [cfg, onPair, Ne.symm hne]
    · simp [cfg, onPair, heads, stayMoves, hs, hd]

theorem step_start {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) :
    (code src dst).step (cfg .start (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right) (D.move .right))) := by
  have h := step_emit (code src dst) hne T S D .start .scan S.head D.head .right
    (by simp [code, heads, hne])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_bit {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (b : Bool)
    (hS : S.head = rawInputSymbol b) :
    (code src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right)
        ((D.write (rawInputSymbol b)).move .right))) := by
  have h := step_emit (code src dst) hne T S D .scan .scan S.head (rawInputSymbol b) .right
    (by simp [code, heads, hS, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_end {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head = cleanAtom .endMark) :
    (code src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T S (D.write (cleanAtom .endMark)))) := by
  have h := step_emit (code src dst) hne T S D .scan .rewind S.head (cleanAtom .endMark) .stay
    (by simp [code, heads, hS, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem step_rewind_move {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 ≠ .home) :
    (code src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T (S.move .left) (D.move .left))) := by
  have h := step_emit (code src dst) hne T S D .rewind .rewind S.head D.head .left
    (by simp [code, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_left] using h

theorem step_rewind_home {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 = .home) :
    (code src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .done (onPair src dst T S D)) := by
  have h := step_emit (code src dst) hne T S D .rewind .done S.head D.head .stay
    (by simp [code, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem write_mk₂ (L R : List TapeSymbol) (a : TapeSymbol) :
    (Tape.mk₂ L R).write a = Tape.mk₂ L (a :: R.tail) := by
  cases R <;> rfl

theorem runs_scan {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (bits : List Bool) (L R : List TapeSymbol) (hR : R.tail = []) :
    RunsIn (code src dst).step
      (cfg .scan (onPair src dst T
        (Tape.mk₂ L (encodeInput bits ++ [cleanAtom .endMark])) (Tape.mk₂ L R)))
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ ((encodeInput bits).reverse ++ L) [cleanAtom .endMark])
        (Tape.mk₂ ((encodeInput bits).reverse ++ L) [cleanAtom .endMark])))
      (bits.length + 1) := by
  induction bits generalizing L R with
  | nil =>
      have h := RunsIn.single (step_scan_end hne T
        (Tape.mk₂ L [cleanAtom .endMark]) (Tape.mk₂ L R) rfl)
      simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
        List.length_nil, Nat.zero_add, write_mk₂, hR] using h
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_scan_bit hne T
        (Tape.mk₂ L (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .endMark])))
        (Tape.mk₂ L R) b rfl)
      have hrest := ih (rawInputSymbol b :: L) [] rfl
      simp only [write_mk₂, TapeWord.move_right_mk₂_cons, hR] at hfirst
      have hboth := hfirst.trans hrest
      simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hboth

theorem runs_rewind {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (bits : List Bool) (a : TapeSymbol) (R : List TapeSymbol)
    (ha : a.1 ≠ .home) :
    RunsIn (code src dst).step
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ (encodeInput bits ++ [cleanAtom .home]) (a :: R))
        (Tape.mk₂ (encodeInput bits ++ [cleanAtom .home]) (a :: R))))
      (cfg .done (onPair src dst T
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput bits).reverse ++ a :: R)))
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput bits).reverse ++ a :: R)))))
      (bits.length + 2) := by
  induction bits generalizing a R with
  | nil =>
      have hfirst := RunsIn.single (step_rewind_move hne T
        (Tape.mk₂ [cleanAtom .home] (a :: R))
        (Tape.mk₂ [cleanAtom .home] (a :: R)) ha)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hlast := RunsIn.single (step_rewind_home hne T
        (Tape.mk₂ [] (cleanAtom .home :: a :: R))
        (Tape.mk₂ [] (cleanAtom .home :: a :: R)) rfl)
      simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
        List.length_nil, Nat.zero_add] using hfirst.trans hlast
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_rewind_move hne T
        (Tape.mk₂ (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .home])) (a :: R))
        (Tape.mk₂ (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .home])) (a :: R)) ha)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol b) (a :: R) (by simp [rawInputSymbol, cleanAtom])
      simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_copy {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (bits : List Bool) :
    RunsIn (code src dst).step
      (cfg .start (onPair src dst T (wordTape bits) (wordTape [])))
      (cfg .done (onPair src dst T (wordTape bits) (wordTape bits)))
      (2 * bits.length + 4) := by
  have hstart := RunsIn.single (step_start hne T (wordTape bits) (wordTape []))
  have hscan := runs_scan hne T bits [cleanAtom .home] [cleanAtom .endMark] rfl
  have hback := runs_rewind hne T bits.reverse (cleanAtom .endMark) [] (by simp [cleanAtom])
  have hreverse : encodeInput bits.reverse = (encodeInput bits).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.reverse_reverse, List.length_reverse] at hback
  have hstart' : RunsIn (code src dst).step
      (cfg .start (onPair src dst T (wordTape bits) (wordTape [])))
      (cfg .scan (onPair src dst T
        (Tape.mk₂ [cleanAtom .home] (encodeInput bits ++ [cleanAtom .endMark]))
        (Tape.mk₂ [cleanAtom .home] [cleanAtom .endMark]))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_nil,
      List.reverse_nil, List.nil_append] using hstart
  have hboth := (hstart'.trans hscan).trans hback
  simpa only [wordTape, Tape.mk₁, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hboth

@[simp] theorem step_done (src dst : TapeRegister) (T : TapeTapes) :
    (code src dst).step (cfg .done T) = none := rfl

end TapeCopy
end DepthThreeLowerBound

end Complexity

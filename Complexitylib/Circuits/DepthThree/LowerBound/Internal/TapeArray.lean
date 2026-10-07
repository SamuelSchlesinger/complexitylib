/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeCopy

/-!
# Unrestricted depth-three lower bound: tape array

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeArray.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound
namespace TapeArray

open Turing TapeMultiProgram TapeCopy

/-- Control states of the array routine. -/
inductive State where
  | start
  | scan
  | rewind (read : Bool)
  | done (read : Bool)
  deriving DecidableEq, Fintype, Inhabited

/-- Transition function of the array routine. -/
def code (index array : TapeRegister) (f : Bool → Bool) : TapeMultiProgram State
  | .start, h => emit index array .scan h (h index) (h array) .right
  | .scan, h =>
      match (h index).1 with
      | .bit true => emit index array .scan h (h index) (h array) .right
      | .endMark =>
          match (h array).1 with
          | .bit b => emit index array (.rewind b) h (h index) (rawInputSymbol (f b)) .stay
          | _ => none
      | _ => none
  | .rewind b, h =>
      if (h index).1 = .home then emit index array (.done b) h (h index) (h array) .stay
      else emit index array (.rewind b) h (h index) (h array) .left
  | .done _, _ => none

private theorem replicate_append_cons {α : Type uDepth1} (n : ℕ) (a : α) (L : List α) :
    List.replicate n a ++ a :: L = a :: (List.replicate n a ++ L) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons a) ih

theorem step_start {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) :
    (code index array f).step (cfg .start (onPair index array T I A)) =
      some (cfg .scan (onPair index array T (I.move .right) (A.move .right))) := by
  have h := step_emit (code index array f) hne T I A .start .scan I.head A.head .right
    (by simp [code, heads, hne])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_bit {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol)
    (hI : I.head = rawInputSymbol true) :
    (code index array f).step (cfg .scan (onPair index array T I A)) =
      some (cfg .scan (onPair index array T (I.move .right) (A.move .right))) := by
  have h := step_emit (code index array f) hne T I A .scan .scan I.head A.head .right
    (by simp [code, heads, hne, hI, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_end {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) (b : Bool)
    (hI : I.head = cleanAtom .endMark) (hA : A.head = rawInputSymbol b) :
    (code index array f).step (cfg .scan (onPair index array T I A)) =
      some (cfg (.rewind b) (onPair index array T I (A.write (rawInputSymbol (f b))))) := by
  have h := step_emit (code index array f) hne T I A .scan (.rewind b)
    I.head (rawInputSymbol (f b)) .stay
    (by simp [code, heads, hne, hI, hA, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem step_rewind_move {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) (b : Bool)
    (hI : I.head.1 ≠ .home) :
    (code index array f).step (cfg (.rewind b) (onPair index array T I A)) =
      some (cfg (.rewind b) (onPair index array T (I.move .left) (A.move .left))) := by
  have h := step_emit (code index array f) hne T I A (.rewind b) (.rewind b)
    I.head A.head .left (by simp [code, heads, hne, hI])
  simpa only [Tape.write_self, HeadMove.apply_left] using h

theorem step_rewind_home {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) (b : Bool)
    (hI : I.head.1 = .home) :
    (code index array f).step (cfg (.rewind b) (onPair index array T I A)) =
      some (cfg (.done b) (onPair index array T I A)) := by
  have h := step_emit (code index array f) hne T I A (.rewind b) (.done b)
    I.head A.head .stay (by simp [code, heads, hne, hI])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem runs_scan {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) («prefix» : List Bool)
    (LI LA R : List TapeSymbol) :
    RunsIn (code index array f).step
      (cfg .scan (onPair index array T
        (Tape.mk₂ LI (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .endMark]))
        (Tape.mk₂ LA (encodeInput «prefix» ++ R))))
      (cfg .scan (onPair index array T
        (Tape.mk₂ (List.replicate «prefix».length (rawInputSymbol true) ++ LI) [cleanAtom .endMark])
        (Tape.mk₂ ((encodeInput «prefix»).reverse ++ LA) R)))
      «prefix».length := by
  induction «prefix» generalizing LI LA with
  | nil =>
      simpa only [List.length_nil, List.replicate_zero, List.nil_append,
        encodeInput, List.map_nil, List.reverse_nil] using
        RunsIn.refl (code index array f).step
          (cfg .scan (onPair index array T (Tape.mk₂ LI [cleanAtom .endMark]) (Tape.mk₂ LA R)))
  | cons a «prefix» ih =>
      have hfirst := RunsIn.single (step_scan_bit hne f T
        (Tape.mk₂ LI (rawInputSymbol true ::
          (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .endMark])))
        (Tape.mk₂ LA (rawInputSymbol a :: (encodeInput «prefix» ++ R))) rfl)
      simp only [TapeWord.move_right_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol true :: LI) (rawInputSymbol a :: LA)
      simpa only [List.length_cons, List.replicate_succ, encodeInput, List.map_cons,
        List.cons_append, List.reverse_cons, List.append_assoc, List.nil_append,
        replicate_append_cons, Nat.add_comm] using hfirst.trans hrest

theorem runs_rewind {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (left : List Bool) (b : Bool)
    (i : TapeSymbol) (RI RA : List TapeSymbol) (hi : i.1 ≠ .home) :
    RunsIn (code index array f).step
      (cfg (.rewind b) (onPair index array T
        (Tape.mk₂ (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home]) (i :: RI))
        (Tape.mk₂ (encodeInput left ++ [cleanAtom .home]) RA)))
      (cfg (.done b) (onPair index array T
        (Tape.mk₂ [] (cleanAtom .home ::
          (List.replicate left.length (rawInputSymbol true) ++ i :: RI)))
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput left).reverse ++ RA)))))
      (left.length + 2) := by
  induction left generalizing i RI RA with
  | nil =>
      have hfirst := RunsIn.single (step_rewind_move hne f T
        (Tape.mk₂ [cleanAtom .home] (i :: RI)) (Tape.mk₂ [cleanAtom .home] RA) b hi)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hlast := RunsIn.single (step_rewind_home hne f T
        (Tape.mk₂ [] (cleanAtom .home :: i :: RI))
        (Tape.mk₂ [] (cleanAtom .home :: RA)) b rfl)
      simpa only [List.length_nil, List.replicate_zero, List.nil_append,
        encodeInput, List.map_nil, List.reverse_nil, Nat.zero_add] using hfirst.trans hlast
  | cons a left ih =>
      have hfirst := RunsIn.single (step_rewind_move hne f T
        (Tape.mk₂ (rawInputSymbol true ::
          (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home])) (i :: RI))
        (Tape.mk₂ (rawInputSymbol a :: (encodeInput left ++ [cleanAtom .home])) RA) b hi)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol true) (i :: RI) (rawInputSymbol a :: RA)
        (by simp [rawInputSymbol, cleanAtom])
      simpa only [List.length_cons, List.replicate_succ, encodeInput, List.map_cons,
        List.cons_append, List.reverse_cons, List.append_assoc, List.nil_append,
        replicate_append_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hfirst.trans hrest

theorem runs_modify {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool) :
    RunsIn (code index array f).step
      (cfg .start (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (cfg (.done b) (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ f b :: suffix))))
      (2 * «prefix».length + 4) := by
  have hstart := RunsIn.single (step_start hne f T
    (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix)))
  have hscan := runs_scan hne f T «prefix» [cleanAtom .home] [cleanAtom .home]
    (rawInputSymbol b :: (encodeInput suffix ++ [cleanAtom .endMark]))
  have hwrite := RunsIn.single (step_scan_end hne f T
    (Tape.mk₂ (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .home])
      [cleanAtom .endMark])
    (Tape.mk₂ ((encodeInput «prefix»).reverse ++ [cleanAtom .home])
      (rawInputSymbol b :: (encodeInput suffix ++ [cleanAtom .endMark]))) b rfl rfl)
  simp only [TapeWord.write_mk₂_cons] at hwrite
  have hback := runs_rewind hne f T «prefix».reverse b (cleanAtom .endMark) []
    (rawInputSymbol (f b) :: (encodeInput suffix ++ [cleanAtom .endMark]))
    (by simp [cleanAtom])
  have hreverse : encodeInput «prefix».reverse = (encodeInput «prefix»).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.reverse_reverse, List.length_reverse] at hback
  have hstart' : RunsIn (code index array f).step
      (cfg .start (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (cfg .scan (onPair index array T
        (Tape.mk₂ [cleanAtom .home]
          (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .endMark]))
        (Tape.mk₂ [cleanAtom .home]
          (encodeInput «prefix» ++ rawInputSymbol b :: (encodeInput suffix ++ [cleanAtom
            .endMark]))))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_append,
      List.map_replicate, List.map_cons, List.map_nil, List.reverse_nil,
      List.nil_append, List.append_assoc, List.cons_append] using hstart
  have hboth := ((hstart'.trans hscan).trans hwrite).trans hback
  simpa only [wordTape, Tape.mk₁, encodeInput, List.map_replicate, List.map_append,
    List.map_cons, List.append_assoc, List.cons_append, List.append_nil,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hboth

theorem runs_read {index array : TapeRegister} (hne : index ≠ array)
    (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool) :
    RunsIn (code index array id).step
      (cfg .start (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (cfg (.done b) (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (2 * «prefix».length + 4) :=
  runs_modify hne id T «prefix» suffix b

@[simp] theorem step_done (index array : TapeRegister) (f : Bool → Bool)
    (T : TapeTapes) (b : Bool) :
    (code index array f).step (cfg (.done b) T) = none := rfl

end TapeArray
end DepthThreeLowerBound

end Complexity

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeStoreRepresentation
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitConvolution

/-!
# Unrestricted depth-three lower bound: tape xor

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeXor.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeXor

open Turing TapeMultiProgram TapeCopy

/-- Control states of the xor routine. -/
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

/-- Initial control state of the xor routine. -/
def start : State := .start
/-- Terminal control state of the xor routine. -/
def done : State := .done

/-- Transition function of the xor routine. -/
def program (src dst : TapeRegister) : TapeMultiProgram State
  | .start, h => emit src dst .scan h (h src) (h dst) .right
  | .scan, h =>
      match (h src).1, (h dst).1 with
      | .bit a, .bit b =>
          emit src dst .scan h (h src) (rawInputSymbol (Bool.xor a b)) .right
      | .endMark, .endMark => emit src dst .rewind h (h src) (h dst) .stay
      | _, _ => none
  | .rewind, h =>
      if (h src).1 = .home then emit src dst .done h (h src) (h dst) .stay
      else emit src dst .rewind h (h src) (h dst) .left
  | .done, _ => none

@[simp] theorem program_done (src dst : TapeRegister) (h : TapeHeads) :
    program src dst done h = none := rfl

theorem step_start {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) :
    (program src dst).step (cfg .start (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right) (D.move .right))) := by
  have h := step_emit (program src dst) hne T S D .start .scan S.head D.head .right
    (by simp [program, heads, hne])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_bit {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (a b : Bool)
    (hS : S.head = rawInputSymbol a) (hD : D.head = rawInputSymbol b) :
    (program src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right)
        ((D.write (rawInputSymbol (Bool.xor a b))).move .right))) := by
  have h := step_emit (program src dst) hne T S D .scan .scan
    S.head (rawInputSymbol (Bool.xor a b)) .right
    (by simp [program, heads, hne, hS, hD, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_end {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol)
    (hS : S.head = cleanAtom .endMark) (hD : D.head = cleanAtom .endMark) :
    (program src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T S D)) := by
  have h := step_emit (program src dst) hne T S D .scan .rewind S.head D.head .stay
    (by simp [program, heads, hne, hS, hD, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem step_rewind_move {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 ≠ .home) :
    (program src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T (S.move .left) (D.move .left))) := by
  have h := step_emit (program src dst) hne T S D .rewind .rewind S.head D.head .left
    (by simp [program, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_left] using h

theorem step_rewind_home {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 = .home) :
    (program src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .done (onPair src dst T S D)) := by
  have h := step_emit (program src dst) hne T S D .rewind .done S.head D.head .stay
    (by simp [program, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem runs_scan {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (a b : List Bool) (LS LD : List TapeSymbol)
    (hlen : a.length = b.length) :
    RunsIn (program src dst).step
      (cfg .scan (onPair src dst T
        (Tape.mk₂ LS (encodeInput a ++ [cleanAtom .endMark]))
        (Tape.mk₂ LD (encodeInput b ++ [cleanAtom .endMark]))))
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ ((encodeInput a).reverse ++ LS) [cleanAtom .endMark])
        (Tape.mk₂ ((encodeInput (List.zipWith Bool.xor a b)).reverse ++ LD)
          [cleanAtom .endMark])))
      (a.length + 1) := by
  induction a generalizing b LS LD with
  | nil =>
      cases b with
      | nil =>
          have h := RunsIn.single (step_scan_end hne T
            (Tape.mk₂ LS [cleanAtom .endMark])
            (Tape.mk₂ LD [cleanAtom .endMark]) rfl rfl)
          simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
            List.length_nil, Nat.zero_add, List.zipWith_nil_left] using h
      | cons y ys => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
      cases b with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y ys =>
          have htail : xs.length = ys.length := Nat.succ.inj hlen
          have hfirst := RunsIn.single (step_scan_bit hne T
            (Tape.mk₂ LS (rawInputSymbol x :: (encodeInput xs ++ [cleanAtom .endMark])))
            (Tape.mk₂ LD (rawInputSymbol y :: (encodeInput ys ++ [cleanAtom .endMark])))
            x y rfl rfl)
          simp only [TapeWord.write_mk₂_cons, TapeWord.move_right_mk₂_cons] at hfirst
          have hrest := ih ys (rawInputSymbol x :: LS)
            (rawInputSymbol (Bool.xor x y) :: LD) htail
          simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
            List.append_assoc, List.nil_append, List.length_cons, List.zipWith_cons_cons,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_rewind {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (a b : List Bool) (c : TapeSymbol) (RS RD : List TapeSymbol)
    (hlen : a.length = b.length) (hc : c.1 ≠ .home) :
    RunsIn (program src dst).step
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ (encodeInput a ++ [cleanAtom .home]) (c :: RS))
        (Tape.mk₂ (encodeInput b ++ [cleanAtom .home]) RD)))
      (cfg .done (onPair src dst T
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput a).reverse ++ c :: RS)))
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput b).reverse ++ RD)))))
      (a.length + 2) := by
  induction a generalizing b c RS RD with
  | nil =>
      cases b with
      | nil =>
          have hfirst := RunsIn.single (step_rewind_move hne T
            (Tape.mk₂ [cleanAtom .home] (c :: RS))
            (Tape.mk₂ [cleanAtom .home] RD) hc)
          simp only [TapeWord.move_left_mk₂_cons] at hfirst
          have hlast := RunsIn.single (step_rewind_home hne T
            (Tape.mk₂ [] (cleanAtom .home :: c :: RS))
            (Tape.mk₂ [] (cleanAtom .home :: RD)) rfl)
          simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
            List.length_nil, Nat.zero_add] using hfirst.trans hlast
      | cons y ys => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
      cases b with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y ys =>
          have htail : xs.length = ys.length := Nat.succ.inj hlen
          have hfirst := RunsIn.single (step_rewind_move hne T
            (Tape.mk₂ (rawInputSymbol x :: (encodeInput xs ++ [cleanAtom .home])) (c :: RS))
            (Tape.mk₂ (rawInputSymbol y :: (encodeInput ys ++ [cleanAtom .home])) RD) hc)
          simp only [TapeWord.move_left_mk₂_cons] at hfirst
          have hrest := ih ys (rawInputSymbol x) (c :: RS) (rawInputSymbol y :: RD)
            htail (by simp [rawInputSymbol, cleanAtom])
          simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
            List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_xor {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (a b : List Bool) (hlen : a.length = b.length) :
    RunsIn (program src dst).step
      (cfg start (onPair src dst T (wordTape a) (wordTape b)))
      (cfg done (onPair src dst T (wordTape a) (wordTape (List.zipWith Bool.xor a b))))
      (2 * a.length + 4) := by
  have hstart := RunsIn.single (step_start hne T (wordTape a) (wordTape b))
  have hscan := runs_scan hne T a b [cleanAtom .home] [cleanAtom .home] hlen
  have hzip : (List.zipWith Bool.xor a b).length = a.length := by
    simp only [List.length_zipWith, ← hlen, min_self]
  have hback := runs_rewind hne T a.reverse (List.zipWith Bool.xor a b).reverse
    (cleanAtom .endMark) [] [cleanAtom .endMark]
    (by simp only [List.length_reverse, hzip]) (by simp [cleanAtom])
  have hreverse (l : List Bool) : encodeInput l.reverse = (encodeInput l).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.reverse_reverse, List.length_reverse] at hback
  have hstart' : RunsIn (program src dst).step
      (cfg .start (onPair src dst T (wordTape a) (wordTape b)))
      (cfg .scan (onPair src dst T
        (Tape.mk₂ [cleanAtom .home] (encodeInput a ++ [cleanAtom .endMark]))
        (Tape.mk₂ [cleanAtom .home] (encodeInput b ++ [cleanAtom .endMark])))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_nil,
      List.reverse_nil, List.nil_append] using hstart
  have hboth := (hstart'.trans hscan).trans hback
  have htime : (1 + (a.length + 1)) + (a.length + 2) = 2 * a.length + 4 := by omega
  simpa only [start, done, wordTape, Tape.mk₁, htime] using hboth

theorem runs_store {src dst : TapeRegister} (hne : src ≠ dst)
    (σ : TapeStore) (a b : List Bool) (hsrc : σ src = a) (hdst : σ dst = b)
    (hlen : a.length = b.length) :
    RunsIn (program src dst).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ dst (List.zipWith Bool.xor a b))))
      (2 * a.length + 4) := by
  have h := runs_xor hne (storeTapes σ) a b hlen
  have hi : onPair src dst (storeTapes σ) (wordTape a) (wordTape b) = storeTapes σ :=
    TapeProductTerm.onPair_eq_self (by simp only [storeTapes_apply, hsrc])
      (by simp only [storeTapes_apply, hdst])
  have ho : onPair src dst (storeTapes σ) (wordTape a)
      (wordTape (List.zipWith Bool.xor a b)) =
        storeTapes (Function.update σ dst (List.zipWith Bool.xor a b)) := by
    rw [← TapeArithmetic.update_onPair_dst hne (storeTapes σ) (wordTape a) (wordTape b),
      hi, storeTapes_update]
  simpa only [hi, ho] using h

theorem wordList_xor {n : ℕ} (a b : BitWord n) :
    wordList (wordXor a b) = List.zipWith Bool.xor (wordList a) (wordList b) := by
  apply List.ext_getElem
  · simp only [wordList_length, List.length_zipWith, min_self]
  · intro i hi hj
    simp only [wordList, wordXor, List.getElem_zipWith, List.getElem_ofFn]

theorem runs_wordStore {src dst : TapeRegister} (hne : src ≠ dst)
    (σ : TapeStore) {n : ℕ} (a b : BitWord n)
    (hsrc : σ src = wordList a) (hdst : σ dst = wordList b) :
    RunsIn (program src dst).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ dst (wordList (wordXor a b)))))
      (2 * n + 4) := by
  have h := runs_store hne σ (wordList a) (wordList b) hsrc hdst
    (by simp only [wordList_length])
  simpa only [wordList_length, ← wordList_xor] using h

end TapeXor
end DepthThreeLowerBound

end Complexity

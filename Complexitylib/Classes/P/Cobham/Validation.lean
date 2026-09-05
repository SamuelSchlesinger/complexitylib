/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Cobham
public meta import Complexitylib.Classes.P.Cobham
public import Complexitylib.Classes.P.Cobham.Internal.Encoding
public meta import Complexitylib.Classes.P.Cobham.Internal.Encoding

/-!
# Executable validation for Cobham's characterization

These closed checks guard the representation choices on which the formal
characterization depends: the all-one smash basis, recursion on notation,
fixed-arity tuple encoding, configuration tape order, corrected writes, and the
edge cases of zero work tapes and a head at the simulation-window boundary.

This module is intentionally absent from the public import graph. Build it with
`lake build --wfail Complexitylib.Classes.P.Cobham.Validation`.
-/


public section

namespace Complexity

namespace Cobham.Validation

/-! ## Algebra and tuple-encoding checks -/

#guard Complexity.smash [false, true] [true, false, false] = List.replicate 6 true
#guard Complexity.smash [] [true, false] = []

#guard recNotation (n := 0) (fun _ => [])
    (fun w => false :: w 1) (fun w => true :: w 1) [false, true]
    (fun i => Fin.elim0 i) = [false, true]

private def sampleVec : Fin 2 → List Bool := ![[false], [true, false]]

#guard encodeVec sampleVec = pair (pair [] [true, false]) [false]
#guard vectorLength sampleVec = 3
#guard (encodeVec sampleVec).length = 11

/-! ## Concrete tape-layout checks -/

private inductive Q where
  | go
  | halt
  deriving DecidableEq

private instance : Fintype Q where
  elems := ⟨↑([Q.go, Q.halt] : List Q), by decide⟩
  complete := fun x => by cases x <;> decide

private def guardedDir (read : Γ) (otherwise : Dir3) : Dir3 :=
  if read = Γ.start then .right else otherwise

/-- A one-work-tape machine whose output and work writes are deliberately
different, so swapping their encoded positions changes the checked result. -/
private def layoutTM : TM 1 where
  Q := Q
  qstart := .go
  qhalt := .halt
  δ := fun _ iHead wHeads oHead =>
    (.halt, fun _ => Γw.one, Γw.zero, guardedDir iHead .stay,
      fun i => guardedDir (wHeads i) .stay, guardedDir oHead .stay)
  δ_right_of_start := by
    intro q iHead wHeads oHead
    simp [guardedDir]

private def atFirstCell (symbol : Γ) : Tape :=
  (Tape.init [symbol]).move .right

#guard correctWrite (Tape.init []) Γ.zero = Γ.start
#guard correctWrite (atFirstCell Γ.one) Γ.zero = Γ.zero

private def layoutCfg : Cfg 1 Q where
  state := .go
  input := atFirstCell Γ.zero
  work := fun _ => atFirstCell Γ.blank
  output := atFirstCell Γ.one

/-- The encoding order is input, output, then work tapes. -/
example :
    (cfgTapes layoutCfg).map Tape.read = [Γ.zero, Γ.one, Γ.blank] := by
  native_decide

/-- The action list follows the same order and keeps the output/work writes
distinct. -/
example :
    stepActs layoutTM layoutCfg =
      [(Γ.zero, .stay), (Γ.zero, .stay), (Γ.one, .stay)] := by
  native_decide

/-- A concrete machine step writes zero to output and one to work, guarding
against an accidental output/work transposition. -/
example :
    (match layoutTM.step layoutCfg with
    | none => false
    | some c =>
        decide (c.output.cells 1 = Γ.zero) && decide ((c.work 0).cells 1 = Γ.one)) = true := by
  decide

private def boundaryTape : Tape :=
  ((Tape.init [Γ.zero, Γ.one]).move .right).move .right

private def paddedHalves (W : ℕ) (t : Tape) : List Bool × List Bool :=
  (padTo (blockRuler W) (leftCode t), padTo (blockRuler W) (rightCode t W))

/-- A right move from `head = W` still fits the advertised block width. -/
example :
    tapeStepBlocks (blockRuler 2) Γ.one .right
        (paddedHalves 2 boundaryTape).1 (paddedHalves 2 boundaryTape).2 =
      paddedHalves 2 ((boundaryTape.write Γ.one).move .right) := by
  native_decide

/-! ## Degenerate-machine checks -/

private inductive HaltQ where
  | halt
  deriving DecidableEq

private instance : Fintype HaltQ where
  elems := ⟨↑([HaltQ.halt] : List HaltQ), by decide⟩
  complete := fun x => by cases x; decide

private def haltedTM : TM 0 where
  Q := HaltQ
  qstart := .halt
  qhalt := .halt
  δ := fun _ _ _ _ =>
    (.halt, fun i => Fin.elim0 i, Γw.blank, .right,
      fun i => Fin.elim0 i, .right)
  δ_right_of_start := by
    intro q iHead wHeads oHead
    simp

/-- Zero work tapes, empty input/output, and `qstart = qhalt` retain their
intended semantics. -/
example :
    (let c := haltedTM.initCfg []
     (cfgTapes c).length == 2 && decide (c.input.read = Γ.start) &&
       decide (c.output.read = Γ.start) && (haltedTM.step c).isNone) = true := by
  decide

end Cobham.Validation

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Parsing

/-!
# Emitting finite-alphabet codewords

Reading a source letter emits its opening delimiter. Finite control then emits
its unary index and closing delimiter. A complete output costs exactly its
binary encoded length plus one final halting transition.
-/

@[expose] public section

namespace Complexity.MathlibTM0.AlphabetMachine

variable {Input Output : Type} (M : AlphabetMachine Input Output)
variable (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)

/-- Output emission from the represented source tape. -/
structure Emitting {w : List Bool} (tape : Turing.Tape M.simulatorSource.binary.Alphabet)
    (emitted : List Bool)
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) : Prop where
  /-- Ready to read the next source letter. -/
  state : d.state = some (.source .emit)
  /-- Previously emitted bits. -/
  output : d.output = emitted
  /-- Remaining source tape relative to the work heads. -/
  tape : ∀ i z, d.workTapes i (d.workTapePos i + z) =
    SymbolTracks.encode (tape.nth z) (trackEquiv M.simulatorSource.binary i)

/-- A symbol's opening delimiter has been emitted; its index and closing delimiter remain. -/
structure Pending {w : List Bool} (n : Fin (co.size + 1))
    (tape : Turing.Tape M.simulatorSource.binary.Alphabet) (emitted : List Bool)
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) : Prop where
  /-- Remaining unary index bits. -/
  state : d.state = some (.emit n)
  /-- Previously emitted bits. -/
  output : d.output = emitted
  /-- Source tracks are already positioned at the following letter. -/
  tape : ∀ i z, d.workTapes i (d.workTapePos i + z) =
    SymbolTracks.encode (tape.nth z) (trackEquiv M.simulatorSource.binary i)

lemma Emitting.read {w : List Bool} {tape : Turing.Tape M.simulatorSource.binary.Alphabet}
    {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w} (h : Emitting M ci co tape emitted d) :
    SymbolTracks.decode (fun a => d.workTapeSymbols
      ((trackEquiv M.simulatorSource.binary).symm a)) = tape.head := by
  have he : (fun a => d.workTapeSymbols ((trackEquiv M.simulatorSource.binary).symm a)) =
      SymbolTracks.encode tape.head := by
    funext a
    simpa [Turing.Cfg.workTapeSymbols] using h.tape ((trackEquiv M.simulatorSource.binary).symm a) 0
  rw [he, SymbolTracks.decode_encode]

lemma pending_run (n : ℕ) (hn : n < co.size + 1) {w : List Bool}
    {tape : Turing.Tape M.simulatorSource.binary.Alphabet} {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w}
    (h : Pending M ci co ⟨n, hn⟩ tape emitted d) :
    Emitting M ci co tape (emitted ++ List.replicate n true ++ [false])
      ((machine M ci co).runFrom d (n + 1)) := by
  induction n generalizing emitted d with
  | zero =>
      change Emitting M ci co tape (emitted ++ [] ++ [false]) ((machine M ci co).step d)
      rw [Turing.MultiTapeTM.step_apply_of_state h.state]
      refine ⟨rfl, ?_, ?_⟩
      · simp [machine, pause, Turing.Action.apply, h.output]
      · simpa [machine, pause, Turing.Action.apply] using h.tape
  | succ n ih =>
      have hs : Pending M ci co ⟨n, by omega⟩ tape (emitted ++ [true])
          ((machine M ci co).step d) := by
        rw [Turing.MultiTapeTM.step_apply_of_state h.state]
        refine ⟨rfl, ?_, ?_⟩
        · simp [machine, pause, Turing.Action.apply, h.output]
        · simpa [machine, pause, Turing.Action.apply] using h.tape
      rw [run_succ_first]
      simpa [List.replicate_succ, List.append_assoc] using ih (by omega) hs

lemma Emitting.start {w : List Bool} {tape : Turing.Tape M.simulatorSource.binary.Alphabet}
    {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w} (h : Emitting M ci co tape emitted d)
    (a : Output) (ha : M.readSymbol (MarkedMachine.Symbol.value tape.head) = some a) :
    Pending M ci co ⟨(co.index a).val, by have := (co.index a).isLt; omega⟩
      (tape.move .right) (emitted ++ [false]) ((machine M ci co).step d) := by
  rw [Turing.MultiTapeTM.step_apply_of_state h.state]
  simp only [machine, Emitting.read M ci co h, ha]
  refine ⟨rfl, ?_, ?_⟩
  · simp [Turing.Action.apply, h.output]
  · intro i z
    simp only [Turing.Action.apply, Turing.Tape.move_right_nth, SignType.coe_one]
    convert h.tape i (z + 1) using 1
    congr 1
    omega

lemma Emitting.halt {w : List Bool} {tape : Turing.Tape M.simulatorSource.binary.Alphabet}
    {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w} (h : Emitting M ci co tape emitted d)
    (ha : M.readSymbol (MarkedMachine.Symbol.value tape.head) = none) :
    ((machine M ci co).step d).state = none ∧
      ((machine M ci co).step d).output = emitted := by
  rw [Turing.MultiTapeTM.step_apply_of_state h.state]
  simp [machine, Emitting.read M ci co h, ha, pause, Turing.Action.apply, h.output]

lemma Emitting.run {w : List Bool} (output : List Output)
    {tape : Turing.Tape M.simulatorSource.binary.Alphabet} {emitted : List Bool}
    {d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w} (h : Emitting M ci co tape emitted d)
    (ho : ∀ j : ℕ, M.readSymbol (MarkedMachine.Symbol.value (tape.nth j)) = output[j]?) :
    ((machine M ci co).runFrom d ((co.encode output).length + 1)).state = none ∧
      ((machine M ci co).runFrom d ((co.encode output).length + 1)).output =
        emitted ++ co.encode output := by
  induction output generalizing tape emitted d with
  | nil =>
      have hb : M.readSymbol (MarkedMachine.Symbol.value tape.head) = none := by simpa using ho 0
      simpa [FiniteAlphabetCode.encode, Turing.MultiTapeTM.runFrom] using
        Emitting.halt M ci co h hb
  | cons a output ih =>
      have hb : M.readSymbol (MarkedMachine.Symbol.value tape.head) = some a := by simpa using ho 0
      have hs := Emitting.start M ci co h a hb
      have hp : Emitting M ci co (tape.move .right) (emitted ++ co.symbol a)
          ((machine M ci co).runFrom ((machine M ci co).step d) ((co.index a).val + 1)) := by
        simpa [FiniteAlphabetCode.symbol, List.append_assoc] using
          pending_run M ci co (co.index a).val (by have := (co.index a).isLt; omega) hs
      have ht : ∀ j : ℕ,
          M.readSymbol (MarkedMachine.Symbol.value ((tape.move .right).nth j)) = output[j]? := by
        intro j
        rw [Turing.Tape.move_right_nth]
        simpa only [List.getElem?_cons_succ, Nat.cast_add, Nat.cast_one] using ho (j + 1)
      have hr := ih hp ht
      rw [← run_add, ← run_succ_first] at hr
      have he : (co.encode (a :: output)).length + 1 =
          ((co.index a).val + 1 + ((co.encode output).length + 1)) + 1 := by
        rw [FiniteAlphabetCode.encode_cons, List.length_append, FiniteAlphabetCode.symbol_length]
        omega
      rw [he]
      simpa only [FiniteAlphabetCode.encode_cons, List.append_assoc] using hr

end Complexity.MathlibTM0.AlphabetMachine

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Defs
public import Complexitylib.Encoding.FiniteAlphabet.Internal
public import Complexitylib.Interop.Mathlib.TM0.Marked.Internal.Initialization

/-!
# Parsing finite-alphabet inputs onto source symbol tracks

The parser's finite control records an opening delimiter and a bounded unary
index. Each completed codeword writes one marked source cell. Invalid codes
halt with empty output before the source is started.
-/

@[expose] public section

namespace Complexity.MathlibTM0.AlphabetMachine

open FiniteAlphabetCode

variable {Input Output : Type} (M : AlphabetMachine Input Output)
variable (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)

/-- Source cells written before the final empty-input check. -/
def prefixCells : List Input → List M.Alphabet
  | [] => []
  | a :: xs => M.inputSymbol true a :: xs.map (M.inputSymbol false)

lemma prefixCells_length (xs : List Input) : (prefixCells M xs).length = xs.length := by
  cases xs <;> simp [prefixCells]

lemma prefixCells_append (xs : List Input) (a : Input) :
    prefixCells M (xs ++ [a]) = prefixCells M xs ++ [M.inputSymbol xs.isEmpty a] := by
  cases xs <;> simp [prefixCells]

lemma inputCells_false (xs : List Input) :
    M.inputCells false xs = xs.map (M.inputSymbol false) := by
  induction xs <;> simp_all [inputCells]

lemma inputCells_true (xs : List Input) :
    M.inputCells true xs = if xs.isEmpty then [M.empty] else prefixCells M xs := by
  cases xs <;> simp [inputCells, prefixCells, inputCells_false]

/-- Number of input bits already consumed by a partial parse. -/
def copyPrefix (xs : List Input) (count : Option (Fin (ci.size + 1))) : List Bool :=
  ci.encode xs ++ pendingPrefix (count.map Fin.val)

/-- State after writing `xs` and reading the indicated prefix of the next codeword. -/
noncomputable def copyCfg (w : List Bool) (xs : List Input)
    (count : Option (Fin (ci.size + 1))) (h : (copyPrefix ci xs count).length ≤ w.length) :
    Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w where
  state := some (.copy xs.isEmpty count)
  inputPos := ⟨(copyPrefix ci xs count).length + 1, by omega⟩
  workTapes := MarkedMachine.contents M.simulatorSource (prefixCells M xs)
  workTapePos := fun _ => xs.length
  output := []

/-- End-of-input configuration before rewinding the parsed input. -/
noncomputable def endCfg (w : List Bool) (xs : List Input) :
    Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w where
  state := some (.rewind true)
  inputPos := ⟨w.length, by omega⟩
  workTapes := MarkedMachine.contents M.simulatorSource (M.inputCells true xs)
  workTapePos := fun _ => xs.length
  output := []

lemma copyCfg_read {w : List Bool} (xs : List Input) (count : Option (Fin (ci.size + 1)))
    (h : (copyPrefix ci xs count).length ≤ w.length) (rest : List Bool)
    (hw : w = copyPrefix ci xs count ++ rest) :
    (copyCfg M ci co w xs count h).inputSymbol = rest.head? := by
  cases rest with
  | nil =>
      have he : (copyPrefix ci xs count).length = w.length := by simp [hw]
      exact Turing.inputSymbol_eq_none_of_boundary (Or.inr (by simp [copyCfg, he]))
  | cons b rest =>
      have ht : (copyPrefix ci xs count).length < w.length := by simp [hw]
      have hb : w[(copyPrefix ci xs count).length] = b := by simp [hw]
      rw [← hb]
      exact Turing.inputSymbolInner _ (by simp [copyCfg, Nat.add_comm]) ht

lemma copyCfg_zero (w : List Bool) :
    copyCfg M ci co w [] none (by simp [copyPrefix, encode, pendingPrefix]) =
      (machine M ci co).initCfg w := by
  simp [copyCfg, copyPrefix, encode, pendingPrefix, prefixCells,
    Turing.MultiTapeTM.initCfg, Turing.Cfg.init, machine]
  exact MarkedMachine.contents_nil M.simulatorSource

lemma run_add {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) (s t : ℕ) :
    (machine M ci co).runFrom d (s + t) =
      (machine M ci co).runFrom ((machine M ci co).runFrom d s) t := by
  simp only [Turing.MultiTapeTM.runFrom, Nat.add_comm s t, Function.iterate_add_apply]

lemma copy_open {w : List Bool} (xs : List Input) (rest : List Bool)
    (hw : w = copyPrefix ci xs none ++ false :: rest)
    (h : (copyPrefix ci xs none).length ≤ w.length)
    (h' : (copyPrefix ci xs (some 0)).length ≤ w.length) :
    (machine M ci co).step (copyCfg M ci co w xs none h) =
      copyCfg M ci co w xs (some 0) h' := by
  have hin := copyCfg_read M ci co xs none h (false :: rest) hw
  have hp : (copyCfg M ci co w xs none h).inputPos.val ≠ w.length + 1 := by
    simp only [copyCfg]
    simp only [hw, List.length_append, List.length_cons]
    omega
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty none) rfl]
  simp only [machine, hin, List.head?_cons]
  apply Turing.Cfg.ext
  · rfl
  · simpa [pause, Turing.Action.apply, copyCfg, copyPrefix, pendingPrefix,
      List.length_append, Nat.add_assoc] using
      Turing.moveInputPos_pos_of_ne_right (copyCfg M ci co w xs none h).inputPos hp
  · rfl
  · simp [pause, Turing.Action.apply, copyCfg]
  · rfl

lemma copy_true {w : List Bool} (xs : List Input) (i : Fin (ci.size + 1))
    (rest : List Bool) (hw : w = copyPrefix ci xs (some i) ++ true :: rest)
    (hi : i.val + 1 < ci.size)
    (h : (copyPrefix ci xs (some i)).length ≤ w.length)
    (h' : (copyPrefix ci xs (some ⟨i.val + 1, by omega⟩)).length ≤ w.length) :
    (machine M ci co).step (copyCfg M ci co w xs (some i) h) =
      copyCfg M ci co w xs (some ⟨i.val + 1, by omega⟩) h' := by
  have hin := copyCfg_read M ci co xs (some i) h (true :: rest) hw
  have hp : (copyCfg M ci co w xs (some i) h).inputPos.val ≠ w.length + 1 := by
    simp only [copyCfg]
    simp only [hw, List.length_append, List.length_cons]
    omega
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty (some i)) rfl]
  simp only [machine, hin, List.head?_cons, dite_eq_ite, hi]
  apply Turing.Cfg.ext
  · rfl
  · simpa [pause, Turing.Action.apply, copyCfg, copyPrefix, pendingPrefix,
      List.length_append, Nat.add_assoc] using
      Turing.moveInputPos_pos_of_ne_right (copyCfg M ci co w xs (some i) h).inputPos hp
  · rfl
  · simp [pause, Turing.Action.apply, copyCfg]
  · rfl

lemma copy_close_prefix (xs : List Input) (i : Fin (ci.size + 1)) (hi : i.val < ci.size) :
    copyPrefix ci (xs ++ [ci.index.symm ⟨i.val, hi⟩]) none =
      copyPrefix ci xs (some i) ++ [false] := by
  simp [copyPrefix, pendingPrefix, encode_append, encode_cons, encode_nil,
    symbol, List.append_assoc]

lemma copy_close {w : List Bool} (xs : List Input) (i : Fin (ci.size + 1))
    (rest : List Bool) (hw : w = copyPrefix ci xs (some i) ++ false :: rest)
    (hi : i.val < ci.size)
    (h : (copyPrefix ci xs (some i)).length ≤ w.length)
    (h' : (copyPrefix ci (xs ++ [ci.index.symm ⟨i.val, hi⟩]) none).length ≤ w.length) :
    (machine M ci co).step (copyCfg M ci co w xs (some i) h) =
      copyCfg M ci co w (xs ++ [ci.index.symm ⟨i.val, hi⟩]) none h' := by
  have hin := copyCfg_read M ci co xs (some i) h (false :: rest) hw
  have hp : (copyCfg M ci co w xs (some i) h).inputPos.val ≠ w.length + 1 := by
    simp only [copyCfg]
    simp only [hw, List.length_append, List.length_cons]
    omega
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty (some i)) rfl]
  simp only [machine, hin, List.head?_cons, hi, dite_true]
  apply Turing.Cfg.ext
  · simp [copyCfg]
  · simpa [Turing.Action.apply, copyCfg, copy_close_prefix ci xs i hi] using
      Turing.moveInputPos_pos_of_ne_right (copyCfg M ci co w xs (some i) h).inputPos hp
  · funext j
    simp only [Turing.Action.apply, copyCfg, prefixCells_append]
    simpa only [prefixCells_length] using
      (MarkedMachine.contents_append M.simulatorSource (prefixCells M xs)
        (M.inputSymbol xs.isEmpty (ci.index.symm ⟨i.val, hi⟩)) j).symm
  · funext j
    simp [Turing.Action.apply, copyCfg, Nat.cast_add]
  · rfl

lemma copy_end {w : List Bool} (xs : List Input) (hw : w = ci.encode xs)
    (h : (copyPrefix ci xs none).length ≤ w.length) :
    (machine M ci co).step (copyCfg M ci co w xs none h) = endCfg M ci co w xs := by
  have hin := copyCfg_read M ci co xs none h [] (by simpa [copyPrefix, pendingPrefix] using hw)
  have he : (copyPrefix ci xs none).length = w.length := by
    simp [copyPrefix, pendingPrefix, hw]
  rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty none) rfl]
  simp only [machine, hin, List.head?_nil]
  apply Turing.Cfg.ext
  · rfl
  · have hp : (copyCfg M ci co w xs none h).inputPos ≠ 0 := by
      intro hh
      have := congrArg Fin.val hh
      simp [copyCfg] at this
    simpa [Turing.Action.apply, copyCfg, endCfg, he] using
      Turing.moveInputPos_neg_of_ne_left (copyCfg M ci co w xs none h).inputPos hp
  · funext j
    cases xs with
    | nil =>
        simpa [Turing.Action.apply, copyCfg, endCfg, inputCells, prefixCells,
          MarkedMachine.contents_nil] using
          (MarkedMachine.contents_append M.simulatorSource [] M.empty j).symm
    | cons a xs => simp [Turing.Action.apply, copyCfg, endCfg, inputCells_true]
  · rfl
  · rfl

lemma run_rejected {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) (t : ℕ)
    (h : ((machine M ci co).step d).state = none ∧
      ((machine M ci co).step d).output = []) :
    ((machine M ci co).runFrom d (t + 1)).state = none ∧
      ((machine M ci co).runFrom d (t + 1)).output = [] := by
  have he := (machine M ci co).runFrom_eq_of_halt d
    (by omega : 1 ≤ t + 1) (by simpa [Turing.MultiTapeTM.runFrom] using h.1)
  rw [he]
  exact h

end Complexity.MathlibTM0.AlphabetMachine

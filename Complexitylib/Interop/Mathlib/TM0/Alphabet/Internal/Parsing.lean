/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Alphabet.Internal.Copy

/-!
# The binary input parser implements the finite-alphabet decoder

An induction on the unread suffix proves both successful copying and early
rejection. All inputs finish this phase within their length plus one step.
-/

@[expose] public section

namespace Complexity.MathlibTM0.AlphabetMachine

open FiniteAlphabetCode

variable {Input Output : Type} (M : AlphabetMachine Input Output)
variable (ci : FiniteAlphabetCode Input) (co : FiniteAlphabetCode Output)

/-- Successful parsing loads the complete input; failed parsing halts with empty output. -/
def Parsed (w : List Bool) (xs : List Input) (result : Option (List Input))
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) : Prop :=
  match result with
  | none => d.state = none ∧ d.output = []
  | some ys => d = endCfg M ci co w (xs ++ ys)

lemma parsed_cons {w : List Bool} (xs : List Input) (a : Input) (result : Option (List Input))
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) :
    Parsed M ci co w (xs ++ [a]) result d ↔ Parsed M ci co w xs (result.map (a :: ·)) d := by
  cases result <;> simp [Parsed, List.append_assoc]

lemma run_succ_first {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) (t : ℕ) :
    (machine M ci co).runFrom d (t + 1) =
      (machine M ci co).runFrom ((machine M ci co).step d) t :=
  Function.iterate_succ_apply _ _ _

lemma run_succ_last {w : List Bool}
    (d : Turing.Cfg (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase ci.size co.size M.State) w) (t : ℕ) :
    (machine M ci co).runFrom d (t + 1) =
      (machine M ci co).step ((machine M ci co).runFrom d t) :=
  Function.iterate_succ_apply' _ _ _

lemma run_copy_decode (w : List Bool) (bits : List Bool) (xs : List Input)
    (count : Option (Fin (ci.size + 1)))
    (hw : w = copyPrefix ci xs count ++ bits)
    (h : (copyPrefix ci xs count).length ≤ w.length) :
    Parsed M ci co w xs (ci.decodeFrom (count.map Fin.val) bits)
      ((machine M ci co).runFrom (copyCfg M ci co w xs count h) (bits.length + 1)) := by
  induction bits generalizing xs count with
  | nil =>
      cases count with
      | none =>
          change (machine M ci co).runFrom (copyCfg M ci co w xs none h) 1 =
            endCfg M ci co w (xs ++ [])
          simpa [Turing.MultiTapeTM.runFrom] using
            copy_end M ci co xs (by simpa [copyPrefix, pendingPrefix] using hw) h
      | some i =>
          have hin := copyCfg_read M ci co xs (some i) h [] hw
          change ((machine M ci co).step (copyCfg M ci co w xs (some i) h)).state = none ∧
            ((machine M ci co).step (copyCfg M ci co w xs (some i) h)).output = []
          rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty (some i)) rfl]
          simp only [machine, hin, List.head?_nil]
          simp [pause, Turing.Action.apply, copyCfg]
  | cons b bits ih =>
      have hin := copyCfg_read M ci co xs count h (b :: bits) hw
      cases count with
      | none =>
          cases b with
          | true =>
              change ((machine M ci co).runFrom (copyCfg M ci co w xs none h)
                (bits.length + 1 + 1)).state = none ∧
                ((machine M ci co).runFrom (copyCfg M ci co w xs none h)
                  (bits.length + 1 + 1)).output = []
              apply run_rejected
              rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty none) rfl]
              simp only [machine, hin, List.head?_cons]
              simp [pause, Turing.Action.apply, copyCfg]
          | false =>
              have hp : copyPrefix ci xs (some 0) = copyPrefix ci xs none ++ [false] := by
                simp [copyPrefix, pendingPrefix]
              have hw' : w = copyPrefix ci xs (some 0) ++ bits := by
                simpa [hp, List.append_assoc] using hw
              have h' : (copyPrefix ci xs (some 0)).length ≤ w.length := by simp [hw']
              change Parsed M ci co w xs (ci.decodeFrom (some 0) bits)
                ((machine M ci co).runFrom (copyCfg M ci co w xs none h) (bits.length + 1 + 1))
              rw [run_succ_first, copy_open M ci co xs bits hw h h']
              exact ih xs (some 0) hw' h'
      | some i =>
          cases b with
          | true =>
              by_cases hi : i.val + 1 < ci.size
              · have hp :
                    copyPrefix ci xs (some ⟨i.val + 1, by omega⟩) =
                      copyPrefix ci xs (some i) ++ [true] := by
                  simp [copyPrefix, pendingPrefix, List.replicate_add, List.append_assoc]
                have hw' : w = copyPrefix ci xs (some ⟨i.val + 1, by omega⟩) ++ bits := by
                  simpa [hp, List.append_assoc] using hw
                have h' : (copyPrefix ci xs (some ⟨i.val + 1, by omega⟩)).length ≤ w.length := by
                  simp [hw']
                change Parsed M ci co w xs
                  (if i.val + 1 < ci.size then ci.decodeFrom (some (i.val + 1)) bits else none)
                  ((machine M ci co).runFrom (copyCfg M ci co w xs (some i) h)
                    (bits.length + 1 + 1))
                rw [ite_eq_left hi, run_succ_first, copy_true M ci co xs i bits hw hi h h']
                exact ih xs (some ⟨i.val + 1, by omega⟩) hw' h'
              · change Parsed M ci co w xs
                  (if i.val + 1 < ci.size then ci.decodeFrom (some (i.val + 1)) bits else none)
                  ((machine M ci co).runFrom (copyCfg M ci co w xs (some i) h)
                    (bits.length + 1 + 1))
                rw [ite_eq_right hi]
                apply run_rejected
                rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty (some i)) rfl]
                simp only [machine, hin, List.head?_cons]
                simp [hi, pause, Turing.Action.apply, copyCfg]
          | false =>
              by_cases hi : i.val < ci.size
              · let a := ci.index.symm ⟨i.val, hi⟩
                have hw' : w = copyPrefix ci (xs ++ [a]) none ++ bits := by
                  simpa [a, copy_close_prefix ci xs i hi, List.append_assoc] using hw
                have h' : (copyPrefix ci (xs ++ [a]) none).length ≤ w.length := by simp [hw']
                change Parsed M ci co w xs
                  (if hi : i.val < ci.size then
                    (ci.decodeFrom none bits).map (ci.index.symm ⟨i.val, hi⟩ :: ·) else none)
                  ((machine M ci co).runFrom (copyCfg M ci co w xs (some i) h)
                    (bits.length + 1 + 1))
                rw [dite_eq_left hi, run_succ_first, copy_close M ci co xs i bits hw hi h h']
                exact (parsed_cons M ci co xs a _ _).mp (ih (xs ++ [a]) none hw' h')
              · change Parsed M ci co w xs
                  (if hi : i.val < ci.size then
                    (ci.decodeFrom none bits).map (ci.index.symm ⟨i.val, hi⟩ :: ·) else none)
                  ((machine M ci co).runFrom (copyCfg M ci co w xs (some i) h)
                    (bits.length + 1 + 1))
                rw [dite_eq_right hi]
                apply run_rejected
                rw [Turing.MultiTapeTM.step_apply_of_state (q := .copy xs.isEmpty (some i)) rfl]
                simp only [machine, hin, List.head?_cons]
                simp [hi, pause, Turing.Action.apply, copyCfg]

lemma copy_encoded (xs : List Input) :
    (machine M ci co).runFrom ((machine M ci co).initCfg (ci.encode xs))
      ((ci.encode xs).length + 1) = endCfg M ci co (ci.encode xs) xs := by
  have h := run_copy_decode M ci co (ci.encode xs) (ci.encode xs) [] none
    (by simp [copyPrefix, pendingPrefix, encode]) (by simp [copyPrefix, pendingPrefix, encode])
  have hd : ci.decodeFrom none (ci.encode xs) = some xs := decode_encode_proof ci xs
  simpa only [Option.map_none, hd, Parsed,
    List.nil_append, copyCfg_zero] using h

lemma copy_invalid (w : List Bool) (hw : ci.decode w = none) :
    ((machine M ci co).runFrom ((machine M ci co).initCfg w) (w.length + 1)).state = none ∧
      ((machine M ci co).runFrom ((machine M ci co).initCfg w) (w.length + 1)).output = [] := by
  have h := run_copy_decode M ci co w w [] none
    (by simp [copyPrefix, pendingPrefix, encode]) (by simp [copyPrefix, pendingPrefix, encode])
  have hd : ci.decodeFrom none w = none := hw
  simpa only [Option.map_none, hd, Parsed, copyCfg_zero] using h

end Complexity.MathlibTM0.AlphabetMachine

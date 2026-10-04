/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Model
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Internal

/-!
# Reconstruction from Boolean primary-input messages

The receiver reconstructs the actual circuit in topological order. The proof uses
only the partial parity or conjunction at each gate and the complementary inputs.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Capacity (selected)

variable {n g : ℕ}

/-- A message depends only on selected primary wire values. -/
theorem lineSummary_eq_of_selected_agree (line : Line signature n g)
    (U : Finset (Fin n)) (x y : Wire n g → Bool)
    (h : ∀ w, selected U w → x w = y w) : lineSummary line U x = lineSummary line U y := by
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient =>
    apply congrArg xorSum
    funext i
    by_cases hi : selected U (wires i) <;> simp [hi, h]
  | conjunction r polarity negated =>
    simp only [lineSummary, conjunctionSummary]
    congr 1
    apply propext
    constructor <;> intro hx i hi
    · rw [← h _ hi]
      exact hx i hi
    · rw [h _ hi]
      exact hx i hi

/-- Partial summaries and the other wire values determine each gate's output. -/
theorem line_eval_eq_of_summary_eq (line : Line signature n g)
    (U : Finset (Fin n)) (x y : Wire n g → Bool)
    (hs : lineSummary line U x = lineSummary line U y)
    (h : ∀ w, ¬ selected U w → x w = y w) :
    interpretation line.op (x ∘ line.wires) = interpretation line.op (y ∘ line.wires) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | affine r bias coefficient =>
    have split (z : Wire n g → Bool) :
        xorSum (fun i => coefficient i && z (wires i)) =
          (xorSum (fun i => if selected U (wires i) then coefficient i && z (wires i)
            else false) ^^
          xorSum (fun i => if selected U (wires i) then false
            else coefficient i && z (wires i))) := by
      rw [← xorSum_xor]
      congr 1
      funext i
      by_cases hi : selected U (wires i) <;> simp [hi]
    simp only [lineSummary] at hs
    simp only [interpretation, Function.comp_apply, split, hs]
    congr 2
    apply congrArg xorSum
    funext i
    by_cases hi : selected U (wires i) <;> simp [hi, h]
  | conjunction r polarity negated =>
    have selected_eq : (∀ i, selected U (wires i) → x (wires i) = polarity i) ↔
        (∀ i, selected U (wires i) → y (wires i) = polarity i) := by
      simpa only [lineSummary, conjunctionSummary, decide_eq_decide] using hs
    simp only [interpretation, conjunctionValue, Function.comp_apply]
    congr 2
    apply propext
    constructor <;> intro hx i
    · by_cases hi : selected U (wires i)
      · exact selected_eq.mp (fun j _ => hx j) i hi
      · rw [← h _ hi]
        exact hx i
    · by_cases hi : selected U (wires i)
      · exact selected_eq.mpr (fun j _ => hx j) i hi
      · rw [h _ hi]
        exact hx i

/-- The gate valuation is irrelevant to primary-input summaries. -/
theorem lineSummary_elim (line : Line signature n g) (U : Finset (Fin n))
    (input : Fin n → Bool) (gates : Fin g → Bool) :
    lineSummary line U (Wire.elim input gates) =
      lineSummary line U (Wire.elim input (fun _ => false)) := by
  apply lineSummary_eq_of_selected_agree
  intro wire hw
  cases wire with
  | input => rfl
  | gate => exact hw.elim

/-- The whole gate message is determined by selected primary inputs. -/
theorem key_eq_of_inputs_agree (p : Program signature n g) (U : Finset (Fin n))
    (x y : Fin n → Bool) (h : ∀ i ∈ U, x i = y i) : key p U x = key p U y := by
  funext gate
  apply lineSummary_eq_of_selected_agree
  intro wire hw
  cases wire with
  | input i => exact h i hw
  | gate => exact hw.elim

/-- Equal messages and equal complementary inputs give identical gate traces. -/
theorem eval_eq_of_key_eq (p : Program signature n g) (U : Finset (Fin n))
    (x y : Fin n → Bool) (hk : key p U x = key p U y)
    (h : ∀ i, i ∉ U → x i = y i) :
    p.eval interpretation x = p.eval interpretation y := by
  apply Program.eq_eval_of_forall_lines_eval
  intro gate
  calc
    _ = (p.lines gate).eval interpretation x (p.eval interpretation x) := by
      apply line_eval_eq_of_summary_eq (p.lines gate) U
      · simpa only [key, lineSummary_elim] using (congrFun hk gate).symm
      · intro wire hw
        cases wire with
        | input i => exact (h i hw).symm
        | gate => rfl
    _ = _ := Program.lines_eval p interpretation x gate

/-- Include the optional output bit without reading complementary inputs. -/
theorem outputKey_eq_of_inputs_agree (p : Program signature n g) (U : Finset (Fin n))
    (out : Wire n g) (x y : Fin n → Bool) (h : ∀ i ∈ U, x i = y i) :
    outputKey p U out x = outputKey p U out y := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [outputKey, Fin.lastCases_last]
    split
    · next hs => cases out with
      | input i => exact h i hs
      | gate => exact hs.elim
    · rfl
  · simpa only [outputKey, Fin.lastCases_castSucc] using
      congrFun (key_eq_of_inputs_agree p U x y h) i

/-- The complete output is determined by the Boolean message and complementary inputs. -/
theorem trace_eq_of_outputKey_eq (p : Program signature n g) (U : Finset (Fin n))
    (out : Wire n g) (x y : Fin n → Bool) (hk : outputKey p U out x = outputKey p U out y)
    (h : ∀ i, i ∉ U → x i = y i) :
    p.trace interpretation x out = p.trace interpretation y out := by
  have keys : key p U x = key p U y := by
    funext i
    simpa only [outputKey, Fin.lastCases_castSucc] using congrFun hk i.castSucc
  cases out with
  | gate j => exact congrFun (eval_eq_of_key_eq p U x y keys h) j
  | input i =>
    by_cases hi : i ∈ U
    · simpa only [outputKey, Fin.lastCases_last, selected, hi, ↓reduceIte, Wire.elim,
        Program.trace] using
        congrFun hk (Fin.last g)
    · exact h i hi

end Algebraic.Aggregate.Geometry

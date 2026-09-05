/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KeyedMinimumTournament.Family.Defs
public import Complexitylib.Circuits.Composition

/-!
# Parallel keyed-record circuit families -- proof internals
-/


public section

namespace Complexity

namespace Circuit

theorem eval_parallelKeyedRecordFamily_internal
    {B : Basis} {inputWidth keyWidth payloadWidth : ℕ}
    [NeZero inputWidth] [NeZero keyWidth]
    (count : ℕ)
    (circuits : Fin (count + 1) →
      Σ internalGates,
        Circuit B inputWidth (keyWidth + payloadWidth) internalGates)
    (input : BitString inputWidth)
    (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth)
    (heval : ∀ index,
      (circuits index).2.eval input =
        Fin.append (keys index) (payloads index)) :
    (parallelKeyedRecordFamily count circuits).2.eval input =
      BitString.packKeyedRecords count keys payloads := by
  induction count with
  | zero =>
      simp only [parallelKeyedRecordFamily, BitString.packKeyedRecords]
      exact heval 0
  | succ count ih =>
      simp only [parallelKeyedRecordFamily, BitString.packKeyedRecords]
      have hparallel := Circuit.eval_parallel
        (parallelKeyedRecordFamily count
          (fun index => circuits index.castSucc)).2
        (circuits (Fin.last (count + 1))).2 input
      refine hparallel.trans (congrArg₂ Fin.append ?_ ?_)
      · exact ih
          (fun index => circuits index.castSucc)
          (fun index => keys index.castSucc)
          (fun index => payloads index.castSucc)
          (fun index => heval index.castSucc)
      · exact heval (Fin.last (count + 1))

theorem size_parallelKeyedRecordFamily_internal
    {B : Basis} {inputWidth keyWidth payloadWidth : ℕ}
    [NeZero inputWidth] [NeZero keyWidth]
    (count : ℕ)
    (circuits : Fin (count + 1) →
      Σ internalGates,
        Circuit B inputWidth (keyWidth + payloadWidth) internalGates) :
    (parallelKeyedRecordFamily count circuits).2.size =
      ∑ index, (circuits index).2.size := by
  induction count with
  | zero =>
      simp [parallelKeyedRecordFamily]
      rfl
  | succ count ih =>
      simp only [parallelKeyedRecordFamily]
      have hparallel := Circuit.size_parallel
        (parallelKeyedRecordFamily count
          (fun index => circuits index.castSucc)).2
        (circuits (Fin.last (count + 1))).2
      calc
        ((parallelKeyedRecordFamily count
              (fun index => circuits index.castSucc)).2.parallel
            (circuits (Fin.last (count + 1))).2).size =
            (parallelKeyedRecordFamily count
              (fun index => circuits index.castSucc)).2.size +
              (circuits (Fin.last (count + 1))).2.size := hparallel
        _ = (∑ index : Fin (count + 1),
              (circuits index.castSucc).2.size) +
              (circuits (Fin.last (count + 1))).2.size := by
          rw [ih (fun index => circuits index.castSucc)]
        _ = ∑ index, (circuits index).2.size :=
          (Fin.sum_univ_castSucc
            (fun index : Fin (count + 1 + 1) =>
              (circuits index).2.size)).symm

end Circuit

end Complexity

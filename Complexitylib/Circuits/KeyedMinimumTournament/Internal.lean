/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KeyedMinimumTournament.Defs

/-!
# Keyed minimum tournaments -- proof internals
-/


public section

namespace Complexity

namespace BitString

theorem keyedTournamentInputWidth_eq_internal (count recordWidth : ℕ) :
    keyedTournamentInputWidth count recordWidth = (count + 1) * recordWidth := by
  induction count with
  | zero => simp [keyedTournamentInputWidth]
  | succ count ih =>
      rw [keyedTournamentInputWidth, ih]
      ring

theorem exists_unsignedMinimumKeyedRecord_eq_internal
    {keyWidth payloadWidth : ℕ} (count : ℕ)
    (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth) :
    ∃ index,
      unsignedMinimumKeyedRecord count keys payloads =
        (keys index, payloads index) := by
  induction count with
  | zero =>
      exact ⟨0, rfl⟩
  | succ count ih =>
      unfold unsignedMinimumKeyedRecord
      dsimp only
      split_ifs
      · obtain ⟨index, hindex⟩ := ih
          (fun prior => keys prior.castSucc)
          (fun prior => payloads prior.castSucc)
        exact ⟨index.castSucc, hindex⟩
      · exact ⟨Fin.last (count + 1), rfl⟩

theorem unsignedMinimumKeyedRecord_key_le_internal
    {keyWidth payloadWidth : ℕ} (count : ℕ)
    (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth)
    (index : Fin (count + 1)) :
    (unsignedMinimumKeyedRecord count keys payloads).1.unsignedValue ≤
      (keys index).unsignedValue := by
  induction count with
  | zero =>
      have hindex : index = 0 := by
        apply Fin.ext
        omega
      subst index
      simp [unsignedMinimumKeyedRecord]
  | succ count ih =>
      unfold unsignedMinimumKeyedRecord
      dsimp only
      split_ifs with hminimum
      · refine Fin.lastCases ?_ (fun prior => ?_) index
        · exact hminimum
        · exact ih
            (fun prior => keys prior.castSucc)
            (fun prior => payloads prior.castSucc) prior
      · have hlast :
            (keys (Fin.last (count + 1))).unsignedValue ≤
              (unsignedMinimumKeyedRecord count
                (fun prior => keys prior.castSucc)
                (fun prior => payloads prior.castSucc)).1.unsignedValue :=
          (Nat.lt_of_not_ge hminimum).le
        refine Fin.lastCases ?_ (fun prior => ?_) index
        · exact le_rfl
        · exact hlast.trans (ih
            (fun prior => keys prior.castSucc)
            (fun prior => payloads prior.castSucc) prior)

end BitString

namespace Circuit

theorem eval_unsignedKeyedMinTournament_internal
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth]
    (count : ℕ) (keys : Fin (count + 1) → BitString keyWidth)
    (payloads : Fin (count + 1) → BitString payloadWidth) :
    (unsignedKeyedMinTournament keyWidth payloadWidth count).2.eval
        (BitString.packKeyedRecords count keys payloads) =
      let winner :=
        BitString.unsignedMinimumKeyedRecord count keys payloads
      Fin.append winner.1 winner.2 := by
  induction count with
  | zero =>
      simp only [unsignedKeyedMinTournament, BitString.packKeyedRecords,
        BitString.unsignedMinimumKeyedRecord]
      erw [Circuit.eval_projectInputs_internal]
      rfl
  | succ count ih =>
      simp only [unsignedKeyedMinTournament, BitString.packKeyedRecords,
        BitString.unsignedMinimumKeyedRecord]
      erw [Circuit.eval_compose]
      have hparallel := Circuit.eval_parallel
        ((unsignedKeyedMinTournament keyWidth payloadWidth count).2.reindexInputs
          (Fin.castAdd (keyWidth + payloadWidth)))
        (projectInputs
          (Fin.natAdd (BitString.keyedTournamentInputWidth count
            (keyWidth + payloadWidth))))
        (Fin.append
          (BitString.packKeyedRecords count
            (fun index => keys index.castSucc)
            (fun index => payloads index.castSucc))
          (Fin.append (keys (Fin.last (count + 1)))
            (payloads (Fin.last (count + 1)))))
      have hprefix :
          ((unsignedKeyedMinTournament keyWidth payloadWidth count).2.reindexInputs
              (Fin.castAdd (keyWidth + payloadWidth))).eval
            (Fin.append
              (BitString.packKeyedRecords count
                (fun index => keys index.castSucc)
                (fun index => payloads index.castSucc))
              (Fin.append (keys (Fin.last (count + 1)))
                (payloads (Fin.last (count + 1))))) =
            let winner := BitString.unsignedMinimumKeyedRecord count
              (fun index => keys index.castSucc)
              (fun index => payloads index.castSucc)
            Fin.append winner.1 winner.2 := by
        rw [Circuit.eval_reindexInputs]
        have hinput :
            (Fin.append
                (BitString.packKeyedRecords count
                  (fun index => keys index.castSucc)
                  (fun index => payloads index.castSucc))
                (Fin.append (keys (Fin.last (count + 1)))
                  (payloads (Fin.last (count + 1))))) ∘
                Fin.castAdd (keyWidth + payloadWidth) =
              BitString.packKeyedRecords count
                (fun index => keys index.castSucc)
                (fun index => payloads index.castSucc) := by
          funext input
          simp
        rw [hinput]
        exact ih _ _
      have hlast :
          (projectInputs
              (Fin.natAdd (BitString.keyedTournamentInputWidth count
                (keyWidth + payloadWidth)))).eval
            (Fin.append
              (BitString.packKeyedRecords count
                (fun index => keys index.castSucc)
                (fun index => payloads index.castSucc))
              (Fin.append (keys (Fin.last (count + 1)))
                (payloads (Fin.last (count + 1))))) =
            Fin.append (keys (Fin.last (count + 1)))
              (payloads (Fin.last (count + 1))) := by
        rw [Circuit.eval_projectInputs]
        funext input
        simp
      have hcandidates := hparallel.trans (congrArg₂ Fin.append hprefix hlast)
      refine
        (congrArg (unsignedKeyedMin keyWidth payloadWidth).eval
          hcandidates).trans ?_
      let winner := BitString.unsignedMinimumKeyedRecord count
        (fun index => keys index.castSucc)
        (fun index => payloads index.castSucc)
      let lastKey := keys (Fin.last (count + 1))
      let lastPayload := payloads (Fin.last (count + 1))
      change (unsignedKeyedMin keyWidth payloadWidth).eval
          (BitString.keyedMinimumInput
            winner.1 winner.2 lastKey lastPayload) =
        Fin.append
          (if winner.1.unsignedValue ≤ lastKey.unsignedValue then
            winner else (lastKey, lastPayload)).1
          (if winner.1.unsignedValue ≤ lastKey.unsignedValue then
            winner else (lastKey, lastPayload)).2
      rw [Circuit.eval_unsignedKeyedMin]
      unfold BitString.unsignedKeyedMin
      split_ifs <;> rfl

theorem size_unsignedKeyedMinTournament_internal
    (keyWidth payloadWidth : ℕ) [NeZero keyWidth] (count : ℕ) :
    (unsignedKeyedMinTournament keyWidth payloadWidth count).2.size =
      (count + 1) * (keyWidth + payloadWidth) +
        count * (20 * keyWidth + 5 * payloadWidth + 1) := by
  induction count with
  | zero =>
      simp only [unsignedKeyedMinTournament]
      erw [Circuit.size_projectInputs]
      omega
  | succ count ih =>
      simp only [unsignedKeyedMinTournament]
      erw [Circuit.size_compose]
      have hparallel := Circuit.size_parallel
        ((unsignedKeyedMinTournament keyWidth payloadWidth count).2.reindexInputs
          (Fin.castAdd (keyWidth + payloadWidth)))
        (projectInputs
          (Fin.natAdd (BitString.keyedTournamentInputWidth count
            (keyWidth + payloadWidth))))
      refine
        (congrArg
          (fun size => size + (unsignedKeyedMin keyWidth payloadWidth).size)
          hparallel).trans ?_
      have hprefix := Circuit.size_reindexInputs
        (unsignedKeyedMinTournament keyWidth payloadWidth count).2
        (Fin.castAdd (keyWidth + payloadWidth))
      have hlast := Circuit.size_projectInputs
        (N := BitString.keyedTournamentInputWidth count
          (keyWidth + payloadWidth) + (keyWidth + payloadWidth))
        (M := keyWidth + payloadWidth)
        (Fin.natAdd (BitString.keyedTournamentInputWidth count
          (keyWidth + payloadWidth)))
      have hselector := Circuit.size_unsignedKeyedMin keyWidth payloadWidth
      calc
        (((unsignedKeyedMinTournament keyWidth payloadWidth count).2.reindexInputs
              (Fin.castAdd (keyWidth + payloadWidth))).size +
            (projectInputs
              (Fin.natAdd (BitString.keyedTournamentInputWidth count
                (keyWidth + payloadWidth)))).size) +
            (unsignedKeyedMin keyWidth payloadWidth).size =
            ((unsignedKeyedMinTournament keyWidth payloadWidth count).2.size +
              (keyWidth + payloadWidth)) +
              (20 * keyWidth + 5 * payloadWidth + 1) :=
          congrArg₂ Nat.add (congrArg₂ Nat.add hprefix hlast) hselector
        _ = (count + 1 + 1) * (keyWidth + payloadWidth) +
              (count + 1) * (20 * keyWidth + 5 * payloadWidth + 1) := by
          rw [ih]
          ring

end Circuit

end Complexity

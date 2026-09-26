/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.BinCounter
public import Complexitylib.Classes.PCP.Internal.SubsetNP

/-!
# Coin strings from their index

A loop over the coin strings of a verifier receives its index in unary, since
that is the form a polynomial-time loop counter takes. `BinCounter` turns such an
index into a fixed-width binary counter; this module identifies that counter
with the coin string `SubsetNP` names, and relates counting coin strings to
counting their indices.

## Main definitions

- `Complexity.coinEquiv` — coin strings and their indices are in bijection

## Main results

- `Complexity.toList_coinOfIndex` — the counter is the coin string `SubsetNP` names
- `Complexity.binValLE_toList` — the value of a coin string is its index
- `Complexity.card_filter_coinIndex` — counting coin strings is counting indices
-/

@[expose] public section

namespace Complexity

/-- **The counter is the coin string.** `SubsetNP` indexes coin strings by their
little-endian binary value, which is exactly what the counter holds. -/
theorem toList_coinOfIndex (t c : ℕ) (h : c < 2 ^ t) :
    BitString.toList (PCPVerifier.coinOfIndex (t := t) ⟨c, h⟩) = bitsOfLenLE t c := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have hj : j < t := by simpa using h1
  rw [bitsOfLenLE_getElem t c j hj,
    BitString.getElem_toList (PCPVerifier.coinOfIndex (t := t) ⟨c, h⟩) ⟨j, hj⟩,
    PCPVerifier.coinOfIndex]
  have hval := finFunctionFinEquiv_symm_apply_val (⟨c, h⟩ : Fin (2 ^ t)) (⟨j, hj⟩ : Fin t)
  have h2 : (finFunctionFinEquiv.symm (⟨c, h⟩ : Fin (2 ^ t)) ⟨j, hj⟩ = 1)
      ↔ (c / 2 ^ j % 2 = 1) := by
    rw [Fin.ext_iff, hval]
    exact Iff.rfl
  exact decide_eq_decide.mpr h2

/-- The index of the coin string an index names. -/
theorem coinIndex_coinOfIndex {t : ℕ} (c : Fin (2 ^ t)) :
    PCPVerifier.coinIndex (PCPVerifier.coinOfIndex c) = c.val := by
  have hd : PCPVerifier.coinDigits (PCPVerifier.coinOfIndex c)
      = finFunctionFinEquiv.symm c := by
    funext i
    rw [PCPVerifier.coinDigits, PCPVerifier.coinOfIndex]
    have hv : (finFunctionFinEquiv.symm c i).val = 0
        ∨ (finFunctionFinEquiv.symm c i).val = 1 := by omega
    rcases hv with hv | hv
    · have h0 : finFunctionFinEquiv.symm c i = 0 := Fin.ext hv
      simp [h0]
    · have h1 : finFunctionFinEquiv.symm c i = 1 := Fin.ext hv
      simp [h1]
  rw [PCPVerifier.coinIndex, hd, Equiv.apply_symm_apply]

/-- **The value of a coin string is its index.** -/
theorem binValLE_toList {T : ℕ} (ρ : Fin T → Bool) :
    binValLE (BitString.toList ρ) = PCPVerifier.coinIndex ρ := by
  have hlt : PCPVerifier.coinIndex ρ < 2 ^ T := PCPVerifier.coinIndex_lt ρ
  have hρ : BitString.toList ρ = bitsOfLenLE T (PCPVerifier.coinIndex ρ) := by
    rw [← PCPVerifier.coinOfIndex_coinIndex ρ hlt, toList_coinOfIndex]
    congr 1
    rw [PCPVerifier.coinOfIndex_coinIndex ρ hlt]
  rw [hρ, binValLE_bitsOfLenLE _ _ hlt]

/-- Coin strings and their indices are in bijection. -/
noncomputable def coinEquiv (T : ℕ) : Fin (2 ^ T) ≃ (Fin T → Bool) where
  toFun := PCPVerifier.coinOfIndex
  invFun := fun ρ => ⟨PCPVerifier.coinIndex ρ, PCPVerifier.coinIndex_lt ρ⟩
  left_inv := fun c => Fin.ext (coinIndex_coinOfIndex c)
  right_inv := fun ρ => PCPVerifier.coinOfIndex_coinIndex ρ (PCPVerifier.coinIndex_lt ρ)

/-- **Counting coin strings is counting indices.** -/
theorem card_filter_coinIndex (T : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun ρ : Fin T → Bool => Q (PCPVerifier.coinIndex ρ))).card
      = ((Finset.range (2 ^ T)).filter Q).card := by
  classical
  refine Finset.card_bij (fun ρ _ => PCPVerifier.coinIndex ρ) ?_ ?_ ?_
  · intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (PCPVerifier.coinIndex_lt ρ), hρ⟩
  · intro ρ₁ h₁ ρ₂ h₂ heq
    exact PCPVerifier.coinIndex_injective heq
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_range] at hc
    refine ⟨PCPVerifier.coinOfIndex ⟨c, hc.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [coinIndex_coinOfIndex]
      exact hc.2
    · exact coinIndex_coinOfIndex ⟨c, hc.1⟩

end Complexity

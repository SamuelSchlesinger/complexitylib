/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Logic.Function.Basic

/-!
# Representing tape symbols by binary tracks

Each nonblank symbol has its own marked track. The blank symbol is represented
by blank cells on every track. The decoding function is exact on these encodings.
-/

@[expose] public section

namespace Complexity.SymbolTracks

/-- One track per source symbol; the blank symbol leaves every track blank. -/
noncomputable def encode {Γ : Type*} [Inhabited Γ] (a b : Γ) : Option Bool := by
  classical
  exact if a ≠ default ∧ b = a then some true else none

/-- Decode a vector of tracks, inverse to the symbol encoding. -/
noncomputable def decode {Γ : Type*} [Inhabited Γ] (v : Γ → Option Bool) : Γ :=
  Function.invFun encode v

/-- Distinct source symbols have distinct vectors of tracks. -/
theorem encode_injective {Γ : Type*} [Inhabited Γ] :
    Function.Injective (encode (Γ := Γ)) := by
  intro a b h
  by_cases ha : a = default
  · by_cases hb : b = default
    · exact ha.trans hb.symm
    · have he := congrFun h b
      simp [encode, ha, hb] at he
  · have he := congrFun h a
    have hb : b ≠ default ∧ a = b := by
      simpa [encode, ha] using he.symm
    exact hb.2

/-- Decoding recovers every encoded source symbol. -/
theorem decode_encode {Γ : Type*} [Inhabited Γ] (a : Γ) : decode (encode a) = a :=
  Function.leftInverse_invFun encode_injective a

/-- A blank source cell is blank on every track. -/
theorem encode_default {Γ : Type*} [Inhabited Γ] :
    encode (default : Γ) = fun _ => none := by
  funext b
  simp [encode]

end Complexity.SymbolTracks

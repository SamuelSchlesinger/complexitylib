/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2

/-!
# Public stack-compiler API regression checks

The public import alone supplies the Mathlib-certificate bridge. The identity
example uses one fixed compiled machine for all words, including the empty word.
Concrete tape examples make the bottom marker and reversed stack order visible.
-/

namespace Complexity.TM2ApiCheck

open Turing MathlibTM2

example : TM2to1.trInit (Γ := fun _ : Unit => Bool) () [] = [(true, fun _ => none)] := rfl

example : TM2to1.trInit (Γ := fun _ : Unit => Bool) () [true, false] =
    [(true, fun _ => some false), (false, fun _ => some true)] := by
  change [(true, Function.update (fun _ : Unit => none) () (some false)),
    (false, Function.update (fun _ : Unit => none) () (some true))] = _
  congr 2

example :
    ∃ (m : ℕ)
      (G : TM0.Machine (TM2to1.Γ' (idComputer Bool).K (idComputer Bool).Γ) (Fin (m + 1)))
      (C : ℕ), 0 < C ∧ ∀ w : List Bool,
        ∃ t ≤ C * (w.length + 2) ^ 2, ∃ c,
          exec (TM0.step G) t (TM0.init (TM2to1.trInit (idComputer Bool).k₀ w)) = some c ∧
          TM0.step G c = none ∧
          c.Tape = Tape.mk₁ (TM2to1.trInit (idComputer Bool).k₁ w) := by
  obtain ⟨m, G, C, hC, hG⟩ := exists_tm0_computer (idComputer Bool)
  refine ⟨m, G, C, hC, ?_⟩
  intro w
  have h : TM2OutputsInTime (idComputer Bool) w (some w) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  obtain ⟨u, hu, c, hc, hh, ho⟩ := hG w w 1 h
  dsimp only [idComputer] at hu
  have htime : w.length + 1 + 1 = w.length + 2 := by omega
  rw [htime] at hu
  exact ⟨u, hu, c, hc, hh, ho⟩

-- The higher-level bridge also accepts a typed problem with a binary encoding.
example := exists_tm0_polynomial_computer
  (idComputableInPolyTime (α := ℕ) Computability.encodeNat)

end Complexity.TM2ApiCheck

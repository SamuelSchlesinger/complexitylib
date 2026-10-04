/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit.Count

/-!
# One-way summaries of whole aggregate circuits

The primary-input summary reconstructs every gate output. One additional bit
handles a designated output that is itself a selected primary input.
-/

@[expose] public section

namespace Algebraic.Aggregate.Capacity

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- A summary with a spare bit for a designated primary-input output. -/
abbrev OutputKey (p : Program (signature State) n g) := Key p × Bool

/-- Summarize selected primary inputs, including a selected primary output if present. -/
def outputKey [∀ j, CommMonoid (State j)] (p : Program (signature State) n g)
    (U : Finset (Fin n)) (out : Wire n g) (input : Fin n → Bool) : OutputKey p :=
  (key p U input, if selected U out then Wire.elim input (fun _ => false) out else false)

/-- The output summary is determined by the sending party's primary inputs. -/
theorem outputKey_eq_of_inputs_agree [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (U : Finset (Fin n)) (out : Wire n g)
    (x y : Fin n → Bool) (h : ∀ i ∈ U, x i = y i) :
    outputKey p U out x = outputKey p U out y := by
  apply Prod.ext (key_eq_of_inputs_agree p U x y h)
  dsimp only [outputKey]
  split
  · next hs =>
      cases out with
      | input i => exact h i hs
      | gate => exact hs.elim
  · rfl

/-- Equal output summaries determine the output for every fixed complementary input. -/
theorem trace_eq_of_outputKey_eq [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (U : Finset (Fin n)) (out : Wire n g)
    (x y : Fin n → Bool) (hk : outputKey p U out x = outputKey p U out y)
    (h : ∀ i, i ∉ U → x i = y i) :
    p.trace interpretation x out = p.trace interpretation y out := by
  by_cases hs : selected U out
  · have he := congrArg Prod.snd hk
    simp only [outputKey, hs, ↓reduceIte] at he
    cases out with
    | input => exact he
    | gate => exact hs.elim
  · exact trace_eq_of_key_eq p U x y (congrArg Prod.fst hk) h out hs

/-- The designated output costs at most one extra bit. -/
theorem card_outputKey_le [∀ j, Fintype (State j)] (p : Program (signature State) n g) :
    Fintype.card (OutputKey p) ≤ 2 ^ (capacity p + 1) := by
  rw [Fintype.card_prod, Fintype.card_bool, Nat.pow_succ]
  exact Nat.mul_le_mul_right 2 (card_key_le p)

end Algebraic.Aggregate.Capacity

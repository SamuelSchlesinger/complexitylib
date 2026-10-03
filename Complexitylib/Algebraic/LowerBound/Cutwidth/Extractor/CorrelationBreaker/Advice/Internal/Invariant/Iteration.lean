/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Step
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Iteration.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Ring

/-!
# The invariant for the complete actual advice fold

Induction from the last processed bit composes the checked one-bit transition
with the actual program's append law. At every prefix the witness retains
the original source law and pointwise program identities. Unequal paired
advice enters the separated phase, with the tampered final state fixed by
the resulting transcript. The numerical recurrence records every error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

private theorem envelope_succ (D α : ℝ) (c i : Nat) :
    D ^ c * (D ^ (c * i) * α) = D ^ (c * (i + 1)) * α := by
  rw [Nat.mul_add, Nat.mul_one, pow_add]
  ring

theorem AdviceInvariant.iterate {n m L : Nat} {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : (Z × B) × A → ℝ} {x : Z → A → Fin n → Bool} {y : Z → B → Fin m → Bool}
    {honest tampered : (Z × B) × A → Fin (matchedBlockOutputBits 64 L) → Bool}
    {separated : Prop} {ρ α β : ℝ}
    (I : AdviceInvariant n m L p x y honest tampered separated ρ α β)
    (e : Nat) (guard : FlipFlopSizeGuard n m L e)
    (x' : Z → A → Fin n → Bool) (y' : Z → B → Fin m → Bool)
    (pairs : List (Bool × Bool)) :
    Nonempty (AdviceInvariant n m L p x y
      (fun z => adviceFold n m L e (x z.1.1 z.2) (y z.1.1 z.1.2)
        (honest z) (pairs.map Prod.fst))
      (fun z => adviceFold n m L e (x' z.1.1 z.2) (y' z.1.1 z.1.2)
        (tampered z) (pairs.map Prod.snd))
      (separated ∨ pairs.map Prod.fst ≠ pairs.map Prod.snd)
      (adviceChainError L e ρ α β pairs.length)
      ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ (8 * pairs.length) * α)
      ((Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ (5 * pairs.length) * β)) := by
  induction pairs using List.reverseRecOn with
  | nil =>
      simpa only [List.map_nil, List.length_nil, adviceFold_nil, ne_self_iff_false, or_false,
        adviceChainError_zero, Nat.mul_zero, pow_zero, one_mul] using
        (show Nonempty (AdviceInvariant n m L p x y honest tampered separated ρ α β) from ⟨I⟩)
  | append_singleton pairs bits ih =>
      obtain ⟨J⟩ := ih
      have next := J.step e guard x' y' bits.1 bits.2
      simpa only [List.map_append, List.map_singleton, List.length_append, List.length_singleton,
        adviceFold_snoc, pairedAdvice_snoc_ne, or_assoc, adviceChainError_succ, envelope_succ]
        using next
end Algebraic.Cutwidth.Extractor.Internal

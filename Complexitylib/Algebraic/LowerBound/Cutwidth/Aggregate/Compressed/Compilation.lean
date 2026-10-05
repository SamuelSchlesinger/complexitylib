/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Observation
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compilation

/-!
# Compiling jointly compressed aggregate circuits

The existing ordinary wiring compiler is unchanged. Only the guessed states and
observations are compressed, so the original gate count and graph excess are retained.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Compressed

open scoped Classical
open MultiOutput MultiOutput.Internal WireGraph Algebraic.Aggregate
open Algebraic.Aggregate.Compressed

variable {J : Type} {State : J → Type}
  [∀ j, CommMonoid (State j)] {M : Type} [CommMonoid M] [Fintype M]
  {n g m : Nat}

private theorem card_accepting_le_sum {k : Nat} {ι : Type} [Fintype ι]
    (f : Cslib.BooleanFunction k) (fibre : ι → Cslib.BooleanFunction k)
    (cover : ∀ x, f x = true → ∃ a, fibre a x = true) :
    (accepting f).card ≤ ∑ a, (accepting (fibre a)).card := by
  have hsub : accepting f ⊆ Finset.univ.biUnion (fun a => accepting (fibre a)) := by
    intro x hx
    obtain ⟨a, ha⟩ := cover x (mem_accepting.mp hx)
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, mem_accepting.mpr ha⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le


/-- Summing exact guessed computations multiplies the component bound by at most
`2 ^ (compressed budget + 1)`. The one extra bit observes the designated output without an edge. -/
theorem card_restriction_le (p : Program (signature State) n g)
    (compression : Factorization p M) (out : Wire n g) (a₀ : Guess p)
    (K : MultiOutput.Internal.ClosedSet (erase p a₀))
    (e : Fin m ≃ ↥(SingleCut.inputsIn K.carrier)) (outside : Fin n → Bool)
    (hm : 2 ≤ m)
    (hconn : ∀ u ∈ K.carrier, ∀ v ∈ K.carrier,
      Relation.ReflTransGen (Linked (erase p a₀)) u v)
    {A η C : ℝ} (hAη : 0 ≤ A + η) (hC : 0 ≤ C)
    (order : Multigraph.OrderingBound A η C) {Krect : Nat} (hK : 1 < Krect)
    (hrect : RectangleFree (fun x => p.trace interpretation x out) Krect) :
    ((accepting (restriction (fun x => p.trace interpretation x out)
      (SingleCut.inputsIn K.carrier) e.symm outside)).card : ℝ) ≤
      (((n : ℝ) + 3 * g) * (2 : ℝ) ^ ((A + η) * max ((g : ℝ) - m) 0 +
        3 * Real.logb 2 ((n : ℝ) + 3 * g) + C + 3) + 1) *
        (2 : ℝ) ^ (Compressed.budget M + 1) * Krect ^ 2 := by
  let U := SingleCut.inputsIn K.carrier
  let input := subcubeInput U e.symm outside
  let F := restriction (fun x => p.trace interpretation x out) U e.symm outside
  let Ka (a : M) := transportClosedSet p a₀ (compression.guess a) K
  let fa (a : M) := componentFunction (Ka a) ordinaryInterpretation
    (fun w value => compression.observe out w.1 value)
    (compression.ComponentAccept a K.carrier out outside)
    e outside
  have hsem (a : M) (x : Fin m → Bool) :
      fa a x = true ↔ compression.AcceptsGuess a out (input x) := by
    change decide (compression.ComponentAccept a K.carrier out outside
      (∏ w : Signal (Ka a), compression.observe out w.1
        ((erase p (compression.guess a)).trace ordinaryInterpretation (input x) w.1))) = true ↔ _
    rw [decide_eq_true_iff]
    exact compression.componentAccept_iff a (Ka a) out outside (input x) (by
      intro j hj
      simp only [input, subcubeInput, Ka, transportClosedSet] at *
      simp [U, hj])
  have hsub (a : M) : ∀ x, fa a x = true → F x = true := by
    intro x hx
    exact ((compression.acceptsGuess_iff a out (input x)).mp ((hsem a x).mp hx)).2
  have hfree : RectangleFree F Krect := hrect.restriction U e.symm outside
  have hfreea (a : M) : RectangleFree (fa a) Krect := by
    intro S P Q hPQ
    exact hfree S P Q (fun x hx y hy => hsub a _ (hPQ x hx y hy))
  let B : ℝ := ((n : ℝ) + 3 * g) * (2 : ℝ) ^
    ((A + η) * max ((g : ℝ) - m) 0 +
      3 * Real.logb 2 ((n : ℝ) + 3 * g) + C + 3) + 1
  have hbound (a : M) :
      ((accepting (fa a)).card : ℝ) ≤ B * Fintype.card (Observation M) * Krect ^ 2 :=
    card_componentFunction_le (Ka a) ordinaryInterpretation
      (fun w value => compression.observe out w.1 value)
    (compression.ComponentAccept a K.carrier out outside)
      e outside (erase_fanInAtMost p (compression.guess a)) hm
      (connected_transportClosedSet p a₀ (compression.guess a) K hconn) hAη hC order hK (hfreea a)
  have hcover : (accepting F).card ≤ ∑ a, (accepting (fa a)).card := by
    apply card_accepting_le_sum F fa
    intro x hx
    refine ⟨compression.actual (input x), (hsem _ x).mpr ?_⟩
    exact (compression.acceptsGuess_iff _ out (input x)).mpr ⟨rfl, hx⟩
  have hstates : (Fintype.card M : ℝ) * Fintype.card (Observation M) ≤
      (2 : ℝ) ^ (Compressed.budget M + 1) := by
    exact_mod_cast Compressed.card_guess_mul_card_observation_le (M := M)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc ((accepting F).card : ℝ)
      ≤ ∑ a, ((accepting (fa a)).card : ℝ) := by exact_mod_cast hcover
    _ ≤ ∑ _a : M, B * Fintype.card (Observation M) * Krect ^ 2 :=
      Finset.sum_le_sum fun a _ => hbound a
    _ = B * ((Fintype.card M : ℝ) * Fintype.card (Observation M)) *
        Krect ^ 2 := by simp [Finset.sum_const]; ring
    _ ≤ B * (2 : ℝ) ^ (Compressed.budget M + 1) * Krect ^ 2 := by
      gcongr


end Algebraic.Cutwidth.Aggregate.Compressed

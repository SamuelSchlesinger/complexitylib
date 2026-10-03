/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Mathlib.Tactic.Ring

/-!
# Exact finite factorization after an observation

Multiplying an observation's marginal by its conditional row recovers the
original mass, including null rows. Deterministic maps retaining both
original side variables therefore give exact factored laws on the extended
transcript. Alternating observations compose these equalities.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem transcript_map_graph {A U : Type*} [Fintype A]
    (p : A → ℝ) (f : A → U) (u : U) (a : A) :
    mapWeight (fun a => (f a, a)) p (u, a) = if f a = u then p a else 0 := by
  simp only [mapWeight, Prod.mk.injEq]
  simp only [and_comm (a := _ = u), ite_and]
  simp

theorem transcript_graph_first {A U : Type*} [Fintype A]
    (p : A → ℝ) (f : A → U) :
    firstWeight (mapWeight (fun a => (f a, a)) p) = mapWeight f p := by
  funext u
  change (∑ a, mapWeight (fun a => (f a, a)) p (u, a)) = _
  simp_rw [transcript_map_graph]
  rfl

theorem observedTranscriptKernel_factor {Z A U : Type*} [Fintype A]
    (p : Z → A → ℝ) (f : Z → A → U)
    (nonnegative : ∀ z a, 0 ≤ p z a) (zu : Z × U) (a : A) :
    mapWeight (f zu.1) (p zu.1) zu.2 * observedTranscriptKernel p f zu a =
      if f zu.1 a = zu.2 then p zu.1 a else 0 := by
  have h := conditionalWeight_factor
    (mapWeight (fun a => (f zu.1 a, a)) (p zu.1))
    (fun ua => by
      rw [transcript_map_graph]
      split_ifs <;> first | exact nonnegative _ _ | exact le_rfl) zu.2 a
  simpa only [observedTranscriptKernel, transcript_graph_first, transcript_map_graph] using h

theorem observedTranscriptKernel_probability {Z A U : Type*} [Fintype A] [Fintype U]
    (p : Z → A → ℝ) (f : Z → A → U) (probability : ∀ z, IsProbabilityWeight (p z))
    (zu : Z × U) : IsProbabilityWeight (observedTranscriptKernel p f zu) := by
  obtain ⟨a, _⟩ := (probability zu.1).exists_pos
  let : Nonempty A := ⟨a⟩
  exact ((probability zu.1).map (fun a => (f zu.1 a, a))).conditionalWeight zu.2

theorem observedTranscriptWeight_mul_kernel {Z A U : Type*} [Fintype A]
    (w : Z → ℝ) (p : Z → A → ℝ) (f : Z → A → U)
    (nonnegative : ∀ z a, 0 ≤ p z a) (zu : Z × U) (a : A) :
    observedTranscriptWeight w p f zu * observedTranscriptKernel p f zu a =
      if f zu.1 a = zu.2 then w zu.1 * p zu.1 a else 0 := by
  rw [observedTranscriptWeight, mul_assoc,
    observedTranscriptKernel_factor p f nonnegative zu a]
  split_ifs <;> simp

theorem observedTranscriptKernel_eq_uniform {Z A U : Type*} [Fintype A]
    (p : Z → A → ℝ) (f : Z → A → U) (zu : Z × U)
    (zero : mapWeight (f zu.1) (p zu.1) zu.2 = 0) :
    observedTranscriptKernel p f zu = uniformWeight A := by
  funext a
  simp only [observedTranscriptKernel, conditionalWeight, transcript_graph_first, zero,
    ite_true]

theorem observedTranscriptWeight_probability {Z A U : Type*}
    [Fintype Z] [Fintype A] [Fintype U]
    (w : Z → ℝ) (p : Z → A → ℝ) (f : Z → A → U)
    (hw : IsProbabilityWeight w) (hp : ∀ z, IsProbabilityWeight (p z)) :
    IsProbabilityWeight (observedTranscriptWeight w p f) := by
  refine ⟨fun zu => mul_nonneg (hw.1 _) (((hp _).map (f _)).1 _), ?_⟩
  simp only [observedTranscriptWeight, Fintype.sum_prod_type, ← Finset.mul_sum,
    ((hp _).map (f _)).2, mul_one]
  exact hw.2

theorem factoredWeight_probability {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) : IsProbabilityWeight (factoredWeight w l r) := by
  refine ⟨fun p => mul_nonneg (mul_nonneg (hw.1 _) ((hr _).1 _)) ((hl _).1 _), ?_⟩
  simp only [factoredWeight, Fintype.sum_prod_type, ← Finset.mul_sum,
    (hl _).2, (hr _).2, mul_one]
  exact hw.2

theorem factoredWeight_observe_left {Z A B U : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (f : Z → A → U)
    (nonnegative : ∀ z a, 0 ≤ l z a) :
    mapWeight (fun p : (Z × B) × A => (((p.1.1, f p.1.1 p.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (observedTranscriptWeight w l f) (observedTranscriptKernel l f)
        (fun zu => r zu.1) := by
  funext ⟨⟨⟨z, u⟩, b⟩, a⟩
  have factor := observedTranscriptKernel_factor l f nonnegative (z, u) a
  have actual : mapWeight
      (fun p : (Z × B) × A => (((p.1.1, f p.1.1 p.2), p.1.2), p.2))
      (factoredWeight w l r) (((z, u), b), a) =
      if f z a = u then w z * r z b * l z a else 0 := by
    have equality (z' : Z) (b' : B) (a' : A) :
        (((z', f z' a'), b'), a') = (((z, u), b), a) ↔
          z' = z ∧ b' = b ∧ a' = a ∧ f z a = u := by
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨rfl, hf⟩, rfl⟩, rfl⟩
        exact ⟨rfl, rfl, rfl, hf⟩
      · rintro ⟨rfl, rfl, rfl, hf⟩
        exact ⟨⟨⟨rfl, hf⟩, rfl⟩, rfl⟩
    simp only [mapWeight, Fintype.sum_prod_type, equality, ite_and, factoredWeight]
    simp
  rw [actual]
  change _ = w z * mapWeight (f z) (l z) u * r z b *
    observedTranscriptKernel l f (z, u) a
  rw [show w z * mapWeight (f z) (l z) u * r z b *
      observedTranscriptKernel l f (z, u) a =
      w z * r z b * (mapWeight (f z) (l z) u *
        observedTranscriptKernel l f (z, u) a) by ring, factor]
  split_ifs <;> simp

theorem factoredWeight_observe_right {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (g : Z → B → V)
    (nonnegative : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A => (((p.1.1, g p.1.1 p.1.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (observedTranscriptWeight w r g) (fun zv => l zv.1)
        (observedTranscriptKernel r g) := by
  funext ⟨⟨⟨z, v⟩, b⟩, a⟩
  have factor := observedTranscriptKernel_factor r g nonnegative (z, v) b
  have actual : mapWeight
      (fun p : (Z × B) × A => (((p.1.1, g p.1.1 p.1.2), p.1.2), p.2))
      (factoredWeight w l r) (((z, v), b), a) =
      if g z b = v then w z * r z b * l z a else 0 := by
    have equality (z' : Z) (b' : B) (a' : A) :
        (((z', g z' b'), b'), a') = (((z, v), b), a) ↔
          z' = z ∧ b' = b ∧ a' = a ∧ g z b = v := by
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨rfl, hg⟩, rfl⟩, rfl⟩
        exact ⟨rfl, rfl, rfl, hg⟩
      · rintro ⟨rfl, rfl, rfl, hg⟩
        exact ⟨⟨⟨rfl, hg⟩, rfl⟩, rfl⟩
    simp only [mapWeight, Fintype.sum_prod_type, equality, ite_and, factoredWeight]
    simp
  rw [actual]
  change _ = w z * mapWeight (g z) (r z) v *
    observedTranscriptKernel r g (z, v) b * l z a
  rw [show w z * mapWeight (g z) (r z) v *
      observedTranscriptKernel r g (z, v) b * l z a =
      w z * (mapWeight (g z) (r z) v *
        observedTranscriptKernel r g (z, v) b) * l z a by ring, factor]
  split_ifs <;> simp

theorem factoredWeight_observe_left_right {Z A B U V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (f : Z → A → U) (g : Z × U → B → V)
    (left_nonnegative : ∀ z a, 0 ≤ l z a) (right_nonnegative : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((((p.1.1, f p.1.1 p.2), g (p.1.1, f p.1.1 p.2) p.1.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (observedTranscriptWeight (observedTranscriptWeight w l f) (fun zu => r zu.1) g)
        (fun zuv => observedTranscriptKernel l f zuv.1)
        (observedTranscriptKernel (fun zu => r zu.1) g) := by
  have first := factoredWeight_observe_left w l r f left_nonnegative
  have second := factoredWeight_observe_right (observedTranscriptWeight w l f)
    (observedTranscriptKernel l f) (fun zu => r zu.1) g
    (fun zu b => right_nonnegative zu.1 b)
  rw [← first, mapWeight_comp] at second
  exact second

theorem observedTranscript_left_right_probability {Z A B U V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (f : Z → A → U) (g : Z × U → B → V)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
        (observedTranscriptWeight (observedTranscriptWeight w l f) (fun zu => r zu.1) g) ∧
      (∀ zuv : (Z × U) × V, IsProbabilityWeight (observedTranscriptKernel l f zuv.1)) ∧
      (∀ zuv : (Z × U) × V,
        IsProbabilityWeight (observedTranscriptKernel (fun zu => r zu.1) g zuv)) := by
  refine ⟨observedTranscriptWeight_probability _ _ g
    (observedTranscriptWeight_probability w l f hw hl) (fun zu => hr zu.1), ?_, ?_⟩
  · exact fun zuv => observedTranscriptKernel_probability l f hl zuv.1
  · exact observedTranscriptKernel_probability (fun zu => r zu.1) g (fun zu => hr zu.1)

end Algebraic.Cutwidth.Extractor.Internal

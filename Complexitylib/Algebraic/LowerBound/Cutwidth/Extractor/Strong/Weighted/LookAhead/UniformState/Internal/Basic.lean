/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional

/-!
# Initial seeds from an exactly uniform repaired state

A map that sends the uniform state law to the uniform seed law preserves
uniformity given an arbitrary transcript. The hypothesis is a weighted
marginal identity, so the calculation also includes transcript rows of
mass zero. This is the seed step after repairing a nearly uniform state.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem retainedSeedWeight_image_dist_le {Z B Q Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) (initialSeed : Q → Seed)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed) :
    weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤
        weightDist (retainedSeedWeight w r q)
          (uniformSecondWeight (retainedSeedWeight w r q)) := by
  let p := retainedSeedWeight w r q
  let f : Z × Q → Z × Seed := fun zu => (zu.1, initialSeed zu.2)
  have mapped : mapWeight f p =
      retainedSeedWeight w r (fun z b => initialSeed (q z b)) := by
    dsimp only [p, retainedSeedWeight, f]
    rw [mapWeight_comp]
  have uniform : mapWeight f (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight f p) := by
    dsimp only [f, uniformSecondWeight]
    rw [firstWeight_map_fiber p (fun _ : Z => initialSeed)]
    unfold uniformExtensionWeight
    rw [mapWeight_tagged (fun _ : Z => initialSeed) (firstWeight p)
      (fun _ : Z => uniformWeight Q), balanced]
  have bound := weightDist_map_le p (uniformSecondWeight p) f
  rw [uniform, mapped] at bound
  exact bound

theorem retainedSeedWeight_uniform_image {Z B Q Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) (initialSeed : Q → Seed)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (uniform : ∀ z u, w z * mapWeight (q z) (r z) u = w z * uniformWeight Q u) :
    retainedSeedWeight w r (fun z b => initialSeed (q z b)) =
      uniformExtensionWeight Seed w := by
  have state : retainedSeedWeight w r q = uniformExtensionWeight Q w := by
    rw [retainedSeedWeight, mapWeight_tagged]
    funext zu
    exact uniform zu.1 zu.2
  calc
    retainedSeedWeight w r (fun z b => initialSeed (q z b)) =
        mapWeight (fun zu : Z × Q => (zu.1, initialSeed zu.2))
          (retainedSeedWeight w r q) := by
      rw [retainedSeedWeight, retainedSeedWeight, mapWeight_comp]
    _ = mapWeight (fun zu : Z × Q => (zu.1, initialSeed zu.2))
        (uniformExtensionWeight Q w) := congrArg _ state
    _ = uniformExtensionWeight Seed w := by
      unfold uniformExtensionWeight
      rw [mapWeight_tagged (fun _ : Z => initialSeed) w (fun _ : Z => uniformWeight Q),
        balanced]

theorem retainedSeedWeight_uniform_image_dist {Z B Q Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Seed] [Nonempty Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) (initialSeed : Q → Seed)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (uniform : ∀ z u, w z * mapWeight (q z) (r z) u = w z * uniformWeight Q u) :
    weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) = 0 := by
  rw [retainedSeedWeight_uniform_image w r q initialSeed balanced uniform]
  simp only [uniformSecondWeight, firstWeight_uniformExtension, weightDist_self]

end Algebraic.Cutwidth.Extractor.Internal

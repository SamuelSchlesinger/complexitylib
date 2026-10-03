/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Mathlib.Data.Fintype.Pi
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Repair.Internal.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact repair of a head with a latent conditional tail

Repair the deterministic pair `(f a, a)` and attach the original tail law
conditioned on `a` to both pair distributions. This construction preserves
the arbitrary correlation of the latent state with its tail. The repaired
tuple's distance is exactly the distance of the old and new head marginals.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem exists_prepend_replacement {α Ω : Type*} [Fintype α] [Fintype Ω]
    (t : Nat) (w : α → ℝ) (tail : α → (Fin t → Ω) → ℝ)
    (f : α → Ω) (target : Ω → ℝ) (hw : IsProbabilityWeight w)
    (htail : ∀ a, IsProbabilityWeight (tail a)) (htarget : IsProbabilityWeight target) :
    ∃ c : Ω × α → ℝ, ∃ r : (Fin (t + 1) → Ω) → ℝ,
      IsProbabilityWeight c ∧ IsProbabilityWeight r ∧
        (∀ h, ∑ a, c (h, a) = target h) ∧ mapWeight (fun z => z 0) r = target ∧
          (∀ h z, r (Fin.cons h z) = ∑ a, c (h, a) * tail a z) ∧
            weightDist
              (mapWeight (fun az : α × (Fin t → Ω) => Fin.cons (f az.1) az.2)
                (fun az => w az.1 * tail az.1 az.2)) r =
              weightDist (mapWeight f w) target := by
  let old := mapWeight (fun a => (f a, a)) w
  have old_probability : IsProbabilityWeight old := hw.map (fun a => (f a, a))
  have old_head : firstWeight old = mapWeight f w := by
    rw [← mapWeight_fst, mapWeight_comp]
  obtain ⟨c, hc, first, _, distance⟩ := exists_joint_marginal_replacement
    old_probability htarget
  let observe (az : (Ω × α) × (Fin t → Ω)) : Fin (t + 1) → Ω :=
    Fin.cons az.1.1 az.2
  let r := mapWeight observe (fun az => c az.1 * tail az.1.2 az.2)
  have r_probability : IsProbabilityWeight r :=
    (attachTail_probability c tail hc htail).map observe
  have head : mapWeight (fun z : Fin (t + 1) → Ω => z 0) r = target :=
    (prependWeight_head c tail htail).trans first
  have factor (h : Ω) (z : Fin t → Ω) :
      r (Fin.cons h z) = ∑ a, c (h, a) * tail a z :=
    prependWeight_apply c tail h z
  have old_output :
      mapWeight observe (fun az => old az.1 * tail az.1.2 az.2) =
        mapWeight (fun az : α × (Fin t → Ω) =>
          (Fin.cons (f az.1) az.2 : Fin (t + 1) → Ω))
          (fun az => w az.1 * tail az.1 az.2) :=
    prependWeight_deterministic w tail f
  have upper : weightDist
      (mapWeight (fun az : α × (Fin t → Ω) => Fin.cons (f az.1) az.2)
        (fun az => w az.1 * tail az.1 az.2)) r ≤
      weightDist (mapWeight f w) target := by
    have bound := weightDist_map_le
      (fun az : (Ω × α) × (Fin t → Ω) => old az.1 * tail az.1.2 az.2)
      (fun az => c az.1 * tail az.1.2 az.2) observe
    rw [old_output, attachTail_dist old c tail htail, distance, old_head] at bound
    exact bound
  have lower : weightDist (mapWeight f w) target ≤ weightDist
      (mapWeight (fun az : α × (Fin t → Ω) => Fin.cons (f az.1) az.2)
        (fun az => w az.1 * tail az.1 az.2)) r := by
    have original_head := prependWeight_head old tail htail
    rw [old_output, old_head] at original_head
    have bound := weightDist_map_le
      (mapWeight (fun az : α × (Fin t → Ω) => Fin.cons (f az.1) az.2)
        (fun az => w az.1 * tail az.1 az.2)) r (fun z : Fin (t + 1) → Ω => z 0)
    rw [original_head, head] at bound
    exact bound
  exact ⟨c, r, hc, r_probability, fun h => congrFun first h, head, factor,
    le_antisymm upper lower⟩

end Algebraic.Cutwidth.Extractor.Internal

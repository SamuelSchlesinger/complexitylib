/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.AverageCase.Sweep
public import Complexitylib.Circuits.Frontier.Boundary.Linear

/-!
# Capacity of boundary codes

An encoding must determine the entire transition: both adjacent boundary states and the
newly read inputs. Bounding each boundary separately would incorrectly omit the cost of
joining them. Any finite code with this property can replace the ambient wire alphabet.
-/

@[expose] public section

namespace Complexity.Frontier.Sweep

open Set

variable {ι U M : Type*} [Finite ι] [Finite U] {S : Set (ι → U)} (P : Sweep S M)

/-- Count used transitions by any finite code that determines them on accepted inputs. -/
theorem transitionCount_le_codes {D : ℕ → Type*}
    (code : ∀ t, (ι → U) → D t) (C : ∀ t, Set (D t))
    (hC : ∀ t < P.length, (C t).Finite)
    (hmem : ∀ t < P.length, ∀ x ∈ S, code t x ∈ C t)
    (hdet : ∀ t < P.length, ∀ x ∈ S, ∀ y ∈ S,
      code t x = code t y → P.transition t x = P.transition t y) :
    P.transitionCount ≤ ∑ t ∈ Finset.range P.length, (C t).ncard := by
  refine Finset.sum_le_sum fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  exact (ncard_image_le_ncard_image_of_determines (toFinite _) _ _ (hdet t ht)).trans
    (ncard_le_ncard (by rintro _ ⟨x, hx, rfl⟩; exact hmem t ht x hx) (hC t ht))

/-- Weighted peeling with code capacity in place of the number of boundary wires. -/
theorem abs_sumOn_le_codes (hP : P.Coherent) (hL : 0 < P.length)
    {D : ℕ → Type*} (code : ∀ t, (ι → U) → D t) (C : ∀ t, Set (D t))
    (hC : ∀ t < P.length, (C t).Finite)
    (hmem : ∀ t < P.length, ∀ x ∈ S, code t x ∈ C t)
    (hdet : ∀ t < P.length, ∀ x ∈ S, ∀ y ∈ S,
      code t x = code t y → P.transition t x = P.transition t y)
    {KL KR : ℕ} (hKL : 1 < KL) (hKR : 1 < KR)
    {w cost : (ι → U) → ℝ} {a : ℝ} (ha : 0 ≤ a) (hw : ∀ x, |w x| ≤ a)
    (hc : ∀ x, 0 ≤ cost x) (hrect : Frontier.RectangleBudget w cost KL KR) :
    |Frontier.sumOn w S| ≤ Frontier.sumOn cost S +
      a * ((KL - 1) * (KR - 1) * ∑ t ∈ Finset.range P.length, (C t).ncard : ℕ) := by
  refine (P.abs_sumOn_le_of_budget hP hL hKL hKR ha hw hc hrect).trans ?_
  gcongr
  exact P.transitionCount_le_codes code C hC hmem hdet

end Complexity.Frontier.Sweep

namespace Complexity.Frontier.Sweep

open Set

variable {ι F M W : Type*} [Finite ι] [Field F] [Finite F]
  [AddCommGroup W] [Module F W]
  {S : Set (ι → F)} (P : Sweep S M)

/-- Affine dependence can be charged by rank: equality of the linear parts is enough to
determine the entire transition, and a fixed translation does not affect this test. -/
theorem transitionCount_le_linear_codes (L : ℕ → (ι → F) →ₗ[F] W)
    (hdet : ∀ t < P.length, ∀ x ∈ S, ∀ y ∈ S,
      L t x = L t y → P.transition t x = P.transition t y) :
    P.transitionCount ≤ ∑ t ∈ Finset.range P.length,
      Nat.card F ^ Module.finrank F (LinearMap.range (L t)) := by
  have H := P.transitionCount_le_codes (fun t x => L t x) (fun t => Set.range (L t))
    (fun t _ => finite_range _) (fun t _ x _ => ⟨x, rfl⟩) hdet
  convert H using 1
  apply Finset.sum_congr rfl
  intro t _
  rw [← LinearMap.coe_range, ← Nat.card_coe_set_eq]
  change _ = Nat.card ↥(LinearMap.range (L t))
  exact (Module.natCard_eq_pow_finrank (K := F)).symm

end Complexity.Frontier.Sweep

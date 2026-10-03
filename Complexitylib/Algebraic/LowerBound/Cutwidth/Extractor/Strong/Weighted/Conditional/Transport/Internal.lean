/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Equiv.Prod

/-!
# Transporting conditional uniformity through fiber equivalences

A bijection of each output fiber preserves its uniform law and the retained
marginal. The resulting map on the tagged product is itself a bijection, so
its total variation distance is unchanged. These identities hold for signed
weights and empty alphabets as well as for probability laws.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem mapWeight_uniformSecond_fiberEquiv {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (e : α → β ≃ γ) :
    mapWeight (fun ab => (ab.1, e ab.1 ab.2)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun ab => (ab.1, e ab.1 ab.2)) p) := by
  funext ac
  change mapWeight (Equiv.prodCongrRight e) (uniformSecondWeight p) ac = _
  rw [mapWeight_equiv_apply]
  change firstWeight p ac.1 * (Fintype.card β : ℝ)⁻¹ =
    firstWeight (mapWeight (fun ab => (ab.1, e ab.1 ab.2)) p) ac.1 *
      (Fintype.card γ : ℝ)⁻¹
  rw [firstWeight_map_fiber p (fun a b => e a b), Fintype.card_congr (e ac.1)]

theorem weightDist_uniformSecond_fiberEquiv {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (e : α → β ≃ γ) :
    weightDist (mapWeight (fun ab => (ab.1, e ab.1 ab.2)) p)
      (uniformSecondWeight (mapWeight (fun ab => (ab.1, e ab.1 ab.2)) p)) =
        weightDist p (uniformSecondWeight p) := by
  rw [← mapWeight_uniformSecond_fiberEquiv p e]
  change weightDist (mapWeight (Equiv.prodCongrRight e) p)
    (mapWeight (Equiv.prodCongrRight e) (uniformSecondWeight p)) = _
  simp only [weightDist, mapWeight_equiv_apply]
  exact congrArg (fun s : ℝ => s / 2)
    ((Equiv.prodCongrRight e).symm.sum_comp (fun ab => |p ab - uniformSecondWeight p ab|))

theorem mapWeight_uniformSecond_add_right {α β : Type*}
    [Fintype α] [Fintype β] [AddGroup β]
    (p : α × β → ℝ) (mask : α → β) :
    mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) p) := by
  simpa only [Equiv.coe_addRight] using
    mapWeight_uniformSecond_fiberEquiv p (fun a => Equiv.addRight (mask a))

theorem weightDist_uniformSecond_add_right {α β : Type*}
    [Fintype α] [Fintype β] [AddGroup β]
    (p : α × β → ℝ) (mask : α → β) :
    weightDist (mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) p)
      (uniformSecondWeight (mapWeight (fun ab => (ab.1, ab.2 + mask ab.1)) p)) =
        weightDist p (uniformSecondWeight p) := by
  simpa only [Equiv.coe_addRight] using
    weightDist_uniformSecond_fiberEquiv p (fun a => Equiv.addRight (mask a))

end Algebraic.Cutwidth.Extractor.Internal

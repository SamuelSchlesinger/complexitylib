/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Synthesis

/-!
# Exclusive or in De Morgan synthesis

Exclusive or of two available functions costs four De Morgan gates:
`x ⊕ y = (x ∨ y) ∧ ¬(x ∧ y)`, sharing nothing beyond the two arguments.

`Synthesis.xor_of_mem` comes from `Cslib.Computability.Circuit.Boolean.Synthesis` at commit
`2a4389b` of the author's CSLib fork (branch `complexitylib-integration`); upstream CSLib does not
have it. This file lives in `Complexitylib/Cslib/` because it extends CSLib types in their home
namespace `Cslib.Circuits`; its contents are candidates for upstreaming to CSLib.
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean

variable {n : ℕ}

namespace Synthesis

variable {s : Set (BooleanFunction n)} {f g : BooleanFunction n}

/-- XOR costs four gates when its two arguments are already available. The intermediate
conjunction and disjunction are shared. -/
theorem xor_of_mem (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis interpretation s {fun x => Bool.xor (f x) (g x)} 4 := by
  let both : BooleanFunction n := fun x => f x && g x
  let either : BooleanFunction n := fun x => f x || g x
  let notBoth : BooleanFunction n := fun x => !(both x)
  have hboth : Synthesis interpretation s {both} 1 := by
    simpa [both] using (of_mem hf).and (of_mem hg)
  have heither : Synthesis interpretation s {either} 1 := by
    simpa [either] using (of_mem hf).or (of_mem hg)
  have hnot : Synthesis interpretation (s ∪ ({both} ∪ {either})) {notBoth} 1 := by
    have hbmem : both ∈ s ∪ ({both} ∪ {either}) := by simp
    simpa [notBoth] using (of_mem hbmem).not
  have hfinal : Synthesis interpretation
      (s ∪ (({both} ∪ {either}) ∪ {notBoth}))
      {fun x => either x && notBoth x} 1 := by
    have hemem : either ∈ s ∪ (({both} ∪ {either}) ∪ {notBoth}) := by simp
    have hnmem : notBoth ∈ s ∪ (({both} ∪ {either}) ∪ {notBoth}) := by simp
    exact (of_mem hemem).and (of_mem hnmem)
  have h := ((hboth.union heither).comp hnot).trans hfinal
  simpa only [Nat.add_assoc] using
    h.mono Set.Subset.rfl (by
      intro q hq
      rcases Set.mem_singleton_iff.mp hq with rfl
      simp only [Set.mem_singleton_iff]
      funext x
      cases hf' : f x <;> cases hg' : g x <;>
        simp [both, either, notBoth, hf', hg'])
      (by omega : (1 + 1 + 1 + 1) ≤ 4)

end Synthesis

end Cslib.Circuits

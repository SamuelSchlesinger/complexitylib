/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict.Defs
public import Complexitylib.Algebraic.Circuit
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict.Internal

/-!
# Restricted splits

The fibre bound of `MultiOutput.Rank` counts all inputs of a circuit. This file restricts it to
a set of inputs, which bounds circuits for maps that are linear only once some inputs are
fixed, such as multiplication with one factor fixed.

**The product-domain fibre bound** (`card_piFinset_le_of_fibres`). Split the wires of a circuit
computing `f` into `S` and its complement, with forward signals `A` and backward signals `B`.
For a coordinatewise product domain `D = D₀ × ⋯ × D_{n-1}`, if every left fibre taken within
`D` has at most `DT` elements and every right fibre within `D` at most `DS`, then
`|D| ≤ |U| ^ (|A| + |B|) · DT · DS`. More generally this holds for every set of inputs closed
under the mixing of `SingleCut.mix` (`card_le_of_fibres_of_mix_of_trace`): the proof of the
unrestricted bound only mixes two inputs, and mixing two members of a product stays in it.

**The kernel form** (`card_pow_le_supportedKernel`). Fix the inputs outside a set `J` of free
coordinates to a base point `z₀`. If on these inputs the function changes by `g d` whenever the
input changes by `d`, then every split satisfies
`|U| ^ |J| ≤ |U| ^ (|A| + |B|) · |ker₁| · |ker₂|`, where `ker₁ = supportedKernel g X_S Y_T`
consists of the vectors supported on the free inputs `X_S` placed in `S` whose image vanishes
on the outputs `Y_T` carried outside `S`, and `ker₂ = supportedKernel g X_T Y_S`. For a linear
`g` these are kernels of blocks, and the bound is the rank-cut bound
`rank g[Y_T, X_S] + rank g[Y_S, X_T] ≤ |A| + |B|` restricted to the free inputs.

**Closed sets separate** (`apply_eq_zero_of_closed_of_trace`). For a split crossed by no
signal, both kernels are full: `g` maps vectors supported on `X_S` to vectors vanishing on
`Y_T`, and vectors supported on `X_T` to vectors vanishing on `Y_S`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut

variable {σ : Signature} {n s m : Nat} {U : Type*}

/-! ## Sets closed under mixing -/

section Mix

variable [Fintype U] [DecidableEq U]

/-- **The fibre bound on a set closed under mixing, for a program.** If the wires `out` of a
program carry `f` and `Z` is closed under mixing for the split `S`, every left fibre within
`Z` has at most `DT` elements and every right fibre within `Z` at most `DS`, then
`|Z| ≤ |U| ^ (|A| + |B|) · DT · DS`. -/
theorem card_le_of_fibres_of_mix_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) {Z : Finset (Fin n → U)}
    (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, mix S x x' ∈ Z) {DT DS : Nat}
    (hT : ∀ x ∈ Z, (Z ∩ leftFibre out f S x).card ≤ DT)
    (hS : ∀ x ∈ Z, (Z ∩ rightFibre out f S x).card ≤ DS) :
    Z.card ≤ Fintype.card U ^ ((forward p S).card + (backward p S).card) * (DT * DS) :=
  Internal.card_le_of_fibres_of_mix p I out f hf S hZ hT hS

/-- **The product-domain fibre bound.** If a circuit computes `f`, and for a split `S` and a
coordinatewise product domain `D` every left fibre taken within `D` has at most `DT` elements
and every right fibre within `D` at most `DS`, then `|D| ≤ |U| ^ (|A| + |B|) · DT · DS`. -/
theorem card_piFinset_le_of_fibres {c : Circuit σ n m} {I : Interpretation σ U}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) (S : Finset (Wire n c.size))
    (D : Fin n → Finset U) {DT DS : Nat}
    (hT : ∀ x ∈ Fintype.piFinset D, (Fintype.piFinset D ∩ leftFibre c.outputs f S x).card ≤ DT)
    (hS : ∀ x ∈ Fintype.piFinset D,
      (Fintype.piFinset D ∩ rightFibre c.outputs f S x).card ≤ DS) :
    ∏ j, (D j).card ≤
      Fintype.card U ^ ((forward c.program S).card + (backward c.program S).card) * (DT * DS) := by
  rw [← Fintype.card_piFinset]
  exact Internal.card_le_of_fibres_of_mix c.program I c.outputs f
    (fun x i => congrFun (hc x) i) S (fun _ hx _ hx' => Internal.mix_mem_piFinset S D hx hx')
    hT hS

end Mix

/-! ## The kernel form -/

section Kernel

variable [AddCommGroup U] [Fintype U] [DecidableEq U]

/-- A kernel has at most `|U| ^ |P|` vectors supported on `P`. -/
theorem card_supportedKernel_le (g : (Fin n → U) → Fin m → U) (P : Finset (Fin n))
    (Q : Finset (Fin m)) : (supportedKernel g P Q).card ≤ Fintype.card U ^ P.card :=
  Internal.card_supportedKernel_le g P Q

/-- **The forward restricted rank-cut bound, kernel form, for a program.** If the wires `out`
of a program carry `f`, and on the inputs agreeing with `z₀` off `J` the function changes by
`g d` when its input changes by `d`, then every split `S` satisfies
`|U| ^ |X_S| ≤ |U| ^ |A| · |supportedKernel g X_S Y_T|`, using only the forward signals
`A = forward p S`. -/
theorem card_pow_le_supportedKernel_forward_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ (inputsIn S ∩ J).card ≤
      Fintype.card U ^ (forward p S).card *
        (supportedKernel g (inputsIn S ∩ J) (outputsIn out S)ᶜ).card :=
  Internal.card_pow_le_supportedKernel_forward (p := p) (I := I) (out := out) (f := f) hf S J z₀ g
    hg

/-- **The backward restricted rank-cut bound, kernel form, for a program.** Symmetrically,
`|U| ^ |X_T| ≤ |U| ^ |B| · |supportedKernel g X_T Y_S|`, using only the backward signals
`B = backward p S`. -/
theorem card_pow_le_supportedKernel_backward_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ ((inputsIn S)ᶜ ∩ J).card ≤
      Fintype.card U ^ (backward p S).card *
        (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn out S)).card :=
  Internal.card_pow_le_supportedKernel_backward (p := p) (I := I) (out := out) (f := f) hf S J z₀
    g hg

/-- **The restricted rank-cut bound, kernel form, for a program.** If the wires `out` of a
program carry `f`, and on the inputs agreeing with `z₀` off `J` the function changes by `g d`
when its input changes by `d`, then every split `S` satisfies
`|U| ^ |J| ≤ |U| ^ (|A| + |B|) · |supportedKernel g X_S Y_T| · |supportedKernel g X_T Y_S|`,
where `X_S` and `X_T` are the free inputs in `S` and outside `S`, and `Y_S` and `Y_T` the
outputs carried in `S` and outside `S`. -/
theorem card_pow_le_supportedKernel_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ J.card ≤
      Fintype.card U ^ ((forward p S).card + (backward p S).card) *
        ((supportedKernel g (inputsIn S ∩ J) (outputsIn out S)ᶜ).card *
          (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn out S)).card) :=
  Internal.card_pow_le_supportedKernel (p := p) (I := I) (out := out) (f := f) hf S J z₀ g hg

/-- **The forward restricted rank-cut bound, kernel form.** If a circuit computes `f`, and on
the inputs agreeing with `z₀` off `J` the function changes by `g d` when its input changes by
`d`, then every split `S` of its wires satisfies
`|U| ^ |X_S| ≤ |U| ^ |A| · |supportedKernel g X_S Y_T|`. -/
theorem card_pow_le_supportedKernel_forward {c : Circuit σ n m} {I : Interpretation σ U}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) (S : Finset (Wire n c.size))
    (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ (inputsIn S ∩ J).card ≤
      Fintype.card U ^ (forward c.program S).card *
        (supportedKernel g (inputsIn S ∩ J) (outputsIn c.outputs S)ᶜ).card :=
  Internal.card_pow_le_supportedKernel_forward (p := c.program) (I := I) (out := c.outputs)
    (f := f) (fun x i => congrFun (hc x) i) S J z₀ g hg

/-- **The backward restricted rank-cut bound, kernel form.** Symmetrically,
`|U| ^ |X_T| ≤ |U| ^ |B| · |supportedKernel g X_T Y_S|`. -/
theorem card_pow_le_supportedKernel_backward {c : Circuit σ n m} {I : Interpretation σ U}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) (S : Finset (Wire n c.size))
    (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ ((inputsIn S)ᶜ ∩ J).card ≤
      Fintype.card U ^ (backward c.program S).card *
        (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn c.outputs S)).card :=
  Internal.card_pow_le_supportedKernel_backward (p := c.program) (I := I) (out := c.outputs)
    (f := f) (fun x i => congrFun (hc x) i) S J z₀ g hg

/-- **The restricted rank-cut bound, kernel form.** If a circuit computes `f`, and on the
inputs agreeing with `z₀` off `J` the function changes by `g d` when its input changes by `d`,
then every split `S` of its wires satisfies
`|U| ^ |J| ≤ |U| ^ (|A| + |B|) · |supportedKernel g X_S Y_T| · |supportedKernel g X_T Y_S|`. -/
theorem card_pow_le_supportedKernel {c : Circuit σ n m} {I : Interpretation σ U}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) (S : Finset (Wire n c.size))
    (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ J.card ≤
      Fintype.card U ^ ((forward c.program S).card + (backward c.program S).card) *
        ((supportedKernel g (inputsIn S ∩ J) (outputsIn c.outputs S)ᶜ).card *
          (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn c.outputs S)).card) :=
  Internal.card_pow_le_supportedKernel (p := c.program) (I := I) (out := c.outputs) (f := f)
    (fun x i => congrFun (hc x) i) S J z₀ g hg

omit [Fintype U] [DecidableEq U] in
/-- **Zero forward cut separates left inputs from outside outputs.** If a split `S` has no
forward signals, `g` maps every vector supported on the free inputs in `S` to a vector
vanishing on the outputs carried outside `S`. -/
theorem apply_eq_zero_of_forward_eq_empty_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z))
    (hfwd : forward p S = ∅) :
    ∀ d : Fin n → U, (∀ k, k ∉ inputsIn S ∩ J → d k = 0) →
      ∀ i, i ∉ outputsIn out S → g d i = 0 :=
  fun _ hd _ hi =>
    Internal.apply_eq_zero_of_forward_eq_empty (p := p) (I := I) (out := out) (f := f) hf S J z₀
      g hg hfwd hd hi

omit [Fintype U] [DecidableEq U] in
/-- **Zero backward cut separates outside inputs from inside outputs.** Symmetrically, if a
split `S` has no backward signals, `g` maps every vector supported on the free inputs outside
`S` to a vector vanishing on the outputs carried in `S`. -/
theorem apply_eq_zero_of_backward_eq_empty_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z))
    (hbwd : backward p S = ∅) :
    ∀ d : Fin n → U, (∀ k, k ∉ (inputsIn S)ᶜ ∩ J → d k = 0) →
      ∀ i ∈ outputsIn out S, g d i = 0 :=
  fun _ hd _ hi =>
    Internal.apply_eq_zero_of_backward_eq_empty (p := p) (I := I) (out := out) (f := f) hf S J z₀
      g hg hbwd hd hi

/-- **Closed sets separate.** If the wires `out` of a program carry `f`, the function changes
by `g d` when its input changes by `d` on the inputs agreeing with `z₀` off `J`, and a split
`S` has no forward and no backward signals, then `g` maps every vector supported on the free
inputs in `S` to a vector vanishing on the outputs carried outside `S`, and every vector
supported on the free inputs outside `S` to a vector vanishing on the outputs carried in
`S`. -/
theorem apply_eq_zero_of_closed_of_trace (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) {f : (Fin n → U) → Fin m → U}
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z))
    (hfwd : forward p S = ∅) (hbwd : backward p S = ∅) :
    (∀ d : Fin n → U, (∀ k, k ∉ inputsIn S ∩ J → d k = 0) →
        ∀ i, i ∉ outputsIn out S → g d i = 0) ∧
      (∀ d : Fin n → U, (∀ k, k ∉ (inputsIn S)ᶜ ∩ J → d k = 0) →
        ∀ i ∈ outputsIn out S, g d i = 0) :=
  Internal.apply_eq_zero_of_closed (p := p) (I := I) (out := out) (f := f) hf S J z₀ g hg hfwd
    hbwd

end Kernel

end Algebraic.Cutwidth.MultiOutput

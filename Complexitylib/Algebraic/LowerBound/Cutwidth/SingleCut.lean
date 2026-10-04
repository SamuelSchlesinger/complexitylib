/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Complexitylib.Algebraic.Circuit
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut.Internal

/-!
# The single-cut criterion

Split the wires of a circuit, its inputs and its gates, into a set `S` and its complement. Let
`i` be the number of inputs in `S`, let `A = forward p S` be the signals computed in `S` and
read outside `S`, and let `B = backward p S` be the signals computed outside `S` and read in
`S`. A signal is the value of one wire, counted once however many gates read it.

**The single-cut criterion** (`card_accepting_le`, `card_accepting_lt`). If a single-output
circuit computes a `K`-rectangle-free function `f`, then for every such split
`|f⁻¹(1)| ≤ (K - 1) (2 ^ (i + |B|) + 2 ^ (n - i + |A|)) < K (2 ^ (i + |B|) + 2 ^ (n - i + |A|))`.
With at least `2 ^ (n - 2)` accepted inputs this gives
`n ≤ max (i + |B|) (n - i + |A|) + ⌈log₂ K⌉ + 2` (`le_max_add_clog`), hence
`max (i + |B|) (n - i + |A|) > n - log₂ K - 3` (`sub_logb_lt_max`).

The proof fixes the values `(a, b)` of the forward and backward signals (the *boundary key*).
Two facts hold for every signature and value type:

* *Cut and paste* (`trace_mix`): if two inputs have the same boundary key, the input taking
  the first input's coordinates on `S` and the second's elsewhere evaluates like the first
  on `S` and like the second outside `S`. So the inputs with a fixed key, and the accepted
  inputs with a fixed key, form a product of a left part and a right part
  (`card_filter_boundaryKey_eq`), and the latter product is a one-rectangle of `f`.
* *Determination* (`trace_eq_of_agree_backward`, `trace_eq_of_agree_forward`): the inputs in
  `S` and the backward values determine every value in `S`; symmetrically outside `S`. So for a
  fixed `b` the left parts of different keys are disjoint, and the left parts of all keys
  number at most `2 ^ (i + |B|)` in total (`sum_card_leftParts_le`); symmetrically the right
  parts number at most `2 ^ (n - i + |A|)` (`sum_card_rightParts_le`).

A rectangle with a side below `K` has at most `K - 1` times its other side many points, and
summing over the keys gives the criterion.

The structural results are stated for programs with any number of outputs, any signature, and
any value type, so they apply equally to multi-output circuits: an output carried by a wire in
`S` is a function of the left part on each fibre, and an output carried by a wire outside `S` is
a function of the right part.

As a remark connecting to orderings (`exists_prefix_le`), every injective ranking of the wires
has a prefix containing half of the inputs, so some prefix is crossed by at least
`⌊n/2⌋ - ⌈log₂ K⌉ - 2` signals.
-/

@[expose] public section

namespace Algebraic.Cutwidth.SingleCut

variable {σ : Signature} {n s : Nat} {U : Type*}

/-! ## Cut and paste, and determination -/

section Structure

variable (p : Program σ n s) (I : Interpretation σ U) {S : Finset (Wire n s)}
  {x x' : Fin n → U}

/-- **Cut and paste.** If two inputs agree on the forward and backward signals of `S`, the
mixed input has the values of the first input on `S` and of the second outside `S`. -/
theorem trace_mix (hfwd : ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w)
    (hbwd : ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w) (w : Wire n s) :
    p.trace I (mix S x x') w = if w ∈ S then p.trace I x w else p.trace I x' w :=
  Internal.trace_mix p I hfwd hbwd w

/-- **Determination.** The inputs placed in `S` and the backward signal values determine every
value on `S`. -/
theorem trace_eq_of_agree_backward (hin : ∀ j ∈ inputsIn S, x j = x' j)
    (hbwd : ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w) :
    ∀ w ∈ S, p.trace I x w = p.trace I x' w :=
  Internal.trace_eq_of_agree_backward p I hin hbwd

/-- **Determination outside the cut.** The inputs placed outside `S` and the forward signal
values determine every value outside `S`. -/
theorem trace_eq_of_agree_forward (hin : ∀ j, j ∉ inputsIn S → x j = x' j)
    (hfwd : ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w) :
    ∀ w, w ∉ S → p.trace I x w = p.trace I x' w :=
  Internal.trace_eq_of_agree_forward p I hin hfwd

variable {p I}

/-- Equal boundary keys mean agreement on the forward signals. -/
theorem agree_forward_of_boundaryKey_eq (h : boundaryKey p I S x = boundaryKey p I S x') :
    ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w :=
  Internal.agree_forward_of_boundaryKey_eq h

/-- Equal boundary keys mean agreement on the backward signals. -/
theorem agree_backward_of_boundaryKey_eq (h : boundaryKey p I S x = boundaryKey p I S x') :
    ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w :=
  Internal.agree_backward_of_boundaryKey_eq h

variable (p I)

/-- Mixing two inputs with equal boundary keys keeps the key. -/
theorem boundaryKey_mix (h : boundaryKey p I S x = boundaryKey p I S x') :
    boundaryKey p I S (mix S x x') = boundaryKey p I S x :=
  Internal.boundaryKey_mix p I h

/-- **Left parts and backward values determine the key.** Two inputs with the same left part
and the same backward values have the same forward values. -/
theorem boundaryKey_eq_of_leftPart_eq (hl : leftPart S x = leftPart S x')
    (hb : (boundaryKey p I S x).2 = (boundaryKey p I S x').2) :
    boundaryKey p I S x = boundaryKey p I S x' :=
  Internal.boundaryKey_eq_of_leftPart_eq p I hl hb

/-- **Right parts and forward values determine the key.** Two inputs with the same right part
and the same forward values have the same backward values. -/
theorem boundaryKey_eq_of_rightPart_eq (hr : rightPart S x = rightPart S x')
    (ha : (boundaryKey p I S x).1 = (boundaryKey p I S x').1) :
    boundaryKey p I S x = boundaryKey p I S x' :=
  Internal.boundaryKey_eq_of_rightPart_eq p I hr ha

end Structure

/-! ## Product fibres and partition bounds -/

section Fibres

variable (p : Program σ n s) (I : Interpretation σ U) {S : Finset (Wire n s)}

@[simp] theorem leftPart_mix (x x' : Fin n → U) : leftPart S (mix S x x') = leftPart S x :=
  Internal.leftPart_mix S x x'

@[simp] theorem rightPart_mix (x x' : Fin n → U) : rightPart S (mix S x x') = rightPart S x' :=
  Internal.rightPart_mix S x x'

/-- An input is determined by its left and right parts. -/
theorem eq_of_leftPart_eq_of_rightPart_eq {x x' : Fin n → U}
    (hl : leftPart S x = leftPart S x') (hr : rightPart S x = rightPart S x') : x = x' :=
  Internal.eq_of_leftPart_eq_of_rightPart_eq hl hr

variable [DecidableEq U] {Z : Finset (Fin n → U)}

/-- **Fibres are closed under mixing.** If `Z` is closed under mixing inputs with equal keys,
so is the set of members of `Z` with a given key. -/
theorem mix_mem_filter
    (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, boundaryKey p I S x = boundaryKey p I S x' → mix S x x' ∈ Z)
    {κ : (↥(forward p S) → U) × (↥(backward p S) → U)} {x x' : Fin n → U}
    (hx : x ∈ Z.filter fun x => boundaryKey p I S x = κ)
    (hx' : x' ∈ Z.filter fun x => boundaryKey p I S x = κ) :
    mix S x x' ∈ Z.filter fun x => boundaryKey p I S x = κ :=
  Internal.mix_mem_filter p I hZ hx hx'

/-- **Product fibres.** If `Z` is closed under mixing inputs with equal keys (for example all
inputs, or the inputs on which an output wire carries a fixed value), the members of `Z` with
a given key are in bijection with the product of their left and right parts. -/
theorem card_filter_boundaryKey_eq
    (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, boundaryKey p I S x = boundaryKey p I S x' → mix S x x' ∈ Z)
    (κ : (↥(forward p S) → U) × (↥(backward p S) → U)) :
    (Z.filter fun x => boundaryKey p I S x = κ).card =
      (leftParts p I S Z κ).card * (rightParts p I S Z κ).card :=
  Internal.card_filter_boundaryKey_eq p I hZ κ

variable [Fintype U] (S) (Z)

/-- There are at most `|U| ^ (|A| + |B|)` boundary keys. -/
theorem card_image_boundaryKey_le :
    (Z.image (boundaryKey p I S)).card ≤
      Fintype.card U ^ ((forward p S).card + (backward p S).card) :=
  Internal.card_image_boundaryKey_le p I S Z

/-- **For a fixed backward part, the left parts partition the left inputs.** Summed over the
keys realized in `Z`, the left parts number at most `|U| ^ (i + |B|)`. -/
theorem sum_card_leftParts_le :
    ∑ κ ∈ Z.image (boundaryKey p I S), (leftParts p I S Z κ).card ≤
      Fintype.card U ^ ((inputsIn S).card + (backward p S).card) :=
  Internal.sum_card_leftParts_le p I S Z

/-- **For a fixed forward part, the right parts partition the right inputs.** Summed over the
keys realized in `Z`, the right parts number at most `|U| ^ (n - i + |A|)`. -/
theorem sum_card_rightParts_le :
    ∑ κ ∈ Z.image (boundaryKey p I S), (rightParts p I S Z κ).card ≤
      Fintype.card U ^ (n - (inputsIn S).card + (forward p S).card) :=
  Internal.sum_card_rightParts_le p I S Z

end Fibres

/-! ## The criterion -/

section Criterion

variable {f : Cslib.BooleanFunction n} {K : Nat}

/-- **The single-cut criterion for a wire.** If the wire `out` of a program carries a
`K`-rectangle-free function `f`, then for every set `S` of wires,
`|f⁻¹(1)| ≤ (K - 1) (2 ^ (i + |B|) + 2 ^ (n - i + |A|))`. -/
theorem card_accepting_le_of_trace (p : Program σ n s) (I : Interpretation σ Bool)
    (out : Wire n s) (hf : ∀ x, f x = p.trace I x out) (hrect : RectangleFree f K)
    (S : Finset (Wire n s)) :
    (accepting f).card ≤ (K - 1) * (2 ^ ((inputsIn S).card + (backward p S).card) +
      2 ^ (n - (inputsIn S).card + (forward p S).card)) :=
  Internal.card_accepting_le_of_trace p I out hf hrect S

variable {c : Circuit σ n 1} {I : Interpretation σ Bool}

/-- **The single-cut criterion.** If a single-output circuit computes a `K`-rectangle-free
function `f`, then for every set `S` of its wires, with `i` inputs in `S`, forward signals
`A = forward c.program S` and backward signals `B = backward c.program S`,
`|f⁻¹(1)| ≤ (K - 1) (2 ^ (i + |B|) + 2 ^ (n - i + |A|))`. -/
theorem card_accepting_le (hc : c.Computes I fun x _ => f x) (hrect : RectangleFree f K)
    (S : Finset (Wire n c.size)) :
    (accepting f).card ≤ (K - 1) * (2 ^ ((inputsIn S).card + (backward c.program S).card) +
      2 ^ (n - (inputsIn S).card + (forward c.program S).card)) :=
  Internal.card_accepting_le_of_trace c.program I (c.outputs 0)
    (Internal.eq_trace_of_computes hc) hrect S

/-- **The single-cut criterion, strict form.**
`|f⁻¹(1)| < K (2 ^ (i + |B|) + 2 ^ (n - i + |A|))`. -/
theorem card_accepting_lt (hc : c.Computes I fun x _ => f x) (hrect : RectangleFree f K)
    (S : Finset (Wire n c.size)) :
    (accepting f).card < K * (2 ^ ((inputsIn S).card + (backward c.program S).card) +
      2 ^ (n - (inputsIn S).card + (forward c.program S).card)) :=
  Internal.card_accepting_lt_of_trace c.program I (c.outputs 0)
    (Internal.eq_trace_of_computes hc) hrect S

/-- **The single-cut corollary.** If a single-output circuit computes a `K`-rectangle-free
function with at least `2 ^ (n - 2)` accepted inputs, then every set `S` of its wires has
`n ≤ max (i + |B|) (n - i + |A|) + ⌈log₂ K⌉ + 2`. -/
theorem le_max_add_clog (hc : c.Computes I fun x _ => f x) (hrect : RectangleFree f K)
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (S : Finset (Wire n c.size)) :
    n ≤ max ((inputsIn S).card + (backward c.program S).card)
      (n - (inputsIn S).card + (forward c.program S).card) + Nat.clog 2 K + 2 :=
  Internal.le_max_add_clog_of_trace c.program I (c.outputs 0)
    (Internal.eq_trace_of_computes hc) hrect hacc S

/-- **The single-cut corollary, real form.** Under the hypotheses of `le_max_add_clog`,
`max (i + |B|) (n - i + |A|) > n - log₂ K - 3`. -/
theorem sub_logb_lt_max (hc : c.Computes I fun x _ => f x) (hrect : RectangleFree f K)
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (S : Finset (Wire n c.size)) :
    (n : ℝ) - Real.logb 2 K - 3 < (max ((inputsIn S).card + (backward c.program S).card)
      (n - (inputsIn S).card + (forward c.program S).card) : Nat) :=
  Internal.sub_logb_lt_max_of_trace c.program I (c.outputs 0)
    (Internal.eq_trace_of_computes hc) hrect hacc S

/-- **Every ordering has a heavily crossed prefix.** Under the hypotheses of
`le_max_add_clog`, every injective ranking of the wires has a prefix, the wires ranked below
some `t`, crossed by at least `⌊n/2⌋ - ⌈log₂ K⌉ - 2` signals: the prefix containing exactly
`⌊n/2⌋` inputs would otherwise violate the criterion. -/
theorem exists_prefix_le (hc : c.Computes I fun x _ => f x) (hrect : RectangleFree f K)
    (hacc : 2 ^ (n - 2) ≤ (accepting f).card) (rank : Wire n c.size → Nat)
    (hrank : Function.Injective rank) :
    ∃ t : Nat, n / 2 ≤
      (forward c.program (Finset.univ.filter fun w => rank w < t)).card +
        (backward c.program (Finset.univ.filter fun w => rank w < t)).card +
          Nat.clog 2 K + 2 :=
  Internal.exists_prefix_le_of_trace c.program I (c.outputs 0)
    (Internal.eq_trace_of_computes hc) hrect hacc rank hrank

end Criterion

end Algebraic.Cutwidth.SingleCut

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

/-!
# Proofs for the single-cut criterion

Wires are handled by induction in program order (`wire_induction`): a gate reads only inputs
and earlier gates. Two facts about a cut `S` follow.

* *Cut and paste* (`trace_mix`): if two inputs agree on the forward and backward signals, the
  mixed input has the first input's values on `S` and the second input's values outside `S`.
  Its gate equations hold because every value a gate reads across the cut is a boundary value.
* *Determination* (`trace_eq_of_agree_backward`): the inputs placed in `S` and the backward
  signal values determine every value on `S`.

So the inputs with a fixed boundary key form a product of a left and a right part
(`card_filter_boundaryKey_eq`), and for a fixed backward part the left parts of different keys
are disjoint, which bounds their total size (`sum_card_leftParts_le`). For an accepting set,
each product is a one-rectangle, so one side is smaller than the rectangle threshold
(`card_accepting_le_of_trace`).

For the ordering remark, the number of inputs in the prefix of an injective ranking grows by
at most one per step (`exists_card_inputsIn_prefixBelow_eq`), so some prefix holds half of the
inputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.SingleCut.Internal

variable {σ : Signature} {n s : Nat} {U : Type*}

/-! ## Induction over wires and gate values -/

/-- Induction over the wires of a program in program order: a gate reads only inputs and
earlier gates. -/
theorem wire_induction (p : Program σ n s) {P : Wire n s → Prop}
    (input : ∀ j, P (Wire.input j))
    (gate : ∀ g : Fin s, (∀ w, p.Reads g w → P w) → P (Wire.gate g)) (w : Wire n s) : P w := by
  induction hindex : w.index.val using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    subst hindex
    cases w with
    | input j => exact input j
    | gate g =>
      refine gate g fun w hw => ih _ ?_ w rfl
      simpa using hw.lt

/-- The value of a gate is its operation applied to the values of the wires it reads. -/
theorem trace_gate (p : Program σ n s) (I : Interpretation σ U) (x : Fin n → U) (g : Fin s) :
    p.trace I x (Wire.gate g) = I (p.lines g).op fun a => p.trace I x ((p.lines g).wires a) := by
  rw [Program.trace_gateWire, Program.gateFunction_apply, ← p.lines_eval I x g]
  rfl

/-- Two evaluations agreeing on the wires a gate reads agree on the gate. -/
theorem trace_gate_congr (p : Program σ n s) (I : Interpretation σ U) {x x' : Fin n → U}
    {g : Fin s} (h : ∀ w, p.Reads g w → p.trace I x w = p.trace I x' w) :
    p.trace I x (Wire.gate g) = p.trace I x' (Wire.gate g) := by
  rw [trace_gate, trace_gate]
  congr 1
  funext a
  exact h _ ⟨a, rfl⟩

/-! ## Cut and paste, and determination -/

/-- **Cut and paste.** If two inputs agree on the forward and backward signals of `S`, the
mixed input has the values of the first input on `S` and of the second outside `S`. -/
theorem trace_mix (p : Program σ n s) (I : Interpretation σ U) {S : Finset (Wire n s)}
    {x x' : Fin n → U} (hfwd : ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w)
    (hbwd : ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w) (w : Wire n s) :
    p.trace I (mix S x x') w = if w ∈ S then p.trace I x w else p.trace I x' w := by
  refine wire_induction p (P := fun w =>
      p.trace I (mix S x x') w = if w ∈ S then p.trace I x w else p.trace I x' w)
    (fun j => ?_) (fun g ih => ?_) w
  · simp [mix]
  · by_cases hg : Wire.gate g ∈ S
    · rw [ite_eq_left hg]
      refine trace_gate_congr p I fun w hw => ?_
      rw [ih w hw]
      split_ifs with hwS
      · rfl
      · exact (hbwd w (mem_backward.mpr ⟨hwS, g, hg, hw⟩)).symm
    · rw [ite_eq_right hg]
      refine trace_gate_congr p I fun w hw => ?_
      rw [ih w hw]
      split_ifs with hwS
      · exact hfwd w (mem_forward.mpr ⟨hwS, g, hg, hw⟩)
      · rfl

/-- **Determination.** The inputs placed in `S` and the backward signal values determine every
value on `S`. -/
theorem trace_eq_of_agree_backward (p : Program σ n s) (I : Interpretation σ U)
    {S : Finset (Wire n s)} {x x' : Fin n → U} (hin : ∀ j ∈ inputsIn S, x j = x' j)
    (hbwd : ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w) :
    ∀ w ∈ S, p.trace I x w = p.trace I x' w := by
  intro w
  refine wire_induction p (P := fun w => w ∈ S → p.trace I x w = p.trace I x' w)
    (fun j hj => ?_) (fun g ih hg => ?_) w
  · exact hin j (mem_inputsIn.mpr hj)
  · refine trace_gate_congr p I fun w hw => ?_
    by_cases hwS : w ∈ S
    · exact ih w hw hwS
    · exact hbwd w (mem_backward.mpr ⟨hwS, g, hg, hw⟩)

/-- **Determination outside the cut.** The inputs placed outside `S` and the forward signal
values determine every value outside `S`. -/
theorem trace_eq_of_agree_forward (p : Program σ n s) (I : Interpretation σ U)
    {S : Finset (Wire n s)} {x x' : Fin n → U} (hin : ∀ j, j ∉ inputsIn S → x j = x' j)
    (hfwd : ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w) :
    ∀ w, w ∉ S → p.trace I x w = p.trace I x' w := by
  intro w hw
  refine trace_eq_of_agree_backward p I (S := Sᶜ) (fun j hj => hin j ?_) (fun w hw => hfwd w ?_)
    w (Finset.mem_compl.mpr hw)
  · rwa [inputsIn_compl, Finset.mem_compl] at hj
  · rwa [backward_compl] at hw

/-! ## Boundary keys -/

/-- Equal boundary keys mean agreement on the forward signals. -/
theorem agree_forward_of_boundaryKey_eq {p : Program σ n s} {I : Interpretation σ U}
    {S : Finset (Wire n s)} {x x' : Fin n → U}
    (h : boundaryKey p I S x = boundaryKey p I S x') :
    ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w :=
  fun w hw => congrFun (congrArg Prod.fst h) ⟨w, hw⟩

/-- Equal boundary keys mean agreement on the backward signals. -/
theorem agree_backward_of_boundaryKey_eq {p : Program σ n s} {I : Interpretation σ U}
    {S : Finset (Wire n s)} {x x' : Fin n → U}
    (h : boundaryKey p I S x = boundaryKey p I S x') :
    ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w :=
  fun w hw => congrFun (congrArg Prod.snd h) ⟨w, hw⟩

theorem forward_subset (p : Program σ n s) (S : Finset (Wire n s)) : forward p S ⊆ S :=
  fun _ hw => (mem_forward.mp hw).1

theorem not_mem_of_mem_backward {p : Program σ n s} {S : Finset (Wire n s)} {w : Wire n s}
    (hw : w ∈ backward p S) : w ∉ S :=
  (mem_backward.mp hw).1

/-- Mixing two inputs with equal boundary keys keeps the key. -/
theorem boundaryKey_mix (p : Program σ n s) (I : Interpretation σ U) {S : Finset (Wire n s)}
    {x x' : Fin n → U} (h : boundaryKey p I S x = boundaryKey p I S x') :
    boundaryKey p I S (mix S x x') = boundaryKey p I S x := by
  have hfwd := agree_forward_of_boundaryKey_eq h
  have hbwd := agree_backward_of_boundaryKey_eq h
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change p.trace I (mix S x x') w = p.trace I x w
    rw [trace_mix p I hfwd hbwd, ite_eq_left (forward_subset p S w.2)]
  · change p.trace I (mix S x x') w = p.trace I x w
    rw [trace_mix p I hfwd hbwd, ite_eq_right (not_mem_of_mem_backward w.2)]
    exact (hbwd w w.2).symm

theorem leftPart_eq_iff {S : Finset (Wire n s)} {x x' : Fin n → U} :
    leftPart S x = leftPart S x' ↔ ∀ j ∈ inputsIn S, x j = x' j := by
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact h j j.2

theorem rightPart_eq_iff {S : Finset (Wire n s)} {x x' : Fin n → U} :
    rightPart S x = rightPart S x' ↔ ∀ j, j ∉ inputsIn S → x j = x' j := by
  constructor
  · intro h j hj
    exact congrFun h ⟨j, Finset.mem_compl.mpr hj⟩
  · intro h
    funext j
    exact h j (Finset.mem_compl.mp j.2)

/-- **Left parts and backward values determine the key.** -/
theorem boundaryKey_eq_of_leftPart_eq (p : Program σ n s) (I : Interpretation σ U)
    {S : Finset (Wire n s)} {x x' : Fin n → U} (hl : leftPart S x = leftPart S x')
    (hb : (boundaryKey p I S x).2 = (boundaryKey p I S x').2) :
    boundaryKey p I S x = boundaryKey p I S x' := by
  have hbwd : ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w :=
    fun w hw => congrFun hb ⟨w, hw⟩
  have hS := trace_eq_of_agree_backward p I (leftPart_eq_iff.mp hl) hbwd
  refine Prod.ext (funext fun w => hS w (forward_subset p S w.2)) hb

/-- **Right parts and forward values determine the key.** -/
theorem boundaryKey_eq_of_rightPart_eq (p : Program σ n s) (I : Interpretation σ U)
    {S : Finset (Wire n s)} {x x' : Fin n → U} (hr : rightPart S x = rightPart S x')
    (ha : (boundaryKey p I S x).1 = (boundaryKey p I S x').1) :
    boundaryKey p I S x = boundaryKey p I S x' := by
  have hfwd : ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w :=
    fun w hw => congrFun ha ⟨w, hw⟩
  have hS := trace_eq_of_agree_forward p I (rightPart_eq_iff.mp hr) hfwd
  exact Prod.ext ha (funext fun w => hS w (not_mem_of_mem_backward w.2))

/-! ## Products -/

theorem leftPart_mix (S : Finset (Wire n s)) (x x' : Fin n → U) :
    leftPart S (mix S x x') = leftPart S x := by
  funext j
  simp [leftPart, mix, mem_inputsIn.mp j.2]

theorem rightPart_mix (S : Finset (Wire n s)) (x x' : Fin n → U) :
    rightPart S (mix S x x') = rightPart S x' := by
  funext j
  have : Wire.input j.1 ∉ S := fun h => Finset.mem_compl.mp j.2 (mem_inputsIn.mpr h)
  simp [rightPart, mix, this]

/-- An input is determined by its left and right parts. -/
theorem eq_of_leftPart_eq_of_rightPart_eq {S : Finset (Wire n s)} {x x' : Fin n → U}
    (hl : leftPart S x = leftPart S x') (hr : rightPart S x = rightPart S x') : x = x' := by
  funext j
  by_cases hj : j ∈ inputsIn S
  · exact leftPart_eq_iff.mp hl j hj
  · exact rightPart_eq_iff.mp hr j hj

/-- In a set closed under mixing inputs with equal keys, the inputs with a given key are
closed under mixing. -/
theorem mix_mem_filter [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U) {S : Finset (Wire n s)}
    {Z : Finset (Fin n → U)}
    (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, boundaryKey p I S x = boundaryKey p I S x' → mix S x x' ∈ Z)
    {κ : (↥(forward p S) → U) × (↥(backward p S) → U)} {x x' : Fin n → U}
    (hx : x ∈ Z.filter fun x => boundaryKey p I S x = κ)
    (hx' : x' ∈ Z.filter fun x => boundaryKey p I S x = κ) :
    mix S x x' ∈ Z.filter fun x => boundaryKey p I S x = κ := by
  rw [Finset.mem_filter] at hx hx' ⊢
  have hkey : boundaryKey p I S x = boundaryKey p I S x' := hx.2.trans hx'.2.symm
  exact ⟨hZ x hx.1 x' hx'.1 hkey, (boundaryKey_mix p I hkey).trans hx.2⟩

/-- **Product fibres.** In a set closed under mixing inputs with equal keys, the inputs with a
given key are exactly the products of their left and right parts. -/
theorem card_filter_boundaryKey_eq [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U)
    {S : Finset (Wire n s)} {Z : Finset (Fin n → U)}
    (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, boundaryKey p I S x = boundaryKey p I S x' → mix S x x' ∈ Z)
    (κ : (↥(forward p S) → U) × (↥(backward p S) → U)) :
    (Z.filter fun x => boundaryKey p I S x = κ).card =
      (leftParts p I S Z κ).card * (rightParts p I S Z κ).card := by
  set F := Z.filter fun x => boundaryKey p I S x = κ with hF
  let φ : (Fin n → U) → (↥(inputsIn S) → U) × (↥(inputsIn S)ᶜ → U) :=
    fun x => (leftPart S x, rightPart S x)
  have inj : Function.Injective φ := fun x x' h =>
    eq_of_leftPart_eq_of_rightPart_eq (congrArg Prod.fst h) (congrArg Prod.snd h)
  have himage : F.image φ = leftParts p I S Z κ ×ˢ rightParts p I S Z κ := by
    ext ⟨l, r⟩
    simp only [Finset.mem_image, Finset.mem_product, leftParts, rightParts, φ, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
    · rintro ⟨⟨x, hx, rfl⟩, ⟨x', hx', rfl⟩⟩
      exact ⟨mix S x x', mix_mem_filter p I hZ hx hx', leftPart_mix S x x',
        rightPart_mix S x x'⟩
  rw [← Finset.card_product, ← himage, Finset.card_image_of_injective _ inj]

/-! ## Partition bounds -/

/-- **The left parts partition the left inputs for each backward part.** Summed over the keys
realized in `Z`, the left parts number at most `|U| ^ (i + |B|)`. -/
theorem sum_card_leftParts_le [Fintype U] [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U)
    (S : Finset (Wire n s)) (Z : Finset (Fin n → U)) :
    ∑ κ ∈ Z.image (boundaryKey p I S), (leftParts p I S Z κ).card ≤
      Fintype.card U ^ ((inputsIn S).card + (backward p S).card) := by
  rw [← Finset.card_sigma]
  let ψ : (Σ _ : (↥(forward p S) → U) × (↥(backward p S) → U), ↥(inputsIn S) → U) →
      (↥(inputsIn S) → U) × (↥(backward p S) → U) := fun κl => (κl.2, κl.1.2)
  have inj : Set.InjOn ψ ↑((Z.image (boundaryKey p I S)).sigma (leftParts p I S Z)) := by
    rintro ⟨κ, l⟩ h ⟨κ', l'⟩ h' heq
    rw [Finset.mem_coe, Finset.mem_sigma] at h h'
    simp only [ψ, Prod.mk.injEq] at heq
    obtain ⟨rfl, hb⟩ := heq
    obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp h.2
    obtain ⟨x', hx', hx'l⟩ := Finset.mem_image.mp h'.2
    rw [Finset.mem_filter] at hx hx'
    have hkey := boundaryKey_eq_of_leftPart_eq p I (hxl.trans hx'l.symm)
      (by rw [hx.2, hx'.2, hb])
    rw [hx.2, hx'.2] at hkey
    subst hkey
    rfl
  calc ((Z.image (boundaryKey p I S)).sigma (leftParts p I S Z)).card
      ≤ (Finset.univ : Finset ((↥(inputsIn S) → U) × (↥(backward p S) → U))).card :=
        Finset.card_le_card_of_injOn ψ (fun _ _ => Finset.mem_univ _) inj
    _ = Fintype.card U ^ ((inputsIn S).card + (backward p S).card) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_coe, Fintype.card_coe, pow_add]

/-- **The right parts partition the right inputs for each forward part.** Summed over the keys
realized in `Z`, the right parts number at most `|U| ^ (n - i + |A|)`. -/
theorem sum_card_rightParts_le [Fintype U] [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U)
    (S : Finset (Wire n s)) (Z : Finset (Fin n → U)) :
    ∑ κ ∈ Z.image (boundaryKey p I S), (rightParts p I S Z κ).card ≤
      Fintype.card U ^ (n - (inputsIn S).card + (forward p S).card) := by
  rw [← Finset.card_sigma]
  let ψ : (Σ _ : (↥(forward p S) → U) × (↥(backward p S) → U), ↥(inputsIn S)ᶜ → U) →
      (↥(inputsIn S)ᶜ → U) × (↥(forward p S) → U) := fun κr => (κr.2, κr.1.1)
  have inj : Set.InjOn ψ ↑((Z.image (boundaryKey p I S)).sigma (rightParts p I S Z)) := by
    rintro ⟨κ, r⟩ h ⟨κ', r'⟩ h' heq
    rw [Finset.mem_coe, Finset.mem_sigma] at h h'
    simp only [ψ, Prod.mk.injEq] at heq
    obtain ⟨rfl, ha⟩ := heq
    obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp h.2
    obtain ⟨x', hx', hx'r⟩ := Finset.mem_image.mp h'.2
    rw [Finset.mem_filter] at hx hx'
    have hkey := boundaryKey_eq_of_rightPart_eq p I (hxr.trans hx'r.symm)
      (by rw [hx.2, hx'.2, ha])
    rw [hx.2, hx'.2] at hkey
    subst hkey
    rfl
  calc ((Z.image (boundaryKey p I S)).sigma (rightParts p I S Z)).card
      ≤ (Finset.univ : Finset ((↥(inputsIn S)ᶜ → U) × (↥(forward p S) → U))).card :=
        Finset.card_le_card_of_injOn ψ (fun _ _ => Finset.mem_univ _) inj
    _ = Fintype.card U ^ (n - (inputsIn S).card + (forward p S).card) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_coe, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, pow_add]

/-- There are at most `|U| ^ (|A| + |B|)` boundary keys. -/
theorem card_image_boundaryKey_le [Fintype U] [DecidableEq U] (p : Program σ n s)
    (I : Interpretation σ U) (S : Finset (Wire n s)) (Z : Finset (Fin n → U)) :
    (Z.image (boundaryKey p I S)).card ≤
      Fintype.card U ^ ((forward p S).card + (backward p S).card) := by
  calc (Z.image (boundaryKey p I S)).card
      ≤ Fintype.card ((↥(forward p S) → U) × (↥(backward p S) → U)) := Finset.card_le_univ _
    _ = Fintype.card U ^ ((forward p S).card + (backward p S).card) := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_coe,
          Fintype.card_coe, pow_add]

/-! ## The single-cut criterion -/

/-- Gluing a left part of `x` and a right part of `x'` is mixing them. -/
theorem glue_leftPart_rightPart (S : Finset (Wire n s)) (x x' : Fin n → Bool) :
    glue (inputsIn S) (leftPart S x) (rightPart S x') = mix S x x' := by
  funext j
  by_cases hj : Wire.input j ∈ S
  · have : j ∈ inputsIn S := mem_inputsIn.mpr hj
    simp [glue, mix, leftPart, this, hj]
  · have : j ∉ inputsIn S := fun h => hj (mem_inputsIn.mp h)
    simp [glue, mix, rightPart, this, hj]

/-- A rectangle-free threshold is positive: the empty rectangle has no side below zero. -/
theorem pos_of_rectangleFree {f : Cslib.BooleanFunction n} {K : Nat}
    (hrect : RectangleFree f K) : 0 < K := by
  rcases hrect ∅ ∅ ∅ (by simp) with h | h <;> simpa using h

/-- **The single-cut criterion**, for the function carried by a wire `out`. -/
theorem card_accepting_le_of_trace (p : Program σ n s) (I : Interpretation σ Bool)
    (out : Wire n s) {f : Cslib.BooleanFunction n} (hf : ∀ x, f x = p.trace I x out) {K : Nat}
    (hrect : RectangleFree f K) (S : Finset (Wire n s)) :
    (accepting f).card ≤ (K - 1) * (2 ^ ((inputsIn S).card + (backward p S).card) +
      2 ^ (n - (inputsIn S).card + (forward p S).card)) := by
  set Z := accepting f with hZdef
  -- Mixing two accepted inputs with the same key keeps the output of whichever side holds it.
  have hZ : ∀ x ∈ Z, ∀ x' ∈ Z, boundaryKey p I S x = boundaryKey p I S x' →
      mix S x x' ∈ Z := by
    intro x hx x' hx' hkey
    rw [hZdef, mem_accepting] at hx hx' ⊢
    rw [hf, trace_mix p I (agree_forward_of_boundaryKey_eq hkey)
      (agree_backward_of_boundaryKey_eq hkey)]
    split_ifs
    · rw [← hf]
      exact hx
    · rw [← hf]
      exact hx'
  -- Each key class is a one-rectangle, so one side is below the threshold.
  have fibre : ∀ κ, (Z.filter fun x => boundaryKey p I S x = κ).card ≤
      (K - 1) * ((leftParts p I S Z κ).card + (rightParts p I S Z κ).card) := by
    intro κ
    rw [card_filter_boundaryKey_eq p I hZ κ]
    have rect : ∀ l ∈ leftParts p I S Z κ, ∀ r ∈ rightParts p I S Z κ,
        f (glue (inputsIn S) l r) = true := by
      intro l hl r hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hr
      rw [glue_leftPart_rightPart]
      exact mem_accepting.mp (Finset.mem_filter.mp (mix_mem_filter p I hZ hx hx')).1
    rcases hrect (inputsIn S) _ _ rect with h | h
    · calc (leftParts p I S Z κ).card * (rightParts p I S Z κ).card
          ≤ (K - 1) * (rightParts p I S Z κ).card :=
            Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt h)
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    · calc (leftParts p I S Z κ).card * (rightParts p I S Z κ).card
          ≤ (leftParts p I S Z κ).card * (K - 1) :=
            Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt h)
        _ = (K - 1) * (leftParts p I S Z κ).card := Nat.mul_comm _ _
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hL := sum_card_leftParts_le p I S Z
  have hR := sum_card_rightParts_le p I S Z
  rw [Fintype.card_bool] at hL hR
  calc Z.card
      = ∑ κ ∈ Z.image (boundaryKey p I S),
          (Z.filter fun x => boundaryKey p I S x = κ).card :=
        Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ κ ∈ Z.image (boundaryKey p I S),
          (K - 1) * ((leftParts p I S Z κ).card + (rightParts p I S Z κ).card) :=
        Finset.sum_le_sum fun κ _ => fibre κ
    _ = (K - 1) * (∑ κ ∈ Z.image (boundaryKey p I S), (leftParts p I S Z κ).card +
          ∑ κ ∈ Z.image (boundaryKey p I S), (rightParts p I S Z κ).card) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add hL hR)

/-- The strict form of the single-cut criterion. -/
theorem card_accepting_lt_of_trace (p : Program σ n s) (I : Interpretation σ Bool)
    (out : Wire n s) {f : Cslib.BooleanFunction n} (hf : ∀ x, f x = p.trace I x out) {K : Nat}
    (hrect : RectangleFree f K) (S : Finset (Wire n s)) :
    (accepting f).card < K * (2 ^ ((inputsIn S).card + (backward p S).card) +
      2 ^ (n - (inputsIn S).card + (forward p S).card)) := by
  have hK := pos_of_rectangleFree hrect
  calc (accepting f).card
      ≤ (K - 1) * (2 ^ ((inputsIn S).card + (backward p S).card) +
          2 ^ (n - (inputsIn S).card + (forward p S).card)) :=
        card_accepting_le_of_trace p I out hf hrect S
    _ < K * (2 ^ ((inputsIn S).card + (backward p S).card) +
          2 ^ (n - (inputsIn S).card + (forward p S).card)) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

/-- **The single-cut corollary.** With at least `2 ^ (n - 2)` accepted inputs, one side of
every cut sees at least `n - ⌈log₂ K⌉ - 2` free bits. -/
theorem le_max_add_clog_of_trace (p : Program σ n s) (I : Interpretation σ Bool)
    (out : Wire n s) {f : Cslib.BooleanFunction n} (hf : ∀ x, f x = p.trace I x out) {K : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (S : Finset (Wire n s)) :
    n ≤ max ((inputsIn S).card + (backward p S).card)
      (n - (inputsIn S).card + (forward p S).card) + Nat.clog 2 K + 2 := by
  set a := (inputsIn S).card + (backward p S).card
  set b := n - (inputsIn S).card + (forward p S).card
  have hlt := card_accepting_lt_of_trace p I out hf hrect S
  have ha : 2 ^ a ≤ 2 ^ max a b := Nat.pow_le_pow_right two_pos (le_max_left a b)
  have hb : 2 ^ b ≤ 2 ^ max a b := Nat.pow_le_pow_right two_pos (le_max_right a b)
  have hK : K ≤ 2 ^ Nat.clog 2 K := Nat.le_pow_clog one_lt_two K
  have hpow : 2 ^ (n - 2) < 2 ^ (Nat.clog 2 K + max a b + 1) :=
    calc 2 ^ (n - 2) ≤ (accepting f).card := hacc
      _ < K * (2 ^ a + 2 ^ b) := hlt
      _ ≤ 2 ^ Nat.clog 2 K * (2 * 2 ^ max a b) := Nat.mul_le_mul hK (by omega)
      _ = 2 ^ (Nat.clog 2 K + max a b + 1) := by ring
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  omega

/-- The real-logarithm form of the single-cut corollary. -/
theorem sub_logb_lt_max_of_trace (p : Program σ n s) (I : Interpretation σ Bool)
    (out : Wire n s) {f : Cslib.BooleanFunction n} (hf : ∀ x, f x = p.trace I x out) {K : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (S : Finset (Wire n s)) :
    (n : ℝ) - Real.logb 2 K - 3 < (max ((inputsIn S).card + (backward p S).card)
      (n - (inputsIn S).card + (forward p S).card) : Nat) := by
  have hnat := le_max_add_clog_of_trace p I out hf hrect hacc S
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast pos_of_rectangleFree hrect
  have hlog : 0 ≤ Real.logb 2 K := Real.logb_nonneg one_lt_two hK
  have hclog : (Nat.clog 2 K : ℝ) < Real.logb 2 K + 1 := by
    rw [← Real.natCeil_logb_natCast 2 K]
    exact_mod_cast Nat.ceil_lt_add_one hlog
  have hcast : (n : ℝ) ≤ ((max ((inputsIn S).card + (backward p S).card)
      (n - (inputsIn S).card + (forward p S).card) : Nat) : ℝ) + Nat.clog 2 K + 2 := by
    exact_mod_cast hnat
  linarith

/-! ## Circuits and orderings -/

/-- A single-output circuit computing `f` carries `f` on its output wire. -/
theorem eq_trace_of_computes {c : Circuit σ n 1} {I : Interpretation σ Bool}
    {f : Cslib.BooleanFunction n} (hc : c.Computes I fun x _ => f x) (x : Fin n → Bool) :
    f x = c.program.trace I x (c.outputs 0) :=
  (congrFun (hc x) 0).symm

/-- One side of a cut sees at most `max i (n - i)` inputs plus all crossing signals. -/
theorem max_le_max_add (i n a b : Nat) :
    max (i + b) (n - i + a) ≤ max i (n - i) + a + b := by
  omega

/-- A monotone step function from `0` that reaches `h` takes the value `h`. -/
theorem exists_eq_of_succ_le (g : Nat → Nat) (h : Nat) (hzero : g 0 = 0)
    (hstep : ∀ t, g (t + 1) ≤ g t + 1) (M : Nat) (hM : h ≤ g M) : ∃ t, g t = h := by
  induction M with
  | zero => exact ⟨0, by omega⟩
  | succ M ih =>
    by_cases hlt : h ≤ g M
    · exact ih hlt
    · exact ⟨M + 1, by have := hstep M; omega⟩

/-- The prefix of the wires ranked below `t`. -/
abbrev prefixBelow (rank : Wire n s → Nat) (t : Nat) : Finset (Wire n s) :=
  Finset.univ.filter fun w => rank w < t

/-- **Prefixes take every input count.** For an injective ranking of the wires, some prefix
contains exactly `h` inputs, for every `h ≤ n`. -/
theorem exists_card_inputsIn_prefixBelow_eq (rank : Wire n s → Nat)
    (hrank : Function.Injective rank) {h : Nat} (hh : h ≤ n) :
    ∃ t, (inputsIn (prefixBelow rank t)).card = h := by
  refine exists_eq_of_succ_le (fun t => (inputsIn (prefixBelow rank t)).card) h ?_ ?_
    ((Finset.univ.sup rank) + 1) ?_
  · simp [inputsIn, prefixBelow]
  · intro t
    have hsub : inputsIn (prefixBelow rank (t + 1)) ⊆
        inputsIn (prefixBelow rank t) ∪ Finset.univ.filter fun j => rank (Wire.input j) = t := by
      intro j hj
      simp only [mem_inputsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_union, mem_inputsIn, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hone : (Finset.univ.filter fun j : Fin n => rank (Wire.input j) = t).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hab := hrank (ha.trans hb.symm)
      injection hab
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left hone _))
  · have hall : prefixBelow rank ((Finset.univ.sup rank) + 1) = Finset.univ := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ w))
    have : inputsIn (Finset.univ : Finset (Wire n s)) = Finset.univ := by
      ext j
      simp [mem_inputsIn]
    simp only [hall, this, Finset.card_univ, Fintype.card_fin]
    exact hh

/-- **Every ordering has a heavily crossed prefix**, for the function carried by a wire. -/
theorem exists_prefix_le_of_trace (p : Program σ n s) (I : Interpretation σ Bool)
    (out : Wire n s) {f : Cslib.BooleanFunction n} (hf : ∀ x, f x = p.trace I x out) {K : Nat}
    (hrect : RectangleFree f K) (hacc : 2 ^ (n - 2) ≤ (accepting f).card)
    (rank : Wire n s → Nat) (hrank : Function.Injective rank) :
    ∃ t : Nat, n / 2 ≤ (forward p (prefixBelow rank t)).card +
      (backward p (prefixBelow rank t)).card + Nat.clog 2 K + 2 := by
  obtain ⟨t, ht⟩ := exists_card_inputsIn_prefixBelow_eq rank hrank (Nat.div_le_self n 2)
  refine ⟨t, ?_⟩
  have h := le_max_add_clog_of_trace p I out hf hrect hacc (prefixBelow rank t)
  have hmax := max_le_max_add (inputsIn (prefixBelow rank t)).card n
    (forward p (prefixBelow rank t)).card (backward p (prefixBelow rank t)).card
  rw [ht] at h hmax
  omega

end Algebraic.Cutwidth.SingleCut.Internal

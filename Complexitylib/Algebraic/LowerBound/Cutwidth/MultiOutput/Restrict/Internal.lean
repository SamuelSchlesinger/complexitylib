/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Restrict.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut

/-!
# Proofs for restricted splits

The fibre bound of `MultiOutput.Rank` sums over all inputs. Its proof only mixes inputs with
equal boundary keys, so it holds for any set `Z` of inputs closed under mixing
(`card_le_of_fibres_of_mix`): the members of `Z` with a fixed key are a product of left and
right parts, and the left parts embed into the left fibre of any member taken within `Z`.
Coordinatewise products are closed under mixing (`mix_mem_piFinset`), and so is the *slice*
of inputs agreeing with a base point `z₀` off a set `J` of free coordinates (`slice`).

On a slice, if the function changes by `g d` when the input changes by `d`, a left fibre minus
its base point consists of vectors supported on the free inputs placed in `S` whose image
vanishes on the outputs carried outside `S` (`card_inter_leftFibre_le`). As the slice has
`|U| ^ |J|` members (`card_slice`), this gives `card_pow_le_supportedKernel`. For a closed set
both kernels must then be full, so `g` maps vectors supported on one side to vectors vanishing
on the outputs of the other side (`apply_eq_zero_of_closed`).
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Internal

open SingleCut

variable {σ : Signature} {n s m : Nat} {U : Type*}

/-! ## The fibre bound on a set closed under mixing -/

section Mix

variable [Fintype U] [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U)
  (out : Fin m → Wire n s) (f : (Fin n → U) → Fin m → U)
  (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) {Z : Finset (Fin n → U)}

include hf in
/-- The left parts of a fibre within `Z` embed into the left fibre, within `Z`, of any of its
members. -/
theorem card_leftParts_le_inter (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, mix S x x' ∈ Z) {x₀ : Fin n → U}
    (hx₀ : x₀ ∈ Z) :
    (leftParts p I S Z (boundaryKey p I S x₀)).card ≤ (Z ∩ leftFibre out f S x₀).card := by
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_image_le (s := Z ∩ leftFibre out f S x₀) (f := leftPart S))
  intro l hl
  simp only [leftParts, Finset.mem_image, Finset.mem_filter] at hl
  obtain ⟨x, ⟨hxZ, hx⟩, rfl⟩ := hl
  refine Finset.mem_image.mpr ⟨mix S x x₀, Finset.mem_inter.mpr ⟨hZ x hxZ x₀ hx₀, ?_⟩,
    leftPart_mix x x₀⟩
  simp only [leftFibre, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfwd := agree_forward_of_boundaryKey_eq hx
  have hbwd := agree_backward_of_boundaryKey_eq hx
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · simp only [mix]
    rw [ite_eq_right fun h => hj (mem_inputsIn.mpr h)]
  · have hout : out i ∉ S := by simpa [outputsIn] using hi
    rw [← hf, ← hf, trace_mix p I hfwd hbwd, ite_eq_right hout]

include hf in
/-- The right parts of a fibre within `Z` embed into the right fibre, within `Z`, of any of its
members. -/
theorem card_rightParts_le_inter (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, mix S x x' ∈ Z) {x₀ : Fin n → U}
    (hx₀ : x₀ ∈ Z) :
    (rightParts p I S Z (boundaryKey p I S x₀)).card ≤ (Z ∩ rightFibre out f S x₀).card := by
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_image_le (s := Z ∩ rightFibre out f S x₀) (f := rightPart S))
  intro r hr
  simp only [rightParts, Finset.mem_image, Finset.mem_filter] at hr
  obtain ⟨x, ⟨hxZ, hx⟩, rfl⟩ := hr
  refine Finset.mem_image.mpr ⟨mix S x₀ x, Finset.mem_inter.mpr ⟨hZ x₀ hx₀ x hxZ, ?_⟩,
    rightPart_mix x₀ x⟩
  simp only [rightFibre, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfwd := agree_forward_of_boundaryKey_eq hx.symm
  have hbwd := agree_backward_of_boundaryKey_eq hx.symm
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · simp only [mix]
    rw [ite_eq_left (mem_inputsIn.mp hj)]
  · have hout : out i ∈ S := by simpa [outputsIn] using hi
    rw [← hf, ← hf, trace_mix p I hfwd hbwd, ite_eq_left hout]

include hf in
/-- **The fibre bound on a set closed under mixing.** If `Z` is closed under mixing, every
left fibre within `Z` has at most `DT` elements and every right fibre within `Z` at most `DS`,
then `|Z| ≤ |U| ^ (|A| + |B|) · DT · DS`. -/
theorem card_le_of_fibres_of_mix (hZ : ∀ x ∈ Z, ∀ x' ∈ Z, mix S x x' ∈ Z) {DT DS : Nat}
    (hT : ∀ x ∈ Z, (Z ∩ leftFibre out f S x).card ≤ DT)
    (hS : ∀ x ∈ Z, (Z ∩ rightFibre out f S x).card ≤ DS) :
    Z.card ≤ Fintype.card U ^ ((forward p S).card + (backward p S).card) * (DT * DS) := by
  have hZ' : ∀ x ∈ Z, ∀ x' ∈ Z, boundaryKey p I S x = boundaryKey p I S x' →
      mix S x x' ∈ Z := fun x hx x' hx' _ => hZ x hx x' hx'
  calc Z.card = ∑ κ ∈ Z.image (boundaryKey p I S),
          (Z.filter fun x => boundaryKey p I S x = κ).card :=
        Finset.card_eq_sum_card_image _ _
    _ = ∑ κ ∈ Z.image (boundaryKey p I S),
          (leftParts p I S Z κ).card * (rightParts p I S Z κ).card :=
        Finset.sum_congr rfl fun κ _ => card_filter_boundaryKey_eq p I hZ' κ
    _ ≤ ∑ _κ ∈ Z.image (boundaryKey p I S), DT * DS := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hκ
        exact Nat.mul_le_mul ((card_leftParts_le_inter p I out f hf S hZ hx₀).trans (hT x₀ hx₀))
          ((card_rightParts_le_inter p I out f hf S hZ hx₀).trans (hS x₀ hx₀))
    _ = (Z.image (boundaryKey p I S)).card * (DT * DS) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card U ^ ((forward p S).card + (backward p S).card) * (DT * DS) :=
        Nat.mul_le_mul_right _ (card_image_boundaryKey_le p I S Z)

omit [Fintype U] [DecidableEq U] in
/-- Coordinatewise products are closed under mixing. -/
theorem mix_mem_piFinset (D : Fin n → Finset U) {x x' : Fin n → U}
    (hx : x ∈ Fintype.piFinset D) (hx' : x' ∈ Fintype.piFinset D) :
    mix S x x' ∈ Fintype.piFinset D := by
  rw [Fintype.mem_piFinset] at hx hx' ⊢
  intro j
  simp only [mix]
  split_ifs
  · exact hx j
  · exact hx' j

end Mix

/-! ## Slices -/

section Slice

variable [Fintype U] [DecidableEq U]

/-- The inputs agreeing with `z₀` on every coordinate outside `J`. -/
def slice (J : Finset (Fin n)) (z₀ : Fin n → U) : Finset (Fin n → U) :=
  Finset.univ.filter fun z => ∀ k, k ∉ J → z k = z₀ k

theorem mem_slice {J : Finset (Fin n)} {z₀ z : Fin n → U} :
    z ∈ slice J z₀ ↔ ∀ k, k ∉ J → z k = z₀ k := by
  simp [slice]

/-- A slice has `|U| ^ |J|` members. -/
theorem card_slice (J : Finset (Fin n)) (z₀ : Fin n → U) :
    (slice J z₀).card = Fintype.card U ^ J.card := by
  have h : slice J z₀ = Fintype.piFinset fun k => if k ∈ J then Finset.univ else {z₀ k} := by
    ext z
    simp only [mem_slice, Fintype.mem_piFinset]
    refine forall_congr' fun k => ?_
    by_cases hk : k ∈ J <;> simp [hk]
  have hcard : ∀ k, (if k ∈ J then (Finset.univ : Finset U) else {z₀ k}).card =
      if k ∈ J then Fintype.card U else 1 := fun k => by
    split_ifs <;> simp
  rw [h, Fintype.card_piFinset]
  simp_rw [hcard]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- Slices are closed under mixing. -/
theorem mix_mem_slice {s : Nat} (S : Finset (Wire n s)) {J : Finset (Fin n)} {z₀ x x' : Fin n → U}
    (hx : x ∈ slice J z₀) (hx' : x' ∈ slice J z₀) : mix S x x' ∈ slice J z₀ := by
  rw [mem_slice] at hx hx' ⊢
  intro k hk
  simp only [mix]
  split_ifs
  · exact hx k hk
  · exact hx' k hk

/-- The two sides of a split partition the free coordinates. -/
theorem card_inter_add_card_compl_inter (X J : Finset (Fin n)) :
    (X ∩ J).card + (Xᶜ ∩ J).card = J.card := by
  rw [Finset.inter_comm X J, Finset.inter_comm Xᶜ J, ← Finset.sdiff_eq_inter_compl,
    Finset.card_inter_add_card_sdiff]

/-- If `h` determines `g` on `Z`, then `Z` has at most as many `g`-images as `h`-images. -/
theorem card_image_le_of_eq_on {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (Z : Finset α) (g : α → β) (h : α → γ)
    (hgh : ∀ x ∈ Z, ∀ x' ∈ Z, h x = h x' → g x = g x') :
    (Z.image g).card ≤ (Z.image h).card := by
  classical
  have hm : ∀ y : ↥(Z.image g), ∃ x ∈ Z, g x = y.1 := fun y => Finset.mem_image.mp y.2
  let φ : ↥(Z.image g) → ↥(Z.image h) := fun y =>
    ⟨h (Classical.choose (hm y)), Finset.mem_image_of_mem h (Classical.choose_spec (hm y)).1⟩
  have hinj : Function.Injective φ := by
    intro y₁ y₂ heq
    have h₁ := Classical.choose_spec (hm y₁)
    have h₂ := Classical.choose_spec (hm y₂)
    exact Subtype.ext
      (h₁.2.symm.trans ((hgh _ h₁.1 _ h₂.1 (Subtype.ext_iff.mp heq)).trans h₂.2))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective φ hinj

/-- Monotonicity of slices in the set of free coordinates. -/
theorem slice_subset_slice {J₁ J₂ : Finset (Fin n)} (hJ : J₁ ⊆ J₂) (z₀ : Fin n → U) :
    slice J₁ z₀ ⊆ slice J₂ z₀ := by
  intro z hz
  rw [mem_slice] at hz ⊢
  exact fun k hk => hz k fun hk₁ => hk (hJ hk₁)

/-- **One-sided forward image bound on a slice.** Fixing the coordinates outside `inputsIn S` to
`z₀`, the outputs outside `S` are determined by the forward signals of `S`, so they take at most
`|U| ^ |forward p S|` values. -/
theorem card_image_restrict_compl_le_forward (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) (f : (Fin n → U) → Fin m → U)
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (z₀ : Fin n → U) :
    ((slice (inputsIn S) z₀).image (fun x (i : ↥(outputsIn out S)ᶜ) => f x i.1)).card ≤
      Fintype.card U ^ (forward p S).card := by
  have hle := card_image_le_of_eq_on (slice (inputsIn S) z₀)
    (fun x (i : ↥(outputsIn out S)ᶜ) => f x i.1) (fun x => (boundaryKey p I S x).1)
    fun x hx x' hx' hkey => by
      funext i
      have hin : ∀ j, j ∉ inputsIn S → x j = x' j := fun j hj => by
        rw [mem_slice.mp hx j hj, mem_slice.mp hx' j hj]
      have hfwd : ∀ w ∈ forward p S, p.trace I x w = p.trace I x' w :=
        fun w hw => congrFun hkey ⟨w, hw⟩
      have hout : out i.1 ∉ S := by simpa [outputsIn] using Finset.mem_compl.mp i.2
      rw [← hf, ← hf]
      exact trace_eq_of_agree_forward p I hin hfwd (out i.1) hout
  refine hle.trans ?_
  calc ((slice (inputsIn S) z₀).image (fun x => (boundaryKey p I S x).1)).card
      ≤ Fintype.card (↥(forward p S) → U) := Finset.card_le_univ _
    _ = Fintype.card U ^ (forward p S).card := by rw [Fintype.card_fun, Fintype.card_coe]

/-- **One-sided backward image bound on a slice.** Fixing the coordinates in `inputsIn S` to `z₀`,
the outputs in `S` are determined by the backward signals of `S`, so they take at most
`|U| ^ |backward p S|` values. -/
theorem card_image_restrict_le_backward (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) (f : (Fin n → U) → Fin m → U)
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (z₀ : Fin n → U) :
    ((slice (inputsIn S)ᶜ z₀).image (fun x (i : ↥(outputsIn out S)) => f x i.1)).card ≤
      Fintype.card U ^ (backward p S).card := by
  have hle := card_image_le_of_eq_on (slice (inputsIn S)ᶜ z₀)
    (fun x (i : ↥(outputsIn out S)) => f x i.1) (fun x => (boundaryKey p I S x).2)
    fun x hx x' hx' hkey => by
      funext i
      have hin : ∀ j ∈ inputsIn S, x j = x' j := fun j hj => by
        have hj' : j ∉ (inputsIn S)ᶜ := by simpa using hj
        rw [mem_slice.mp hx j hj', mem_slice.mp hx' j hj']
      have hbwd : ∀ w ∈ backward p S, p.trace I x w = p.trace I x' w :=
        fun w hw => congrFun hkey ⟨w, hw⟩
      have hout : out i.1 ∈ S := by simpa [outputsIn] using i.2
      rw [← hf, ← hf]
      exact trace_eq_of_agree_backward p I hin hbwd (out i.1) hout
  refine hle.trans ?_
  calc ((slice (inputsIn S)ᶜ z₀).image (fun x => (boundaryKey p I S x).2)).card
      ≤ Fintype.card (↥(backward p S) → U) := Finset.card_le_univ _
    _ = Fintype.card U ^ (backward p S).card := by rw [Fintype.card_fun, Fintype.card_coe]

/-- **One-sided forward fibre bound on a slice.** On the slice of inputs agreeing with `z₀`
outside `J`, if every left fibre within `slice J z₀` has at most `DT` elements, then
`|U| ^ |inputsIn S ∩ J| ≤ |U| ^ |forward p S| · DT`. -/
theorem card_pow_inter_le_forward_of_leftFibre (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) (f : (Fin n → U) → Fin m → U)
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) {DT : Nat}
    (hT : ∀ x ∈ slice J z₀, (slice J z₀ ∩ leftFibre out f S x).card ≤ DT) :
    Fintype.card U ^ (inputsIn S ∩ J).card ≤ Fintype.card U ^ (forward p S).card * DT := by
  set Z := slice (inputsIn S ∩ J) z₀
  have hsub : Z ⊆ slice J z₀ := slice_subset_slice Finset.inter_subset_right z₀
  calc Fintype.card U ^ (inputsIn S ∩ J).card
      = Z.card := (card_slice _ _).symm
    _ = ∑ κ ∈ Z.image (fun x => (boundaryKey p I S x).1),
          (Z.filter fun x => (boundaryKey p I S x).1 = κ).card :=
        Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _κ ∈ Z.image (fun x => (boundaryKey p I S x).1), DT := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hκ
        refine (Finset.card_le_card ?_).trans (hT x₀ (hsub hx₀))
        intro x hx
        rw [Finset.mem_filter] at hx
        refine Finset.mem_inter.mpr ⟨hsub hx.1, ?_⟩
        simp only [leftFibre, Finset.mem_filter, Finset.mem_univ, true_and]
        have hin : ∀ j, j ∉ inputsIn S → x j = x₀ j := fun j hj => by
          have hj' : j ∉ inputsIn S ∩ J := fun h => hj (Finset.mem_of_mem_inter_left h)
          rw [mem_slice.mp hx.1 j hj', mem_slice.mp hx₀ j hj']
        have hfwd : ∀ w ∈ forward p S, p.trace I x w = p.trace I x₀ w :=
          fun w hw => congrFun hx.2 ⟨w, hw⟩
        refine ⟨hin, fun i hi => ?_⟩
        have hout : out i ∉ S := by simpa [outputsIn] using hi
        rw [← hf, ← hf]
        exact trace_eq_of_agree_forward p I hin hfwd (out i) hout
    _ = (Z.image (fun x => (boundaryKey p I S x).1)).card * DT := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card U ^ (forward p S).card * DT := by
        refine Nat.mul_le_mul_right _ ?_
        calc (Z.image (fun x => (boundaryKey p I S x).1)).card
            ≤ Fintype.card (↥(forward p S) → U) := Finset.card_le_univ _
          _ = Fintype.card U ^ (forward p S).card := by rw [Fintype.card_fun, Fintype.card_coe]

/-- **One-sided backward fibre bound on a slice.** On the slice of inputs agreeing with `z₀`
outside `J`, if every right fibre within `slice J z₀` has at most `DS` elements, then
`|U| ^ |(inputsIn S)ᶜ ∩ J| ≤ |U| ^ |backward p S| · DS`. -/
theorem card_pow_compl_inter_le_backward_of_rightFibre (p : Program σ n s) (I : Interpretation σ U)
    (out : Fin m → Wire n s) (f : (Fin n → U) → Fin m → U)
    (hf : ∀ x i, p.trace I x (out i) = f x i) (S : Finset (Wire n s)) (J : Finset (Fin n))
    (z₀ : Fin n → U) {DS : Nat}
    (hS : ∀ x ∈ slice J z₀, (slice J z₀ ∩ rightFibre out f S x).card ≤ DS) :
    Fintype.card U ^ ((inputsIn S)ᶜ ∩ J).card ≤ Fintype.card U ^ (backward p S).card * DS := by
  set Z := slice ((inputsIn S)ᶜ ∩ J) z₀
  have hsub : Z ⊆ slice J z₀ := slice_subset_slice Finset.inter_subset_right z₀
  calc Fintype.card U ^ ((inputsIn S)ᶜ ∩ J).card
      = Z.card := (card_slice _ _).symm
    _ = ∑ κ ∈ Z.image (fun x => (boundaryKey p I S x).2),
          (Z.filter fun x => (boundaryKey p I S x).2 = κ).card :=
        Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _κ ∈ Z.image (fun x => (boundaryKey p I S x).2), DS := by
        refine Finset.sum_le_sum fun κ hκ => ?_
        obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hκ
        refine (Finset.card_le_card ?_).trans (hS x₀ (hsub hx₀))
        intro x hx
        rw [Finset.mem_filter] at hx
        refine Finset.mem_inter.mpr ⟨hsub hx.1, ?_⟩
        simp only [rightFibre, Finset.mem_filter, Finset.mem_univ, true_and]
        have hin : ∀ j ∈ inputsIn S, x j = x₀ j := fun j hj => by
          have hj' : j ∉ (inputsIn S)ᶜ ∩ J :=
            fun h => (Finset.mem_compl.mp (Finset.mem_of_mem_inter_left h)) hj
          rw [mem_slice.mp hx.1 j hj', mem_slice.mp hx₀ j hj']
        have hbwd : ∀ w ∈ backward p S, p.trace I x w = p.trace I x₀ w :=
          fun w hw => congrFun hx.2 ⟨w, hw⟩
        refine ⟨hin, fun i hi => ?_⟩
        have hout : out i ∈ S := by simpa [outputsIn] using hi
        rw [← hf, ← hf]
        exact trace_eq_of_agree_backward p I hin hbwd (out i) hout
    _ = (Z.image (fun x => (boundaryKey p I S x).2)).card * DS := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card U ^ (backward p S).card * DS := by
        refine Nat.mul_le_mul_right _ ?_
        calc (Z.image (fun x => (boundaryKey p I S x).2)).card
            ≤ Fintype.card (↥(backward p S) → U) := Finset.card_le_univ _
          _ = Fintype.card U ^ (backward p S).card := by rw [Fintype.card_fun, Fintype.card_coe]

end Slice

/-! ## Kernels on a slice -/

section Kernel

variable [AddCommGroup U] [Fintype U] [DecidableEq U]

/-- Kernel vectors are supported vectors, so there are at most `|U| ^ |P|` of them. -/
theorem supportedKernel_subset_slice (g : (Fin n → U) → Fin m → U) (P : Finset (Fin n))
    (Q : Finset (Fin m)) : supportedKernel g P Q ⊆ slice P 0 := by
  intro d hd
  simp only [supportedKernel, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  exact mem_slice.mpr fun k hk => hd.1 k hk

theorem card_supportedKernel_le (g : (Fin n → U) → Fin m → U) (P : Finset (Fin n))
    (Q : Finset (Fin m)) : (supportedKernel g P Q).card ≤ Fintype.card U ^ P.card := by
  rw [← card_slice P 0]
  exact Finset.card_le_card (supportedKernel_subset_slice g P Q)

/-- A supported vector whose image does not vanish on `Q` leaves the kernel short. -/
theorem card_supportedKernel_lt (g : (Fin n → U) → Fin m → U) {P : Finset (Fin n)}
    {Q : Finset (Fin m)} {d : Fin n → U} (hd : ∀ k, k ∉ P → d k = 0) {i : Fin m} (hi : i ∈ Q)
    (hgd : g d i ≠ 0) : (supportedKernel g P Q).card < Fintype.card U ^ P.card := by
  rw [← card_slice P 0]
  refine Finset.card_lt_card ⟨supportedKernel_subset_slice g P Q, fun h => ?_⟩
  have := h (mem_slice.mpr hd)
  simp only [supportedKernel, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact hgd (this.2 i hi)

variable {p : Program σ n s} {out : Fin m → Wire n s} {f : (Fin n → U) → Fin m → U}
  {S : Finset (Wire n s)} {J : Finset (Fin n)} {z₀ : Fin n → U} {g : (Fin n → U) → Fin m → U}

/-- **Left fibres on a slice.** Subtracting the base point maps a left fibre within the slice
injectively into the vectors supported on the free inputs in `S` whose image vanishes on the
outputs carried outside `S`. -/
theorem card_inter_leftFibre_le
    (hg : ∀ z ∈ slice J z₀, ∀ z' ∈ slice J z₀, f z' - f z = g (z' - z)) {x : Fin n → U}
    (hx : x ∈ slice J z₀) :
    (slice J z₀ ∩ leftFibre out f S x).card ≤
      (supportedKernel g (inputsIn S ∩ J) (outputsIn out S)ᶜ).card := by
  refine Finset.card_le_card_of_injOn (fun z' => z' - x) ?_ ?_
  · intro z' hz'
    rw [Finset.mem_coe, Finset.mem_inter] at hz'
    obtain ⟨hz'Z, hz'F⟩ := hz'
    simp only [leftFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hz'F
    simp only [Finset.mem_coe, supportedKernel, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun k hk => ?_, fun i hi => ?_⟩
    · rw [Finset.mem_inter, not_and_or] at hk
      rcases hk with hk | hk
      · simp [hz'F.1 k hk]
      · simp [mem_slice.mp hz'Z k hk, mem_slice.mp hx k hk]
    · rw [← hg x hx z' hz'Z]
      simp [hz'F.2 i (Finset.mem_compl.mp hi)]
  · intro z' _ z'' _ h
    exact sub_left_injective h

/-- **Right fibres on a slice.** -/
theorem card_inter_rightFibre_le
    (hg : ∀ z ∈ slice J z₀, ∀ z' ∈ slice J z₀, f z' - f z = g (z' - z)) {x : Fin n → U}
    (hx : x ∈ slice J z₀) :
    (slice J z₀ ∩ rightFibre out f S x).card ≤
      (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn out S)).card := by
  refine Finset.card_le_card_of_injOn (fun z' => z' - x) ?_ ?_
  · intro z' hz'
    rw [Finset.mem_coe, Finset.mem_inter] at hz'
    obtain ⟨hz'Z, hz'F⟩ := hz'
    simp only [rightFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hz'F
    simp only [Finset.mem_coe, supportedKernel, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun k hk => ?_, fun i hi => ?_⟩
    · rw [Finset.mem_inter, not_and_or, Finset.mem_compl, not_not] at hk
      rcases hk with hk | hk
      · simp [hz'F.1 k hk]
      · simp [mem_slice.mp hz'Z k hk, mem_slice.mp hx k hk]
    · rw [← hg x hx z' hz'Z]
      simp [hz'F.2 i hi]
  · intro z' _ z'' _ h
    exact sub_left_injective h

variable (p) (I : Interpretation σ U) (out) (f)

/-- **The one-sided forward kernel bound on a slice.** If the wires `out` carry `f`, and on the
slice of inputs agreeing with `z₀` off `J` the function changes by `g d` when its input changes
by `d`, then every split `S` satisfies
`|U| ^ |inputsIn S ∩ J| ≤ |U| ^ |forward p S| · |supportedKernel g (inputsIn S ∩ J) Y_T|`. -/
theorem card_pow_le_supportedKernel_forward (hf : ∀ x i, p.trace I x (out i) = f x i)
    (S : Finset (Wire n s)) (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ (inputsIn S ∩ J).card ≤
      Fintype.card U ^ (forward p S).card *
        (supportedKernel g (inputsIn S ∩ J) (outputsIn out S)ᶜ).card := by
  have hg' : ∀ z ∈ slice J z₀, ∀ z' ∈ slice J z₀, f z' - f z = g (z' - z) :=
    fun z hz z' hz' => hg z z' (mem_slice.mp hz) (mem_slice.mp hz')
  exact card_pow_inter_le_forward_of_leftFibre p I out f hf S J z₀
    fun x hx => card_inter_leftFibre_le hg' hx

/-- **The one-sided backward kernel bound on a slice.** Symmetrically,
`|U| ^ |(inputsIn S)ᶜ ∩ J| ≤ |U| ^ |backward p S| · |supportedKernel g ((inputsIn S)ᶜ ∩ J) Y_S|`. -/
theorem card_pow_le_supportedKernel_backward (hf : ∀ x i, p.trace I x (out i) = f x i)
    (S : Finset (Wire n s)) (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ ((inputsIn S)ᶜ ∩ J).card ≤
      Fintype.card U ^ (backward p S).card *
        (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn out S)).card := by
  have hg' : ∀ z ∈ slice J z₀, ∀ z' ∈ slice J z₀, f z' - f z = g (z' - z) :=
    fun z hz z' hz' => hg z z' (mem_slice.mp hz) (mem_slice.mp hz')
  exact card_pow_compl_inter_le_backward_of_rightFibre p I out f hf S J z₀
    fun x hx => card_inter_rightFibre_le hg' hx

/-- **The kernel form of the restricted rank-cut bound.** If the wires `out` carry `f`, and on
the slice of inputs agreeing with `z₀` off `J` the function changes by `g d` when its input
changes by `d`, then every split satisfies
`|U| ^ |J| ≤ |U| ^ (|A| + |B|) · |ker₁| · |ker₂|`, where `ker₁` consists of the vectors
supported on the free inputs in `S` whose image vanishes on the outputs outside `S`, and
`ker₂` symmetrically. -/
theorem card_pow_le_supportedKernel (hf : ∀ x i, p.trace I x (out i) = f x i)
    (S : Finset (Wire n s)) (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z)) :
    Fintype.card U ^ J.card ≤
      Fintype.card U ^ ((forward p S).card + (backward p S).card) *
        ((supportedKernel g (inputsIn S ∩ J) (outputsIn out S)ᶜ).card *
          (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn out S)).card) := by
  have h₁ := card_pow_le_supportedKernel_forward p out f I hf S J z₀ g hg
  have h₂ := card_pow_le_supportedKernel_backward p out f I hf S J z₀ g hg
  calc Fintype.card U ^ J.card
      = Fintype.card U ^ (inputsIn S ∩ J).card * Fintype.card U ^ ((inputsIn S)ᶜ ∩ J).card := by
        rw [← pow_add, card_inter_add_card_compl_inter]
    _ ≤ (Fintype.card U ^ (forward p S).card *
          (supportedKernel g (inputsIn S ∩ J) (outputsIn out S)ᶜ).card) *
        (Fintype.card U ^ (backward p S).card *
          (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn out S)).card) :=
        Nat.mul_le_mul h₁ h₂
    _ = Fintype.card U ^ ((forward p S).card + (backward p S).card) *
          ((supportedKernel g (inputsIn S ∩ J) (outputsIn out S)ᶜ).card *
            (supportedKernel g ((inputsIn S)ᶜ ∩ J) (outputsIn out S)).card) := by
        rw [pow_add]
        ring

omit [Fintype U] [DecidableEq U] in
/-- **No forward signals separate.** If `forward p S = ∅`, then `g` maps vectors supported on
the free inputs in `S` to vectors vanishing on the outputs carried outside `S`. -/
theorem apply_eq_zero_of_forward_eq_empty (hf : ∀ x i, p.trace I x (out i) = f x i)
    (S : Finset (Wire n s)) (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z))
    (hfwd : forward p S = ∅) {d : Fin n → U} (hd : ∀ k, k ∉ inputsIn S ∩ J → d k = 0)
    {i : Fin m} (hi : i ∉ outputsIn out S) : g d i = 0 := by
  have hz₀ : ∀ k, k ∉ J → z₀ k = z₀ k := fun _ _ => rfl
  have hzd : ∀ k, k ∉ J → (z₀ + d) k = z₀ k := fun k hk => by
    simp [hd k fun h => hk (Finset.mem_of_mem_inter_right h)]
  have hin : ∀ j, j ∉ inputsIn S → (z₀ + d) j = z₀ j := fun j hj => by
    simp [hd j fun h => hj (Finset.mem_of_mem_inter_left h)]
  have htr := trace_eq_of_agree_forward p I hin
    (fun w hw => False.elim (Finset.notMem_empty w (hfwd ▸ hw))) (out i)
    (by simpa [outputsIn] using hi)
  have hsub := congrFun (hg z₀ (z₀ + d) hz₀ hzd) i
  rw [add_sub_cancel_left, Pi.sub_apply, ← hf, ← hf, htr, sub_self] at hsub
  exact hsub.symm

omit [Fintype U] [DecidableEq U] in
/-- **No backward signals separate.** If `backward p S = ∅`, then `g` maps vectors supported on
the free inputs outside `S` to vectors vanishing on the outputs carried in `S`. -/
theorem apply_eq_zero_of_backward_eq_empty (hf : ∀ x i, p.trace I x (out i) = f x i)
    (S : Finset (Wire n s)) (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z))
    (hbwd : backward p S = ∅) {d : Fin n → U} (hd : ∀ k, k ∉ (inputsIn S)ᶜ ∩ J → d k = 0)
    {i : Fin m} (hi : i ∈ outputsIn out S) : g d i = 0 := by
  have hz₀ : ∀ k, k ∉ J → z₀ k = z₀ k := fun _ _ => rfl
  have hzd : ∀ k, k ∉ J → (z₀ + d) k = z₀ k := fun k hk => by
    simp [hd k fun h => hk (Finset.mem_of_mem_inter_right h)]
  have hin : ∀ j ∈ inputsIn S, (z₀ + d) j = z₀ j := fun j hj => by
    simp [hd j fun h => (Finset.mem_compl.mp (Finset.mem_of_mem_inter_left h)) hj]
  have htr := trace_eq_of_agree_backward p I hin
    (fun w hw => False.elim (Finset.notMem_empty w (hbwd ▸ hw))) (out i)
    (by simpa [outputsIn] using hi)
  have hsub := congrFun (hg z₀ (z₀ + d) hz₀ hzd) i
  rw [add_sub_cancel_left, Pi.sub_apply, ← hf, ← hf, htr, sub_self] at hsub
  exact hsub.symm

/-- **Closed sets separate.** If a split has no forward and no backward signals, then `g` maps
vectors supported on the free inputs in `S` to vectors vanishing on the outputs carried outside
`S`, and vectors supported on the free inputs outside `S` to vectors vanishing on the outputs
carried in `S`. -/
theorem apply_eq_zero_of_closed (hf : ∀ x i, p.trace I x (out i) = f x i)
    (S : Finset (Wire n s)) (J : Finset (Fin n)) (z₀ : Fin n → U) (g : (Fin n → U) → Fin m → U)
    (hg : ∀ z z' : Fin n → U, (∀ k, k ∉ J → z k = z₀ k) → (∀ k, k ∉ J → z' k = z₀ k) →
      f z' - f z = g (z' - z))
    (hfwd : forward p S = ∅) (hbwd : backward p S = ∅) :
    (∀ d : Fin n → U, (∀ k, k ∉ inputsIn S ∩ J → d k = 0) →
        ∀ i, i ∉ outputsIn out S → g d i = 0) ∧
      (∀ d : Fin n → U, (∀ k, k ∉ (inputsIn S)ᶜ ∩ J → d k = 0) →
        ∀ i ∈ outputsIn out S, g d i = 0) :=
  ⟨fun d hd _ hi => by
    have _ : d ∈ slice (inputsIn S ∩ J) 0 := mem_slice.mpr hd
    exact apply_eq_zero_of_forward_eq_empty p out f I hf S J z₀ g hg hfwd hd hi,
   fun _ hd _ hi => apply_eq_zero_of_backward_eq_empty p out f I hf S J z₀ g hg hbwd hd hi⟩

end Kernel

end Algebraic.Cutwidth.MultiOutput.Internal

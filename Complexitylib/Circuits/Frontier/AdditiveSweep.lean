/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Extractor
public import Complexitylib.Circuits.Frontier.Sweep

/-!
# Threshold charging for additive generators

A path can describe an input by adding its edge labels, without assigning each
coordinate a unique read position. Prefix and suffix sums through the same state
can be combined. A sumset disperser, unlike a coordinate-rectangle disperser,
forbids a large sumset formed this way.

The transition threshold proof uses only reconstruction from the old prefix,
the emitted label, and the new suffix. It does not require unique paths, disjoint
coordinate scopes, or injectivity of addition on arbitrary prefix/suffix sets.
The program-to-sweep direction is sound; no converse for arbitrary sweeps is claimed.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {G M : Type*}

/-- `S` contains no sumset whose two summand sets both have cardinality at least `K`.
This is a threshold property, not the usual additive-combinatorial term "sum-free". -/
def SumsetFree [Add G] (S : Set G) (K : ℕ) : Prop :=
  ∀ A B : Set G, (∀ a ∈ A, ∀ b ∈ B, a + b ∈ S) → A.ncard < K ∨ B.ncard < K

/-- A large sumset-free set cannot be invariant under a large set of translations.
For a function of a linear image, this bounds the size of the image map's kernel. -/
theorem SumsetFree.ncard_lt_of_stable [Add G] {S H : Set G} {K : ℕ}
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hstable : ∀ x ∈ S, ∀ y ∈ H, x + y ∈ S) : H.ncard < K :=
  (hS S H hstable).resolve_left (not_lt_of_ge hK)

theorem SumsetDisperser.sumsetFree {ι U : Type*} [Add U]
    {f : (ι → U) → Bool} {K : ℕ} (hf : SumsetDisperser f K) (b : Bool) :
    SumsetFree {x | f x = b} K := by
  intro A B hAB
  by_contra! h
  obtain ⟨x, hx, y, hy, hne⟩ := hf A B h.1 h.2 b
  exact hne (hAB x hx y hy)

/-- Splicing by addition of prefix and suffix contributions. The input itself is an
element of the additive monoid; its coordinates need not be revealed separately. -/
structure AdditiveSweep [AddMonoid G] (S : Set G) (M : Type*) where
  /-- The number of steps. -/
  length : ℕ
  /-- The contribution of the steps before `t`. -/
  past : ℕ → G → G
  /-- The contribution of the steps from `t` on. -/
  future : ℕ → G → G
  /-- The label emitted at step `t`. -/
  emit : ℕ → G → G
  /-- The message at time `t`, possibly depending on the whole input. -/
  message : ℕ → G → M
  past_zero : ∀ x ∈ S, past 0 x = 0
  past_length : ∀ x ∈ S, past length x = x
  message_length : ∀ x ∈ S, ∀ y ∈ S, message length x = message length y
  reconstruct : ∀ t, ∀ x ∈ S, past t x + future t x = x
  step : ∀ t, ∀ x ∈ S, past (t + 1) x = past t x + emit t x
  splice : ∀ t, ∀ x ∈ S, ∀ y ∈ S, message t x = message t y →
    past t x + future t y ∈ S

namespace AdditiveSweep

variable [AddMonoid G] {S : Set G} (P : AdditiveSweep S M)

/-- The inputs of `S` sending the same message at time `t` as `x`. -/
def peers (t : ℕ) (x : G) : Set G := {y ∈ S | P.message t y = P.message t x}

/-- The past contributions of the peers of `x` at time `t`. -/
def pastSide (t : ℕ) (x : G) : Set G := P.past t '' P.peers t x

/-- The future contributions of the peers of `x` at time `t`. -/
def futureSide (t : ℕ) (x : G) : Set G := P.future t '' P.peers t x

/-- The step from time `t`: the old message, the new message, and the emitted label. -/
def transition (t : ℕ) (x : G) : M × M × G :=
  (P.message t x, P.message (t + 1) x, P.emit t x)

/-- The number of distinct transitions realized by `S`, summed over all steps. -/
noncomputable def transitionCount : ℕ :=
  ∑ t ∈ Finset.range P.length, (P.transition t '' S).ncard

/-- Any finite encoding that determines the old state, new state, and emitted label
can replace the raw transition count. In particular, only one old syndrome is needed
when the new syndrome is determined by the current read value. -/
theorem transitionCount_le_codes [Finite G] {D : ℕ → Type*}
    (code : ∀ t, G → D t) (C : ∀ t, Set (D t))
    (hC : ∀ t < P.length, (C t).Finite)
    (hmem : ∀ t < P.length, ∀ x ∈ S, code t x ∈ C t)
    (hdet : ∀ t < P.length, ∀ x ∈ S, ∀ y ∈ S,
      code t x = code t y → P.transition t x = P.transition t y) :
    P.transitionCount ≤ ∑ t ∈ Finset.range P.length, (C t).ncard := by
  refine Finset.sum_le_sum fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  exact (ncard_image_le_ncard_image_of_determines (toFinite _) _ _ (hdet t ht)).trans
    (ncard_le_ncard (by rintro _ ⟨x, hx, rfl⟩; exact hmem t ht x hx) (hC t ht))

theorem pastSide_lt_or_futureSide_lt {K : ℕ} (hS : SumsetFree S K) (t : ℕ) (x : G) :
    (P.pastSide t x).ncard < K ∨ (P.futureSide t x).ncard < K := by
  apply hS
  rintro _ ⟨y, ⟨hy, hyx⟩, rfl⟩ _ ⟨z, ⟨hz, hzx⟩, rfl⟩
  exact P.splice t y hy z hz (hyx.trans hzx.symm)

theorem ncard_pastSide_zero_le [Finite G] (x : G) : (P.pastSide 0 x).ncard ≤ 1 := by
  have h : P.pastSide 0 x ⊆ {0} := by
    rintro _ ⟨y, ⟨hy, _⟩, rfl⟩
    exact P.past_zero y hy
  simpa using ncard_le_ncard h

theorem ncard_pastSide_length {x : G} (hx : x ∈ S) :
    (P.pastSide P.length x).ncard = S.ncard := by
  congr 1
  apply subset_antisymm
  · rintro _ ⟨y, ⟨hy, _⟩, rfl⟩
    simpa only [P.past_length y hy] using hy
  · intro y hy
    exact ⟨y, ⟨hy, P.message_length y hy x hx⟩, P.past_length y hy⟩

/-- The first time at which the past contributions of the peers of `x` number at least
`K`. -/
noncomputable def chargeTime (K : ℕ) (x : G) : ℕ :=
  sInf {t | K ≤ (P.pastSide t x).ncard}

/-- **Additive frontier bound.** Dense sumset-free sets require almost as many
transitions as elements, even when different paths can describe the same element. -/
theorem ncard_le [Finite G] {K : ℕ} (hS : SumsetFree S K) (hK1 : 1 < K)
    (hK : K ≤ S.ncard) : S.ncard ≤ (K - 1) ^ 2 * P.transitionCount := by
  have hlength : ∀ x ∈ S, P.length ∈ {t | K ≤ (P.pastSide t x).ncard} := fun x hx =>
    show K ≤ _ by rw [P.ncard_pastSide_length hx]; exact hK
  have hcharged : ∀ x ∈ S, K ≤ (P.pastSide (P.chargeTime K x) x).ncard := fun x hx =>
    Nat.sInf_mem ⟨_, hlength x hx⟩
  have hbefore : ∀ x, ∀ t < P.chargeTime K x, (P.pastSide t x).ncard < K := fun x t ht =>
    not_le.mp (Nat.notMem_of_lt_sInf (s := {t | K ≤ (P.pastSide t x).ncard}) ht)
  have hle_length : ∀ x ∈ S, P.chargeTime K x ≤ P.length := fun x hx =>
    Nat.sInf_le (hlength x hx)
  have hpos : ∀ x ∈ S, 0 < P.chargeTime K x := by
    intro x hx
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h := hcharged x hx
    rw [h0] at h
    have := h.trans (P.ncard_pastSide_zero_le x)
    lia
  let step : G → ℕ := fun x => P.chargeTime K x - 1
  calc S.ncard
      ≤ ∑ t ∈ Finset.range P.length, (S ∩ step ⁻¹' {t}).ncard :=
        ncard_le_sum_ncard_fiber (toFinite S) step P.length fun x hx => by
          have := hle_length x hx; have := hpos x hx; simp only [step]; lia
    _ ≤ ∑ t ∈ Finset.range P.length, (K - 1) ^ 2 * (P.transition t '' S).ncard := by
      refine Finset.sum_le_sum fun t _ => ?_
      refine (ncard_le_mul_ncard_image (toFinite _) (P.transition t) _ fun τ => ?_).trans
        (Nat.mul_le_mul_left _ (ncard_le_ncard (image_mono inter_subset_left)))
      rcases (S ∩ step ⁻¹' {t} ∩ P.transition t ⁻¹' {τ}).eq_empty_or_nonempty with
        h | ⟨x, hx⟩
      · simp [h]
      obtain ⟨⟨hxS, hxt⟩, hxτ⟩ := hx
      have hxcharge : P.chargeTime K x = t + 1 := by
        have := hpos x hxS
        simp only [step, mem_preimage, mem_singleton_iff] at hxt
        lia
      have hpast : (P.pastSide t x).ncard ≤ K - 1 := by
        have := hbefore x t (by lia); lia
      have hfuture : (P.futureSide (t + 1) x).ncard ≤ K - 1 := by
        have := hcharged x hxS
        rw [hxcharge] at this
        rcases P.pastSide_lt_or_futureSide_lt hS (t + 1) x with h | h <;> lia
      calc (S ∩ step ⁻¹' {t} ∩ P.transition t ⁻¹' {τ}).ncard
          ≤ (P.pastSide t x ×ˢ P.futureSide (t + 1) x).ncard := by
            refine ncard_le_ncard_of_injOn
              (fun y => (P.past t y, P.future (t + 1) y)) ?_ ?_ (toFinite _)
            · rintro y ⟨⟨hyS, _⟩, hyτ⟩
              have hyx : P.transition t y = P.transition t x := hyτ.trans hxτ.symm
              simp only [transition, Prod.mk.injEq] at hyx
              exact ⟨⟨y, ⟨hyS, hyx.1⟩, rfl⟩, ⟨y, ⟨hyS, hyx.2.1⟩, rfl⟩⟩
            · rintro y ⟨⟨hyS, _⟩, hyτ⟩ z ⟨⟨hzS, _⟩, hzτ⟩ hyz
              have hemit : P.emit t y = P.emit t z := by
                have h := hyτ.trans hzτ.symm
                exact congrArg (fun p => p.2.2) h
              have hparts := Prod.mk.inj hyz
              calc y = (P.past t y + P.emit t y) + P.future (t + 1) y := by
                      rw [← P.step t y hyS, P.reconstruct (t + 1) y hyS]
                   _ = (P.past t z + P.emit t z) + P.future (t + 1) z := by
                      rw [hparts.1, hparts.2, hemit]
                   _ = z := by rw [← P.step t z hzS, P.reconstruct (t + 1) z hzS]
        _ = (P.pastSide t x).ncard * (P.futureSide (t + 1) x).ncard := ncard_prod
        _ ≤ (K - 1) ^ 2 := by simpa only [sq] using Nat.mul_le_mul hpast hfuture
    _ = (K - 1) ^ 2 * P.transitionCount := (Finset.mul_sum ..).symm

end AdditiveSweep

end Complexity.Frontier

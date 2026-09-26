/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Balanced
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Direction
public import Complexitylib.Algebraic.LowerBound.Cutwidth.FourN

/-!
# The average-case `(4 - ε) n` bound

A circuit with at most `(4 - ε) n` gates agrees with a `(K, ν)`-balanced
function on at most `(1/2 + 3ν) 2ⁿ + 2^{(1 - ε/24) n}` inputs, for `K`
polynomial and `n` large, under the graph-ordering hypothesis.

This does not follow from the worst-case cut-counting lemma: an input whose
past set is still small at a vertex lies in a thin rectangle, on which a
balanced function is unconstrained. Instead the proof uses the direction of
the wiring graph. At a cut, the forward-crossing bits are determined by the
inputs read so far and the backward-crossing bits (`trace_eq_of_agree_backward`),
and symmetrically for the future. This caps the number of cut assignments a
fixed past or future can see, so the thin mass at a prefix `L` is at most
`(K - 1)(2^{n - a(L)} + 2^{n - c(L)})` with
`a(L) = |past L| - |forward cut|` and `c(L) = n - |past L| - |backward cut|`.
Along the vertex order `a` grows from `0` to the number of inputs read in
steps of at most four, and `a + c = n - |cut|`, so a prefix with both `a` and
`c` linear exists whenever the cutwidth is below `(1 - Ω(ε)) n`.

Circuits reading few inputs are handled separately: on every subcube fixing
the read inputs the circuit is constant, and a balanced function is close to
one half on a rectangle refining that subcube.

The attribution of the underlying compiler is as in `FourN`.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical
open Filter

/-! ## The wiring network has unique, direction-determined assignments -/

namespace Wiring

variable {n s : Nat} (p : Program Binary.signature n s) (out : Fin s)

theorem network_unambiguous : (network p out).Unambiguous := by
  intro x α α' hα hα'
  funext e
  rw [eq_trace_of_satisfies p out hα (signal p out e) e rfl,
    eq_trace_of_satisfies p out hα' (signal p out e) e rfl]

theorem network_forwardDetermined : (network p out).ForwardDetermined := by
  intro L x x' α α' hα hα' hpast hback e he
  have hα_eq : α = traceAssignment p out x := funext fun e =>
    eq_trace_of_satisfies p out hα (signal p out e) e rfl
  have hα'_eq : α' = traceAssignment p out x' := funext fun e =>
    eq_trace_of_satisfies p out hα' (signal p out e) e rfl
  subst hα_eq hα'_eq
  have hcut := (Multigraph.mem_cut _).mp he
  have key := trace_eq_of_agree_backward p out hpast (fun e hf hs => by
    apply hback
    rw [Network.mem_bwdCut, Multigraph.mem_cut]
    exact ⟨fun h => hf (h.mpr hs), hs⟩) (signal p out e) e rfl (by tauto)
  exact key

theorem network_backwardDetermined : (network p out).BackwardDetermined := by
  intro L x x' α α' hα hα' hfuture hfwd e he
  have hα_eq : α = traceAssignment p out x := funext fun e =>
    eq_trace_of_satisfies p out hα (signal p out e) e rfl
  have hα'_eq : α' = traceAssignment p out x' := funext fun e =>
    eq_trace_of_satisfies p out hα' (signal p out e) e rfl
  subst hα_eq hα'_eq
  have hcut := (Multigraph.mem_cut _).mp he
  have key := trace_eq_of_agree_backward p out (L := Lᶜ) (fun j hj => by
      obtain ⟨hr, hnp⟩ := (mem_past_compl p out).mp hj
      exact hfuture j hr hnp)
    (fun e hf hs => by
      apply hfwd
      rw [Network.mem_fwdCut, Multigraph.mem_cut]
      rw [Finset.mem_compl, not_not] at hf
      rw [Finset.mem_compl] at hs
      exact ⟨fun h => hs (h.mp hf), hf⟩) (signal p out e) e rfl (by
      rw [Finset.mem_compl, Finset.mem_compl]
      tauto)
  exact key

end Wiring

/-! ## Balanced functions on subcubes -/

variable {n : Nat}

/-- The whole cube split at `u` coordinates is a rectangle with sides `2^u`
and `2^(n-u)`, so a balanced function accepts within `ν` of half of all inputs
once both exceed `K`. -/
theorem card_accepting_bounds_of_balanced {f : Cslib.BooleanFunction n} {K : Nat} {ν : ℝ}
    (hbal : Balanced f K ν) {u : Nat} (hu : u ≤ n) (hK₁ : K ≤ 2 ^ u) (hK₂ : K ≤ 2 ^ (n - u)) :
    (1 / 2 - ν) * 2 ^ n ≤ ((accepting f).card : ℝ) ∧
      ((accepting f).card : ℝ) ≤ (1 / 2 + ν) * 2 ^ n := by
  set U : Finset (Fin n) := Finset.univ.filter fun i => i.val < u with hU
  have hUcard : U.card = u := by
    rw [hU, Fin.card_filter_val_lt, Nat.min_eq_right hu]
  have hPcard : (Finset.univ : Finset (U → Bool)).card = 2 ^ u := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hUcard]
  have hQcard : (Finset.univ : Finset (↥Uᶜ → Bool)).card = 2 ^ (n - u) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      Finset.card_compl, Fintype.card_fin, hUcard]
  have hrect := hbal U Finset.univ Finset.univ (hPcard ▸ hK₁) (hQcard ▸ hK₂)
  have hones : (rectangleOnes f U Finset.univ Finset.univ).card = (accepting f).card := by
    apply Finset.card_bij (fun pq _ => glue U pq.1 pq.2)
    · intro pq hpq
      rw [rectangleOnes, Finset.mem_filter] at hpq
      exact mem_accepting.mpr hpq.2
    · intro pq _ pq' _ h
      exact Network.glue_injOn U Finset.univ (Finset.mem_univ _) (Finset.mem_univ _) h
    · intro x hx
      refine ⟨(fun i : U => x i, fun i : ↥Uᶜ => x i), ?_, glue_restrict U x⟩
      rw [rectangleOnes, Finset.mem_filter, glue_restrict]
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, mem_accepting.mp hx⟩
  rw [hPcard, hQcard] at hrect
  have hpow : ((2 : ℝ) ^ u) * (2 : ℝ) ^ (n - u) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hu]
  push_cast at hrect
  rw [hones, hpow] at hrect
  exact hrect

/-- **Few inputs read.** If `g` depends only on `R` and at least `2 ⌈log₂ K⌉`
coordinates lie outside `R`, then `g` agrees with a `(K, ν)`-balanced `f` on
at most `(1/2 + ν) 2ⁿ` inputs: on each subcube fixing `R`, `g` is constant,
and refining the subcube by `⌈log₂ K⌉` free coordinates gives a rectangle on
which `f` is balanced. -/
theorem card_agree_le_of_dependsOnlyOn {g f : Cslib.BooleanFunction n} {K : Nat} {ν : ℝ}
    (hbal : Balanced f K ν) {R : Finset (Fin n)}
    (hg : DependsOnlyOn g R) (hR : R.card + 2 * Nat.clog 2 K ≤ n) :
    ((Finset.univ.filter fun x => g x = f x).card : ℝ) ≤ (1 / 2 + ν) * 2 ^ n := by
  set k := Nat.clog 2 K with hk
  have hcompl : k ≤ Rᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcompl
  have hdisj : Disjoint R T := Finset.disjoint_of_subset_right hTsub disjoint_compl_right
  set U := R ∪ T with hU
  have hUcard : U.card = R.card + k := by
    rw [hU, Finset.card_union_of_disjoint hdisj, hTcard]
  have hUn : U.card ≤ n := by omega
  have hRU : ∀ i : R, i.1 ∈ U := fun i => Finset.mem_union_left T i.2
  -- The restriction of an assignment to `U` onto `R`.
  let ρ : (U → Bool) → (R → Bool) := fun p i => p ⟨i.1, hRU i⟩
  let Pr : (R → Bool) → Finset (U → Bool) := fun r => Finset.univ.filter fun p => ρ p = r
  have mem_Pr : ∀ r p, p ∈ Pr r ↔ ρ p = r := fun r p => by simp [Pr]
  -- Every row class has at least `2 ^ k ≥ K` elements.
  have hPr_ge : ∀ r, K ≤ (Pr r).card := by
    intro r
    have hT : ∀ i : U, i.1 ∉ R → i.1 ∈ T := fun i h => by
      rcases Finset.mem_union.mp i.2 with h' | h'
      · exact absurd h' h
      · exact h'
    let ψ : (T → Bool) → (U → Bool) := fun t i =>
      if h : i.1 ∈ R then r ⟨i.1, h⟩ else t ⟨i.1, hT i h⟩
    have maps : ∀ t, ψ t ∈ Pr r := by
      intro t
      rw [mem_Pr]
      funext i
      simp [ρ, ψ, i.2]
    have inj : Function.Injective ψ := by
      intro t t' h
      funext i
      have hi : i.1 ∉ R := Finset.disjoint_right.mp hdisj i.2
      have := congrFun h ⟨i.1, Finset.mem_union_right R i.2⟩
      simpa [ψ, hi] using this
    calc K ≤ 2 ^ k := Nat.le_pow_clog one_lt_two K
      _ = (Finset.univ : Finset (T → Bool)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hTcard]
      _ ≤ (Pr r).card := Finset.card_le_card_of_injOn ψ (fun t _ => maps t) inj.injOn
  have hQcard : (Finset.univ : Finset (↥Uᶜ → Bool)).card = 2 ^ (n - U.card) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      Finset.card_compl, Fintype.card_fin]
  have hKQ : K ≤ (Finset.univ : Finset (↥Uᶜ → Bool)).card := by
    rw [hQcard]
    calc K ≤ 2 ^ k := Nat.le_pow_clog one_lt_two K
      _ ≤ 2 ^ (n - U.card) := Nat.pow_le_pow_right two_pos (by omega)
  -- The row classes partition the assignments to `U`.
  have hsum : (∑ r : R → Bool, ((Pr r).card : ℝ)) = 2 ^ U.card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := ρ) (s := (Finset.univ : Finset (U → Bool)))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at h
    have h' : ((2 ^ U.card : Nat) : ℝ) = ∑ r : R → Bool, ((Pr r).card : ℝ) := by
      rw [h]
      push_cast
      rfl
    rw [← h']
    push_cast
    rfl
  -- The value of `g` on the subcube fixing `R` to `r`.
  let b : (R → Bool) → Bool := fun r => g (glue R r fun _ => false)
  have hb : ∀ x, g x = b (fun i : R => x i) := by
    intro x
    apply hg
    intro i hi
    simp [glue, hi]
  -- The agreement fibers.
  let A : (R → Bool) → Finset (Fin n → Bool) := fun r =>
    (Finset.univ.filter fun x => g x = f x).filter fun x => (fun i : R => x i) = r
  have hA : ((Finset.univ.filter fun x => g x = f x).card : ℝ) = ∑ r : R → Bool, ((A r).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := fun x : Fin n → Bool => fun i : R => x i)
      (s := Finset.univ.filter fun x => g x = f x) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [h]
    push_cast
    rfl
  -- Each fiber is a rectangle slice on which `f` takes the constant value of `g`.
  have hfiber : ∀ r, ((A r).card : ℝ) ≤ (1 / 2 + ν) * ((Pr r).card * 2 ^ (n - U.card)) := by
    intro r
    have hrect := hbal U (Pr r) Finset.univ (hPr_ge r) hKQ
    rw [hQcard] at hrect
    push_cast at hrect
    -- Restriction maps the fiber bijectively onto the points of the rectangle where `f = b r`.
    let B : Finset ((U → Bool) × (↥Uᶜ → Bool)) :=
      (Pr r ×ˢ Finset.univ).filter fun pq => f (glue U pq.1 pq.2) = b r
    have hAB : (A r).card = B.card := by
      apply Finset.card_bij (fun x _ => (fun i : U => x i, fun i : ↥Uᶜ => x i))
      · intro x hx
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨hgf, hr⟩ := hx
        simp only [B, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        refine ⟨(mem_Pr r _).mpr ?_, ?_⟩
        · funext i
          simp only [ρ]
          exact congrFun hr i
        · rw [glue_restrict, ← hgf, hb x, hr]
      · intro x _ y _ h
        simp only [Prod.mk.injEq] at h
        funext i
        by_cases hi : i ∈ U
        · exact congrFun h.1 ⟨i, hi⟩
        · exact congrFun h.2 ⟨i, Finset.mem_compl.mpr hi⟩
      · intro pq hpq
        simp only [B, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hpq
        obtain ⟨hp, hf⟩ := hpq
        refine ⟨glue U pq.1 pq.2, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          have hr : (fun i : R => glue U pq.1 pq.2 i) = r := by
            rw [← (mem_Pr r _).mp hp]
            funext i
            simp only [ρ]
            exact glue_apply_mem U pq.1 pq.2 ⟨i.1, hRU i⟩
          refine ⟨?_, hr⟩
          rw [hf, hb, hr]
        · exact Prod.ext (funext fun i => glue_apply_mem U pq.1 pq.2 i)
            (funext fun i => glue_apply_compl U pq.1 pq.2 i)
    rw [hAB]
    cases hbr : b r
    · -- `g` is `0` on the subcube: count the rejected points of the rectangle.
      have hB : B = (Pr r ×ˢ (Finset.univ : Finset (↥Uᶜ → Bool))).filter
          fun pq => ¬ f (glue U pq.1 pq.2) = true := by
        ext pq
        simp [B, hbr]
      have hsplit : (rectangleOnes f U (Pr r) Finset.univ).card + B.card =
          (Pr r ×ˢ (Finset.univ : Finset (↥Uᶜ → Bool))).card := by
        rw [hB]
        exact Finset.card_filter_add_card_filter_not _
      have h1 : ((Pr r ×ˢ (Finset.univ : Finset (↥Uᶜ → Bool))).card : ℝ) =
          (Pr r).card * 2 ^ (n - U.card) := by
        rw [Finset.card_product, hQcard]
        push_cast
        rfl
      have h2 : (B.card : ℝ) = (Pr r).card * 2 ^ (n - U.card) -
          (rectangleOnes f U (Pr r) Finset.univ).card := by
        have h := congrArg (Nat.cast : ℕ → ℝ) hsplit
        push_cast at h
        linarith
      rw [h2]
      linarith [hrect.1]
    · -- `g` is `1` on the subcube: the rectangle's accepted points.
      have : B = rectangleOnes f U (Pr r) Finset.univ := by
        ext pq
        simp [B, rectangleOnes, hbr]
      rw [this]
      exact hrect.2
  rw [hA]
  calc (∑ r : R → Bool, ((A r).card : ℝ))
      ≤ ∑ r : R → Bool, (1 / 2 + ν) * ((Pr r).card * 2 ^ (n - U.card)) :=
        Finset.sum_le_sum fun r _ => hfiber r
    _ = (1 / 2 + ν) * 2 ^ (n - U.card) * ∑ r : R → Bool, ((Pr r).card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = (1 / 2 + ν) * 2 ^ n := by
        rw [hsum, mul_assoc, ← pow_add, Nat.sub_add_cancel hUn]

/-! ## A good prefix of the vertex order -/

namespace Network

variable {V E : Type} (N : Network n V E) [Fintype V] [Fintype E] [LinearOrder V]

omit [Fintype E] in
/-- Processing one vertex adds to the past at most one variable when no two
variables are read at the same vertex. -/
theorem card_past_upto_le (v : V)
    (hv : ∀ j ∈ N.read, ∀ j' ∈ N.read, N.portVertex j = v → N.portVertex j' = v → j = j') :
    (N.past (upto v)).card ≤ (N.past (below v)).card + 1 := by
  have hsub : N.past (upto v) ⊆ N.past (below v) ∪ N.read.filter fun j => N.portVertex j = v := by
    intro j hj
    rw [mem_past, mem_upto] at hj
    obtain ⟨hr, hle⟩ := hj
    rcases hle.lt_or_eq with hlt | heq
    · exact Finset.mem_union_left _ (N.mem_past.mpr ⟨hr, mem_below.mpr hlt⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, heq⟩)
  have hone : (N.read.filter fun j => N.portVertex j = v).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro j hj j' hj'
    rw [Finset.mem_filter] at hj hj'
    exact hv j hj.1 j' hj'.1 hj.2 hj'.2
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hone _))

/-- Processing one vertex removes from the forward cut only its incident edges. -/
theorem fwdCut_below_subset (v : V) :
    N.fwdCut (below v) ⊆ N.fwdCut (upto v) ∪ N.edgesAt v := by
  intro e he
  rw [mem_fwdCut, Multigraph.mem_cut, mem_below, mem_below] at he
  obtain ⟨hcut, hfst⟩ := he
  have hsnd : ¬ N.snd e < v := fun h => hcut ⟨fun _ => h, fun _ => hfst⟩
  by_cases hv : N.snd e = v
  · exact Finset.mem_union_right _ ((Multigraph.mem_edgesAt _).mpr (Or.inr hv))
  · refine Finset.mem_union_left _ ?_
    rw [mem_fwdCut, Multigraph.mem_cut, mem_upto, mem_upto]
    have hlt : v < N.snd e := lt_of_le_of_ne (not_lt.mp hsnd) (Ne.symm hv)
    exact ⟨fun h => absurd (h.mp hfst.le) (not_le.mpr hlt), hfst.le⟩

/-- Processing one vertex drops the forward cut by at most its degree. -/
theorem card_fwdCut_below_le (v : V) :
    (N.fwdCut (below v)).card ≤ (N.fwdCut (upto v)).card + N.degree v :=
  (Finset.card_le_card (N.fwdCut_below_subset v)).trans (Finset.card_union_le _ _)

end Network

/-- **A good prefix.** For quantities `P` and `F` on the prefixes of a finite
linear order with `P ∅ = 0`, `t + F univ ≤ P univ`, `P` growing by at most one
and `F` dropping by at most three per vertex, some prefix `L` has
`t ≤ P L - F L < t + 4`. -/
theorem exists_good_prefix {V : Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (P F : Finset V → Nat) (t : Nat) (hP0 : P ∅ = 0)
    (huniv : t + F Finset.univ ≤ P Finset.univ)
    (hstepP : ∀ v, P (Network.upto v) ≤ P (Network.below v) + 1)
    (hstepF : ∀ v, F (Network.below v) ≤ F (Network.upto v) + 3) :
    ∃ L : Finset V, IsLowerSet (L : Set V) ∧ t + F L ≤ P L ∧ P L < F L + t + 4 := by
  have univ_nonempty : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  let B : Finset V := Finset.univ.filter fun v => t + F (Network.upto v) ≤ P (Network.upto v)
  have hBne : B.Nonempty := by
    refine ⟨Finset.univ.max' univ_nonempty, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [Network.upto_max']
    exact huniv
  have hvB : B.min' hBne ∈ B := Finset.min'_mem B hBne
  have hvle : t + F (Network.upto (B.min' hBne)) ≤ P (Network.upto (B.min' hBne)) :=
    (Finset.mem_filter.mp hvB).2
  refine ⟨Network.upto (B.min' hBne), Network.isLowerSet_upto _, hvle, ?_⟩
  rcases Network.below_eq_empty_or_exists_upto (B.min' hBne) with hempty | ⟨u, huv, hbelow⟩
  · have := hstepP (B.min' hBne)
    rw [hempty, hP0] at this
    omega
  · have huB : u ∉ B := fun huB => absurd (Finset.min'_le B u huB) (not_le.mpr huv)
    have hu : ¬ t + F (Network.upto u) ≤ P (Network.upto u) :=
      fun h => huB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have h₁ := hstepP (B.min' hBne)
    have h₂ := hstepF (B.min' hBne)
    rw [hbelow] at h₁ h₂
    omega

namespace Wiring

variable {n s : Nat} (p : Program Binary.signature n s) (out : Fin s)

/-- A vertex of the wiring graph reads at most one variable. -/
theorem card_past_upto_le [LinearOrder (Vertex p out)] (v : Vertex p out) :
    ((network p out).past (Network.upto v)).card ≤
      ((network p out).past (Network.below v)).card + 1 := by
  apply (network p out).card_past_upto_le v
  intro j hj j' hj' h h'
  have hjr : Reach p out (Wire.input j) := (mem_read p out).mp hj
  have hj'r : Reach p out (Wire.input j') := (mem_read p out).mp hj'
  have hpv : portVertex p out j = portVertex p out j' := h.trans h'.symm
  rw [portVertex_of_reach p out hjr, portVertex_of_reach p out hj'r] at hpv
  have h'' := Subtype.ext_iff.mp (Sum.inl_injective hpv)
  injection h''

end Wiring

/-! ## Assembly -/

/-- Agreement counted through the accepting sets. -/
theorem card_agree_eq (g f : Cslib.BooleanFunction n) :
    ((Finset.univ.filter fun x => g x = f x).card : ℝ) =
      2 ^ n - (accepting g).card - (accepting f).card + 2 * (accepting g ∩ accepting f).card := by
  have h1 : (Finset.univ.filter fun x => g x = f x) =
      (accepting g ∩ accepting f) ∪ (accepting g ∪ accepting f)ᶜ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, mem_accepting]
    cases hg : g x <;> cases hf : f x <;> simp
  have h2 : Disjoint (accepting g ∩ accepting f) (accepting g ∪ accepting f)ᶜ := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_compl] at hx'
    exact hx' (Finset.mem_union_left _ (Finset.mem_inter.mp hx).1)
  have h3 : (accepting g ∪ accepting f).card + (accepting g ∩ accepting f).card =
      (accepting g).card + (accepting f).card := Finset.card_union_add_card_inter _ _
  have h5 : (accepting g ∪ accepting f).card ≤ 2 ^ n := by
    have := Finset.card_le_univ (accepting g ∪ accepting f)
    rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  have h4 : ((accepting g ∪ accepting f)ᶜ).card = 2 ^ n - (accepting g ∪ accepting f).card := by
    rw [Finset.card_compl, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [h1, Finset.card_union_of_disjoint h2, h4, Nat.cast_add, Nat.cast_sub h5]
  have h3' : ((accepting g ∪ accepting f).card : ℝ) + (accepting g ∩ accepting f).card =
      (accepting g).card + (accepting f).card := by exact_mod_cast h3
  push_cast
  linarith

/-- **The numeric core of the average case.** At a good prefix, twice the
thin-rectangle mass of the one-sided count is at most `2 ^ ((1 - ε/24) n)`,
once `n` satisfies an explicit logarithmic condition. -/
theorem thin_mass_le {ε η C : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 4) (hη : 0 ≤ η) (hη1 : η ≤ ε / 36)
    (hC : 0 ≤ C) {n : Nat} (hn : 2 ≤ n) {K c : Nat} (hK : K ≤ n ^ c)
    (hlog : (2 * c + 3) * Real.logb 2 n + (C + 24) < ε * n / 24)
    {s n' : Nat} (hs : (s : ℝ) ≤ (4 - ε) * n) (hn'le : n' ≤ n)
    (hread : n - n' < 2 * Nat.clog 2 K)
    {Vb : ℝ} (hVpos : 0 < Vb) (hVb : Vb ≤ 16 * n)
    {t : Nat} (ht : ε * n / 12 ≤ t) (ht' : (t : ℝ) < ε * n / 12 + 1)
    {P F B : Nat} (hP : P ≤ n) (hgood₁ : t + F ≤ P) (hgood₂ : P < F + t + 4)
    (hcut : ((F + B : Nat) : ℝ) ≤
      (1 / 3 + η) * max ((s : ℝ) - n') 0 + 3 * Real.logb 2 Vb + C) :
    2 * (((K - 1 : Nat) : ℝ) * (2 ^ (n - P + F) + 2 ^ (P + B))) ≤
      (2 : ℝ) ^ ((1 - ε / 24) * n) := by
  set k := Nat.clog 2 K with hk_def
  have hK1 : 1 < K := by
    by_contra h
    rw [not_lt] at h
    have : k = 0 := Nat.clog_of_right_le_one h 2
    omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two hn1
  have hcL : 0 ≤ (c : ℝ) * Real.logb 2 n := by positivity
  have hεn : 0 ≤ ε * n := by positivity
  have hε4n : ε * n ≤ 4 * n := mul_le_mul_of_nonneg_right hε4 (by positivity)
  have hk1 : 1 ≤ k := Nat.clog_pos one_lt_two hK1
  have hlow : 2 ^ (k - 1) < K := Nat.pow_pred_clog_lt_self one_lt_two hK1
  have hkR : (k : ℝ) < c * Real.logb 2 n + 1 := by
    have h₁ : ((2 : ℝ) ^ (k - 1)) < (n : ℝ) ^ c := by
      have : (2 ^ (k - 1) : Nat) < n ^ c := hlow.trans_le hK
      exact_mod_cast this
    have h₂ := (Real.logb_lt_logb one_lt_two (by positivity) h₁)
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h₂
    have : ((k - 1 : Nat) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]
      simp
    linarith
  have hlogK : Real.logb 2 K ≤ c * Real.logb 2 n := by
    have h := (Real.logb_le_logb one_lt_two hKpos (by positivity)).mpr
      (show (K : ℝ) ≤ (n : ℝ) ^ c by exact_mod_cast hK)
    rwa [Real.logb_pow] at h
  have hlogS : Real.logb 2 Vb ≤ 4 + Real.logb 2 n := by
    calc Real.logb 2 Vb ≤ Real.logb 2 (16 * n) :=
          (Real.logb_le_logb one_lt_two hVpos (by positivity)).mpr hVb
      _ = 4 + Real.logb 2 n := by
          rw [Real.logb_mul (by norm_num) (by positivity),
            show (16 : ℝ) = 2 ^ (4 : Nat) by norm_num, Real.logb_pow,
            Real.logb_self_eq_one one_lt_two]
          ring
  have hreadR : (n : ℝ) - n' < 2 * k := by
    have : ((n - n' : Nat) : ℝ) < 2 * k := by exact_mod_cast hread
    rwa [Nat.cast_sub hn'le] at this
  -- The two exponents at the good prefix.
  have hE1 : ((n - P + F : Nat) : ℝ) ≤ (1 - ε / 12) * n := by
    have h : n - P + F ≤ n - t := by omega
    have h' : ((n - P + F : Nat) : ℝ) ≤ ((n - t : Nat) : ℝ) := by exact_mod_cast h
    have htn : t ≤ n := by omega
    rw [Nat.cast_sub htn] at h'
    linarith
  have hE2 : ((P + B : Nat) : ℝ) ≤ t + 3 + ((F + B : Nat) : ℝ) := by
    have h : P + B + 1 ≤ t + 4 + (F + B) := by omega
    have h' : ((P + B + 1 : Nat) : ℝ) ≤ ((t + 4 + (F + B) : Nat) : ℝ) := by exact_mod_cast h
    push_cast at h' ⊢
    linarith
  -- The cut bound in terms of `n`, `k`, and the logarithms.
  have hηn : η * n ≤ ε / 36 * n := mul_le_mul_of_nonneg_right hη1 (by positivity)
  have hεη : 0 ≤ ε * η * n := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hηk : η * k ≤ k / 6 := by
    have : η ≤ 1 / 6 := by linarith
    nlinarith
  have hw : (1 / 3 + η) * max ((s : ℝ) - n') 0 + 3 * Real.logb 2 Vb + C ≤
      max ((1 - ε / 4) * n + k) 0 + 12 + 3 * Real.logb 2 n + C := by
    have h₁ : (1 / 3 + η) * max ((s : ℝ) - n') 0 ≤ (1 / 3 + η) * max ((3 - ε) * n + 2 * k) 0 :=
      mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (by linarith)
    have h₂ : (1 / 3 + η) * max ((3 - ε) * n + 2 * k) 0 ≤ max ((1 - ε / 4) * n + k) 0 := by
      rcases le_or_gt 0 ((3 - ε) * n + 2 * k) with hA | hA
      · rw [max_eq_left hA]
        refine le_max_of_le_left ?_
        nlinarith
      · rw [max_eq_right hA.le, mul_zero]
        exact le_max_right _ _
    linarith
  -- Exponent comparison for each term.
  have hX1 : 1 + Real.logb 2 K + ((n - P + F : Nat) : ℝ) ≤ (1 - ε / 24) * n - 1 := by
    linarith
  have hX2 : 1 + Real.logb 2 K + ((P + B : Nat) : ℝ) ≤ (1 - ε / 24) * n - 1 := by
    have h : ((P + B : Nat) : ℝ) ≤
        t + 3 + (max ((1 - ε / 4) * n + k) 0 + 12 + 3 * Real.logb 2 n + C) := by
      linarith [hcut.trans hw]
    rcases le_or_gt 0 ((1 - ε / 4) * n + k) with hpos | hneg
    · rw [max_eq_left hpos] at h
      linarith
    · rw [max_eq_right hneg.le] at h
      linarith
  -- Each term is at most half of the target.
  have hpow : ∀ (m : Nat) (X : ℝ), (m : ℝ) ≤ X →
      2 * (((K - 1 : Nat) : ℝ) * (2 : ℝ) ^ m) ≤ (2 : ℝ) ^ (1 + Real.logb 2 K + X) := by
    intro m X hmX
    have hK' : ((K - 1 : Nat) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
    have hKeq : (K : ℝ) = (2 : ℝ) ^ Real.logb 2 K :=
      (Real.rpow_logb two_pos (by norm_num) hKpos).symm
    have h2m : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ X := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two hmX
    have hK0 : (0 : ℝ) ≤ ((K - 1 : Nat) : ℝ) := by positivity
    calc 2 * (((K - 1 : Nat) : ℝ) * (2 : ℝ) ^ m) ≤ 2 * ((K : ℝ) * (2 : ℝ) ^ X) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hK' h2m (by positivity) hKpos.le
      _ = 2 * ((2 : ℝ) ^ Real.logb 2 K * (2 : ℝ) ^ X) := by rw [← hKeq]
      _ = (2 : ℝ) ^ (1 + Real.logb 2 K + X) := by
          rw [Real.rpow_add two_pos, Real.rpow_add two_pos, Real.rpow_one]
          ring
  have hA := (hpow (n - P + F) _ le_rfl).trans (Real.rpow_le_rpow_of_exponent_le one_le_two hX1)
  have hB := (hpow (P + B) _ le_rfl).trans (Real.rpow_le_rpow_of_exponent_le one_le_two hX2)
  have hhalf : (2 : ℝ) ^ ((1 - ε / 24) * n - 1) = (2 : ℝ) ^ ((1 - ε / 24) * n) / 2 :=
    Real.rpow_sub_one (by norm_num) _
  rw [hhalf] at hA hB
  have hsplit : 2 * (((K - 1 : Nat) : ℝ) * (2 ^ (n - P + F) + 2 ^ (P + B))) =
      2 * (((K - 1 : Nat) : ℝ) * 2 ^ (n - P + F)) + 2 * (((K - 1 : Nat) : ℝ) * 2 ^ (P + B)) := by
    ring
  rw [hsplit]
  linarith

/-- **The fixed-`n` average-case bound.** With the graph-ordering hypothesis
for slack `η ≤ ε/36`, a circuit with at most `(4 - ε) n` binary gates agrees
with a `(K, ν)`-balanced function, `K ≤ n ^ c`, on at most
`(1/2 + 3ν) 2ⁿ + 2 ^ ((1 - ε/24) n)` inputs, once `n` satisfies an explicit
logarithmic condition. -/
theorem card_agree_le_of_bounds {ε η C : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 4) (hη : 0 ≤ η)
    (hη1 : η ≤ ε / 36) (hC : 0 ≤ C) (order : Multigraph.OrderingBound η C)
    {n : Nat} (hn : 2 ≤ n) {f : Cslib.BooleanFunction n} {K c : Nat} (hK : K ≤ n ^ c)
    {ν : ℝ} (hν : 0 ≤ ν) (hbal : Balanced f K ν)
    (hlog : (2 * c + 3) * Real.logb 2 n + (C + 24) < ε * n / 24)
    (circuit : Circuit Binary.signature n 1) (hs : (circuit.size : ℝ) ≤ (4 - ε) * n) :
    ((Finset.univ.filter fun x => circuit.eval Binary.interpretation x 0 = f x).card : ℝ) ≤
      (1 / 2 + 3 * ν) * 2 ^ n + (2 : ℝ) ^ ((1 - ε / 24) * n) := by
  set k := Nat.clog 2 K with hk_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two hn1
  have hcL : 0 ≤ (c : ℝ) * Real.logb 2 n := by positivity
  have hεn : 0 ≤ ε * n := by positivity
  have hε4n : ε * n ≤ 4 * n := mul_le_mul_of_nonneg_right hε4 (by positivity)
  -- The threshold `⌈log₂ K⌉` is tiny compared with `n`.
  have hkR : (k : ℝ) < c * Real.logb 2 n + 1 := by
    rcases Nat.lt_or_ge 1 K with hK1 | hK1
    · have hk1 : 1 ≤ k := Nat.clog_pos one_lt_two hK1
      have hlow : 2 ^ (k - 1) < K := Nat.pow_pred_clog_lt_self one_lt_two hK1
      have h₁ : ((2 : ℝ) ^ (k - 1)) < (n : ℝ) ^ c := by
        have : (2 ^ (k - 1) : Nat) < n ^ c := hlow.trans_le hK
        exact_mod_cast this
      have h₂ := (Real.logb_lt_logb one_lt_two (by positivity) h₁)
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h₂
      have : ((k - 1 : Nat) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk1]
        simp
      linarith
    · rw [hk_def, Nat.clog_of_right_le_one hK1]
      simp only [Nat.cast_zero]
      linarith
  have hkε : (2 * k + 2 : ℝ) < ε * n / 24 := by linarith
  have hk_small : 2 * k + 2 < n := by
    have : (2 * k + 2 : ℝ) < n := by linarith
    exact_mod_cast this
  -- The bound is immediate when the circuit reads few inputs.
  have few : ∀ g : Cslib.BooleanFunction n, ∀ R : Finset (Fin n), DependsOnlyOn g R →
      R.card + 2 * k ≤ n →
      ((Finset.univ.filter fun x => g x = f x).card : ℝ) ≤
        (1 / 2 + 3 * ν) * 2 ^ n + (2 : ℝ) ^ ((1 - ε / 24) * n) := by
    intro g R hg hR
    have h := card_agree_le_of_dependsOnlyOn hbal hg hR
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((1 - ε / 24) * n) := by positivity
    have h3 : (0 : ℝ) ≤ ν * 2 ^ n := by positivity
    linarith
  -- The circuit's output wire.
  obtain ⟨g, hg⟩ : ∃ g, circuit.outputs 0 = g := ⟨_, rfl⟩
  have eval_eq : ∀ x, circuit.eval Binary.interpretation x 0 =
      circuit.program.trace Binary.interpretation x g := by
    intro x
    rw [← hg]
    rfl
  simp only [eval_eq]
  cases g with
  | input j =>
    apply few _ {j}
    · intro x y agree
      simp only [Program.trace_input]
      exact agree j (Finset.mem_singleton_self j)
    · rw [Finset.card_singleton]
      omega
  | gate out =>
    have gdef : ∀ x, circuit.program.trace Binary.interpretation x (Wire.gate out) =
        circuit.program.eval Binary.interpretation x out := by
      intro x
      simp [Program.trace_gateWire]
    simp only [gdef]
    have hn'le : (Wiring.read circuit.program out).card ≤ n := Wiring.card_read_le _ out
    by_cases hfew : (Wiring.read circuit.program out).card + 2 * k ≤ n
    · exact few _ _ (Wiring.network_computes circuit.program out).dependsOnlyOn hfew
    rw [not_le] at hfew
    have hread : n - (Wiring.read circuit.program out).card < 2 * k := by omega
    have hreadR : (n : ℝ) - (Wiring.read circuit.program out).card < 2 * k := by
      have : ((n - (Wiring.read circuit.program out).card : Nat) : ℝ) < 2 * k := by
        exact_mod_cast hread
      rwa [Nat.cast_sub hn'le] at this
    -- The ordering of the wiring graph and its cut bound.
    obtain ⟨inst, hcut⟩ := order (Wiring.Vertex circuit.program out) (Wiring.Edge circuit.program out)
      (Wiring.network circuit.program out).toMultigraph (Wiring.loopless _ out)
      (Wiring.maxDegreeLE_three _ out) (Wiring.connected _ out)
    -- The threshold for the good prefix.
    obtain ⟨t, ht, ht'⟩ : ∃ t : Nat, ε * n / 12 ≤ t ∧ (t : ℝ) < ε * n / 12 + 1 :=
      ⟨⌈ε * n / 12⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩
    have htn' : t ≤ (Wiring.read circuit.program out).card := by
      have : (t : ℝ) ≤ (Wiring.read circuit.program out).card := by linarith
      exact_mod_cast this
    have hstepP : ∀ v, ((Wiring.network circuit.program out).past (Network.upto v)).card ≤
        ((Wiring.network circuit.program out).past (Network.below v)).card + 1 :=
      Wiring.card_past_upto_le circuit.program out
    have hstepF : ∀ v, ((Wiring.network circuit.program out).fwdCut (Network.below v)).card ≤
        ((Wiring.network circuit.program out).fwdCut (Network.upto v)).card + 3 := by
      intro v
      have hdeg : (Wiring.network circuit.program out).degree v ≤ 3 :=
        Wiring.maxDegreeLE_three circuit.program out v
      exact ((Wiring.network circuit.program out).card_fwdCut_below_le v).trans
        (Nat.add_le_add_left hdeg _)
    have hP0 : ((Wiring.network circuit.program out).past ∅).card = 0 := by
      rw [Network.past_empty, Finset.card_empty]
    have huniv : t + ((Wiring.network circuit.program out).fwdCut Finset.univ).card ≤
        ((Wiring.network circuit.program out).past Finset.univ).card := by
      rw [Network.past_univ]
      have hF : (Wiring.network circuit.program out).fwdCut Finset.univ = ∅ := by
        apply Finset.subset_empty.mp
        have := (Wiring.network circuit.program out).fwdCut_subset Finset.univ
        rwa [Multigraph.cut_univ] at this
      rw [hF, Finset.card_empty, add_zero]
      exact htn'
    obtain ⟨L, hL, hgood₁, hgood₂⟩ := exists_good_prefix
      (fun L => ((Wiring.network circuit.program out).past L).card)
      (fun L => ((Wiring.network circuit.program out).fwdCut L).card) t hP0 huniv hstepP hstepF
    have hgood₁' : t + ((Wiring.network circuit.program out).fwdCut L).card ≤
        ((Wiring.network circuit.program out).past L).card := hgood₁
    have hgood₂' : ((Wiring.network circuit.program out).past L).card <
        ((Wiring.network circuit.program out).fwdCut L).card + t + 4 := hgood₂
    have hPn : ((Wiring.network circuit.program out).past L).card ≤ n := by
      simpa using Finset.card_le_univ ((Wiring.network circuit.program out).past L)
    -- The cut bound at `L` in terms of the circuit size.
    have hVpos : (0 : ℝ) < Fintype.card (Wiring.Vertex circuit.program out) := by
      exact_mod_cast Fintype.card_pos
    have hV : (Fintype.card (Wiring.Vertex circuit.program out) : ℝ) ≤ n + 3 * circuit.size := by
      exact_mod_cast Wiring.card_vertex_le circuit.program out
    have hdiff : (Fintype.card (Wiring.Edge circuit.program out) : ℝ) -
        Fintype.card (Wiring.Vertex circuit.program out) ≤
        (circuit.size : ℝ) - (Wiring.read circuit.program out).card := by
      rw [Wiring.card_edge_sub_card_vertex]
      have : (Fintype.card (Wiring.ReachableGate circuit.program out) : ℝ) ≤ circuit.size := by
        exact_mod_cast Wiring.card_reachableGate_le circuit.program out
      linarith
    have hbound : (((Wiring.network circuit.program out).cut L).card : ℝ) ≤
        (1 / 3 + η) * max ((circuit.size : ℝ) - (Wiring.read circuit.program out).card) 0 +
          3 * Real.logb 2 (n + 3 * circuit.size) + C := by
      have h₁ : (1 / 3 + η) * max ((Fintype.card (Wiring.Edge circuit.program out) : ℝ) -
          Fintype.card (Wiring.Vertex circuit.program out)) 0 ≤
          (1 / 3 + η) * max ((circuit.size : ℝ) - (Wiring.read circuit.program out).card) 0 :=
        mul_le_mul_of_nonneg_left (max_le_max hdiff le_rfl) (by linarith)
      have h₂ : Real.logb 2 (Fintype.card (Wiring.Vertex circuit.program out)) ≤
          Real.logb 2 (n + 3 * circuit.size) :=
        (Real.logb_le_logb one_lt_two hVpos (hVpos.trans_le hV)).mpr hV
      linarith [hcut L hL]
    have hVb : (n : ℝ) + 3 * circuit.size ≤ 16 * n := by linarith
    have hthin := thin_mass_le hε hε4 hη hη1 hC hn hK hlog hs hn'le hread
      (by positivity : (0 : ℝ) < n + 3 * circuit.size) hVb ht ht' hPn hgood₁' hgood₂'
      (by rw [Network.card_fwdCut_add_card_bwdCut]; exact hbound)
    -- The one-sided count and the balance of `f` on the whole cube.
    have hinter := (Wiring.network circuit.program out).card_accepting_inter_le
      (Wiring.network_computes circuit.program out) (Wiring.network_unambiguous circuit.program out)
      (Wiring.network_forwardDetermined circuit.program out)
      (Wiring.network_backwardDetermined circuit.program out) hν hbal L
    have hF := (card_accepting_bounds_of_balanced hbal (u := k) (by omega)
      (Nat.le_pow_clog one_lt_two K)
      ((Nat.le_pow_clog one_lt_two K).trans (Nat.pow_le_pow_right two_pos (by omega)))).1
    have hA : ((accepting fun x => circuit.program.eval Binary.interpretation x out).card : ℝ) ≤
        2 ^ n := by
      have := Finset.card_le_univ (accepting fun x => circuit.program.eval Binary.interpretation x out)
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
      exact_mod_cast this
    have hνA : ν * (accepting fun x => circuit.program.eval Binary.interpretation x out).card ≤
        ν * 2 ^ n := mul_le_mul_of_nonneg_left hA hν
    have hagree := card_agree_eq (fun x => circuit.program.eval Binary.interpretation x out) f
    beta_reduce at hagree
    rw [hagree]
    linarith

/-- **Theorem (average case).** Assume the graph-ordering lemma for every
slack `η > 0` and a family `f n` that is `(K n, ν)`-balanced with `K n ≤ n ^ c`
for all large `n`. Then for every `ε > 0` and all sufficiently large `n`,
every binary circuit with at most `(4 - ε) n` gates agrees with `f n` on at
most `(1/2 + 3ν) 2ⁿ + 2 ^ ((1 - ε/24) n)` inputs. -/
theorem eventually_card_agree_le
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat) {ν : ℝ} (hν : 0 ≤ ν)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hbal : ∀ᶠ n in atTop, Balanced (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      (circuit.size : ℝ) ≤ (4 - ε) * n →
        ((Finset.univ.filter fun x => circuit.eval Binary.interpretation x 0 = f n x).card : ℝ) ≤
          (1 / 2 + 3 * ν) * 2 ^ n + (2 : ℝ) ^ ((1 - ε / 24) * n) := by
  rcases le_or_gt ε 4 with hε4 | hε4
  · obtain ⟨C, hC⟩ := order (ε / 36) (by positivity)
    have order' : Multigraph.OrderingBound (ε / 36) (max C 0) := hC.mono (le_max_left _ _)
    have hlog := eventually_mul_logb_add_lt (2 * c + 3) (max C 0 + 24)
      (by positivity : 0 < ε / 24)
    filter_upwards [hK, hbal, hlog, eventually_ge_atTop 2] with n hKn hbaln hlogn hn2
    intro circuit hs
    have hlogn' : (2 * c + 3) * Real.logb 2 n + (max C 0 + 24) < ε * n / 24 := by
      have : ε / 24 * n = ε * n / 24 := by ring
      rw [← this]
      exact hlogn
    exact card_agree_le_of_bounds hε hε4 (by positivity) le_rfl (le_max_right C 0) order' hn2 hKn
      hν hbaln hlogn' circuit hs
  · -- No circuit has negative size.
    filter_upwards [eventually_ge_atTop 1] with n hn1
    intro circuit hs
    exfalso
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h0 : (0 : ℝ) ≤ circuit.size := by positivity
    nlinarith

/-- **The average case from the pathwidth hypothesis.** -/
theorem eventually_card_agree_le_of_pathwidthBound
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat) {ν : ℝ} (hν : 0 ≤ ν)
    (hK : ∀ᶠ n in atTop, K n ≤ n ^ c)
    (hbal : ∀ᶠ n in atTop, Balanced (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      (circuit.size : ℝ) ≤ (4 - ε) * n →
        ((Finset.univ.filter fun x => circuit.eval Binary.interpretation x 0 = f n x).card : ℝ) ≤
          (1 / 2 + 3 * ν) * 2 ^ n + (2 : ℝ) ^ ((1 - ε / 24) * n) := by
  refine eventually_card_agree_le (fun η hη => ?_) f K c hν hK hbal hε
  obtain ⟨N₀, hN₀⟩ := pathwidth (η / 2) (by positivity)
  refine ⟨N₀ + 9, ?_⟩
  have := Multigraph.orderingBound_of_pathwidthBound (by positivity) hN₀
  rwa [show 2 * (η / 2) = η by ring] at this

end Cutwidth
end Algebraic

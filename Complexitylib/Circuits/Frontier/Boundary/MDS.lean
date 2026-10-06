/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Boundary.Fiber
public import Complexitylib.Circuits.Frontier.Linear.LowerBound
public import Complexitylib.Circuits.Frontier.Layouts

/-!
# Nonlinear recovery maps

The graph code `(x, F x)` is MDS when any `N` of its `2N` coordinates determine `x`.
Every layout has a cut containing exactly `N` input and output terminals. The complementary
mixed observations at that cut are both injective, so its signal values determine the input.
Over a finite alphabet this gives the same circuit lower bound as total regularity.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Set Filter Asymptotics Matrix

universe u v

variable {U : Type u} {N : ℕ}

/-- Any balanced mixed observation determines the input. Equivalently, any `N` coordinates
of the systematic graph code `(x, F x)` determine its codeword. -/
def IsMDS (F : (Fin N → U) → (Fin N → U)) : Prop :=
  ∀ X Y : Set (Fin N), X.ncard + Y.ncard = N →
    ∀ x y, EqOn x y X → EqOn (F x) (F y) Y → x = y

theorem IsMDS.mixedFiber_eq_singleton {F : (Fin N → U) → (Fin N → U)} (hF : IsMDS F)
    {X Y : Set (Fin N)} (hXY : X.ncard + Y.ncard = N) (x : Fin N → U) :
    mixedFiber F X Y x = {x} := by
  ext z
  constructor
  · intro hz; exact hF X Y hXY z x hz.1 hz.2
  · rintro rfl; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

section Circuit

variable {σ : Signature.{v}} {I : Interpretation σ U} {c : Circuit σ N N}
  {F : (Fin N → U) → (Fin N → U)}

/-- The MDS property forces every output to depend on every input. -/
theorem upstream_of_mds [Nontrivial U] (hF : IsMDS F) (hc : c.Computes I F)
    (o i : Fin N) : c.program.Upstream (c.outputs o) (.input i) := by
  classical
  by_contra hnot
  obtain ⟨a, b, hab⟩ := exists_pair_ne U
  let x : Fin N → U := fun _ => a
  let y := Function.update x i b
  have hout : c.program.trace I x (c.outputs o) = c.program.trace I y (c.outputs o) := by
    apply c.program.trace_congr_of_upstream I (w := c.outputs o) _ _ .refl
    intro j hj
    have hji : j ≠ i := fun h => hnot (h ▸ hj)
    simp [y, hji]
  have hXY : ({i}ᶜ : Set (Fin N)).ncard + ({o} : Set (Fin N)).ncard = N := by
    have H := ncard_add_ncard_compl ({i} : Set (Fin N))
    simp only [ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at H ⊢
    lia
  have heq : x = y := hF {i}ᶜ {o} hXY x y
    (fun j hj => by have hji : j ≠ i := hj; simp [y, hji])
    (by
      intro j hj
      have hj : j = o := hj
      subst j
      exact (congrFun (hc x) o).symm.trans (hout.trans (congrFun (hc y) o)))
  exact hab (by simpa [x, y] using congrFun heq i)

/-- Every layout passes a balanced input-output observation. This statement only needs
the output terminals; some unused inputs are allowed. -/
theorem exists_balanced_terminal_cut (I : Interpretation σ U) (c : Circuit σ N N)
    (π : Layout (Compiler.Vertex c.program c.outputs)) :
    ∃ t, ((Compiler.network c.program c.outputs I fun _ => univ).readIn (π.initial t)).ncard +
      {o | Compiler.Vertex.output o ∈ π.initial t}.ncard = N := by
  classical
  let G := Compiler.network c.program c.outputs I fun _ => univ
  let outs (P : Set (Compiler.Vertex c.program c.outputs)) := {o | Compiler.Vertex.output o ∈ P}
  let a (t : ℕ) := (G.readIn (π.initial t)).ncard + (outs (π.initial t)).ncard
  have h0 : a 0 = 0 := by simp [a, outs, Network.readIn]
  have hT : N ≤ a (Nat.card (Compiler.Vertex c.program c.outputs)) := by
    simp only [a, π.initial_of_card_le le_rfl, outs, mem_univ, ofPred_true, ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    lia
  have hstep : ∀ t < Nat.card (Compiler.Vertex c.program c.outputs), a (t + 1) ≤ a t + 1 := by
    intro t ht
    set v := π.symm ⟨t, ht⟩
    have hsucc := π.initial_succ ht
    have hread : G.readIn (π.initial (t + 1)) ⊆ G.readIn (π.initial t) ∪ G.readAt v := by
      rintro i ⟨u, hu, hiu⟩
      rw [hsucc] at hu
      rcases hu with rfl | hu
      · exact Or.inr hiu
      · exact Or.inl ⟨u, hu, hiu⟩
    have houts : outs (π.initial (t + 1)) ⊆ outs (π.initial t) ∪ {o | .output o = v} := by
      intro o ho
      simp only [outs, mem_ofPred_eq, hsucc, mem_insert_iff] at ho
      exact ho.elim Or.inr Or.inl
    have hv : (G.readAt v).ncard + {o | Compiler.Vertex.output o = v}.ncard ≤ 1 := by
      rcases hvv : v with w | j | o
      · have h1 := Compiler.ncard_readAt_le I (fun _ => univ) (Compiler.Vertex.signal w)
        have h2 : {o | (Compiler.Vertex.output o : Compiler.Vertex c.program c.outputs) =
            Compiler.Vertex.signal w}.ncard = 0 := by simp
        dsimp [G] at *
        lia
      · have h1 : G.readAt (.junction j) = ∅ := by
          ext i
          simp only [Network.readAt, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hi
          obtain ⟨_, h⟩ := Compiler.site_eq_some hi
          cases h
        simp [h1]
      · have h1 : G.readAt (.output o) = ∅ := by
          ext i
          simp only [Network.readAt, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hi
          obtain ⟨_, h⟩ := Compiler.site_eq_some hi
          cases h
        simp [h1]
    have := ncard_le_ncard hread (toFinite _)
    have := ncard_le_ncard houts (toFinite _)
    have := ncard_union_le (G.readIn (π.initial t)) (G.readAt v)
    have := ncard_union_le (outs (π.initial t)) {o | Compiler.Vertex.output o = v}
    dsimp [a]
    lia
  obtain ⟨t, _, ht⟩ := exists_eq_of_le_succ h0 hT hstep
  exact ⟨t, ht⟩

/-- The frontier of a balanced cut determines the input of an MDS map. -/
theorem exists_injective_cut_mds (hF : IsMDS F) (hc : c.Computes I F)
    (π : Layout (Compiler.Vertex c.program c.outputs)) :
    ∃ t, Function.Injective fun (x : Fin N → U)
      (e : ↥((Compiler.network c.program c.outputs I fun _ => univ).cut (π.initial t))) =>
        c.program.trace I x e.1.signal.1 := by
  classical
  obtain ⟨t, ht⟩ := exists_balanced_terminal_cut I c π
  let G := Compiler.network c.program c.outputs I fun _ => univ
  let X := G.readIn (π.initial t)
  let Y := {o | Compiler.Vertex.output o ∈ π.initial t}
  have hXY : X.ncard + Y.ncard = N := ht
  have hcomp : Xᶜ.ncard + Yᶜ.ncard = N := by
    have hX := ncard_add_ncard_compl X
    have hY := ncard_add_ncard_compl Y
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hX hY
    lia
  have hsplice : OutputSplicing F X Y
      (fun (x : Fin N → U) (e : ↥(G.cut (π.initial t))) => c.program.trace I x e.1.signal.1) := by
    intro x y hxy z hzx hzy
    have H := Compiler.trace_out_of_cut I
      (fun e he => congrFun hxy ⟨e, he⟩) hzx hzy
    have htrace (x : Fin N → U) (o : Fin N) := congrFun (hc x) o
    exact ⟨fun o ho => (htrace z o).symm.trans ((H o).1 ho |>.trans (htrace x o)),
      fun o ho => (htrace z o).symm.trans ((H o).2 ho |>.trans (htrace y o))⟩
  exact ⟨t, hsplice.injective (hF X Y hXY) (hF Xᶜ Yᶜ hcomp)⟩

/-- An MDS map supplies the same full-entropy graph demand as a totally regular matrix. -/
theorem exists_graph_of_mds [Finite U] [Nontrivial U] (hN : 1 ≤ N) {r : ℕ} (hr : 2 ≤ r)
    (hfan : c.FanInAtMost r) (hF : IsMDS F) (hc : c.Computes I F) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 * N ∧
      G.cycleRank + N ≤ (r - 1) * c.innerSize + 1 ∧
      ∀ π : Layout V, ∃ t, N ≤ (G.cut (π.initial t)).ncard := by
  let G := Compiler.network c.program c.outputs I fun _ => univ
  have hconn : G.Connected := Compiler.connected_of_upstream I _
    (w₀ := .input ⟨0, hN⟩) fun o => upstream_of_mds hF hc o _
  have hread : G.read.ncard = N := by
    have heq : G.read = univ := by
      rw [Compiler.read_network]
      exact eq_univ_of_forall fun i => Compiler.reach_of_upstream (upstream_of_mds hF hc i i)
    rw [heq, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨_, _, inferInstance, inferInstance, G.toMultigraph, hconn, Compiler.loopless I _,
    Compiler.maxDegreeLE I _ hr hfan, ?_, ?_, fun π => ?_⟩
  · simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
  · have H := Compiler.cycleRank_add_ncard_read_le I _ hfan hconn
    rw [hread] at H
    exact H
  · obtain ⟨t, hinj⟩ := exists_injective_cut_mds hF hc π
    have H := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin N),
      Fintype.card_fin, Nat.card_coe_set_eq] at H
    exact ⟨t, (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp H⟩

end Circuit

/-- **Circuit lower bounds from mixed recovery.** The alphabet and circuit basis are
arbitrary; finiteness supplies the capacity bound. -/
theorem lowerBound_mds {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (U : Type u) [Finite U] [Nontrivial U]
      (σ : Signature.{v}) (I : Interpretation σ U) (F : (Fin N → U) → (Fin N → U))
      (c : Circuit σ N N), IsMDS F → c.FanInAtMost r → c.Computes I F →
        (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA (κ := 4) (by norm_num) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  replace H := H η hη le_rfl
  filter_upwards [H C (fun _ => 1) (isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))),
    eventually_ge_atTop 1] with N hN hN1
  intro U _ _ σ I F c hF hfan hc
  obtain ⟨V, E, _, _, G, hconn, hloop, hdeg, hV, hrank, hwidth⟩ :=
    exists_graph_of_mds hN1 hr hfan hF hc
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  set B := (A + η) * G.cycleRank + η * Nat.card V + C
  obtain ⟨t, ht⟩ := hwidth π
  have hB : (N : ℝ) ≤ B := (by exact_mod_cast ht : (N : ℝ) ≤ _).trans (hπ t)
  set s : ℝ := (((r - 1) * c.innerSize : ℕ) : ℝ)
  have hs : s = (r - 1) * c.innerSize := by
    simp only [s]; rw [Nat.cast_mul, Nat.cast_sub (by lia), Nat.cast_one]
  have hVs : (Nat.card V : ℝ) ≤ 4 * (N + s + 1) := by
    have : 2 * r * c.innerSize + 3 * N ≤ 4 * ((r - 1) * c.innerSize) + 4 * N := by
      have : 2 * r ≤ 4 * (r - 1) := by lia
      nlinarith
    have h4 : (Nat.card V : ℝ) ≤ 4 * ((r - 1) * c.innerSize : ℕ) + 4 * N := by
      exact_mod_cast hV.trans this
    simp only [s]
    linarith
  rw [← hs]
  refine hN s (Nat.card V) B (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVs ?_ ?_
  · have : 0 ≤ Real.log (Nat.card V + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
    linarith
  · have hrank' : (G.cycleRank : ℝ) ≤ s - N + 1 := by
      have : (G.cycleRank : ℝ) + N ≤ ((r - 1) * c.innerSize : ℕ) + 1 := by exact_mod_cast hrank
      simp only [s]; linarith
    have := mul_le_mul_of_nonneg_left hrank' (by linarith : 0 ≤ A + η)
    linarith

/-- Nonlinear MDS maps inherit the binary Gaussian coefficient. -/
theorem mds_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (U : Type u) [Finite U] [Nontrivial U]
      (σ : Signature.{v}) (I : Interpretation σ U) (F : (Fin N → U) → (Fin N → U))
      (c : Circuit σ N N), IsMDS F → c.FanInAtMost 2 → c.Computes I F →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
          c.innerSize := by
  filter_upwards [lowerBound_mds.{u, v} le_rfl
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian hε] with N hN
  intro U _ _ σ I F c hF hfan hc
  have H := hN U σ I F c hF hfan hc
  rw [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at H
  norm_num at H
  exact H

/-- **Every fixed fan-in for nonlinear MDS maps**, with the Gaussian degree coefficient. -/
theorem mds_degree {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (U : Type u) [Finite U] [Nontrivial U]
      (σ : Signature.{v}) (I : Interpretation σ U) (F : (Fin N → U) → (Fin N → U))
      (c : Circuit σ N N), IsMDS F → c.FanInAtMost r → c.Computes I F →
        (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * N <
          (r - 1) * c.innerSize :=
  lowerBound_mds hr (Gaussian.degreeCoefficient_pos (by lia)) (layoutBound_degree (by lia)) hε

/-- Coordinatewise alphabet permutations preserve the MDS graph-code property. -/
theorem IsMDS.permute {F : (Fin N → U) → (Fin N → U)} (hF : IsMDS F)
    (before after : Fin N → Equiv.Perm U) :
    IsMDS (fun x i => after i (F (fun j => before j (x j)) i)) := by
  intro X Y hXY x y hX hY
  have H := hF X Y hXY (fun j => before j (x j)) (fun j => before j (y j))
    (fun j hj => congrArg (before j) (hX hj))
    (fun i hi => (after i).injective (hY hi))
  exact funext fun j => (before j).injective (congrFun H j)

/-- Total regularity is the linear special case of mixed recovery. -/
theorem TotallyRegular.isMDS {K : Type*} [Field K]
    {M : Matrix (Fin N) (Fin N) K} (hM : TotallyRegular M) :
    IsMDS (fun x => M *ᵥ x) := by
  classical
  intro X Y hXY x y hX hY
  have hXc := ncard_add_ncard_compl X
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hXc
  have H := hM.eq_zero (R := Y.toFinset) (C := Xᶜ.toFinset) (v := x - y)
    (by simpa only [← ncard_eq_toFinset_card'] using (by lia : Y.ncard = Xᶜ.ncard))
    (fun j hj => by
      have hj : j ∈ X := by simpa using hj
      simp [hX hj])
    (fun i hi => by
      have hi : i ∈ Y := by simpa using hi
      simp only [Matrix.mulVec_sub, Pi.sub_apply, hY hi, sub_self])
  exact sub_eq_zero.mp H

end Complexity.Frontier

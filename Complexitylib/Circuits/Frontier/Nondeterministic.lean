/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Projection
public import Complexitylib.Circuits.Frontier.LowerBound
public import Complexitylib.Circuits.Frontier.Layouts

/-!
# Nondeterministic circuit lower bounds

A verifier has `n` ordinary inputs and `k` existential witness inputs, with no restriction on
`k`. Hiding the witnesses preserves the compiler graph and its degree and size bounds. The
cycle count still subtracts every reachable ordinary input. The same dense rectangle-free
families therefore have the same lower bound, uniformly in the number of witness inputs.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Set Filter Asymptotics

universe u v

variable {U : Type u} {σ : Signature.{v}} {n k : ℕ}

/-- A verifier accepts an ordinary input exactly when some witness makes its output accepting. -/
def NondeterministicDecides (c : Circuit σ (n + k) 1) (I : Interpretation σ U) (Acc : Set U)
    (S : Set (Fin n → U)) : Prop :=
  ∀ x, x ∈ S ↔ ∃ y : Fin k → U, c.eval I (Fin.append x y) 0 ∈ Acc

variable [Finite U] [Nontrivial U]

/-- The compiler graph of a verifier, after hiding witnesses, has the same reduction bounds
as an ordinary circuit. The subtraction counts only ordinary inputs. -/
theorem exists_graph_of_nondeterministic_decides {I : Interpretation σ U} {Acc : Set U}
    {c : Circuit σ (n + k) 1} {S : Set (Fin n → U)} {K r : ℕ}
    (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : NondeterministicDecides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 ∧
      (G.cycleRank : ℝ) ≤ ((r - 1) * c.innerSize : ℕ) - n + Real.logb (Nat.card U) K + 1 ∧
      ∀ (π : Layout V) (w : ℕ), (∀ t, (G.cut (π.initial t)).ncard ≤ w) →
        Real.logb (Nat.card U) S.ncard ≤
          w + (r + 2) + 3 * Real.logb (Nat.card U) K +
            Real.logb (Nat.card U) (Nat.card V + 1) := by
  let N := constraintNetwork I Acc c
  let H := N.hide
  have hacc : H.accepted = S := by
    rw [Network.accepted_hide, Compiler.accepted_network]
    ext x
    rw [hS x]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy 0⟩, fun ⟨y, hy⟩ =>
      ⟨y, fun o => Subsingleton.elim o 0 ▸ hy⟩⟩
  have hf : RectangleFree H.accepted K := hacc ▸ hfree
  have hb : Nat.card U * K ^ 2 ≤ H.accepted.ncard := hacc ▸ hbig
  have hread := N.ncard_read_hide_le
  have hrank := Compiler.cycleRank_add_ncard_read_le (out := c.outputs) I (fun _ => Acc) hfan
    (Compiler.connected I _)
  have hsum : H.cycleRank + H.read.ncard ≤ (r - 1) * c.innerSize + 1 := by
    change N.cycleRank + N.hide.read.ncard ≤ _
    exact (Nat.add_le_add_left hread _).trans hrank
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hunread : (H.readᶜ.ncard : ℝ) < Real.logb (Nat.card U) K := by
    rw [Real.lt_logb_iff_rpow_lt hq (by exact_mod_cast hfree.pos), Real.rpow_natCast]
    exact_mod_cast hf.pow_ncard_compl_lt H.dependsOn_read hb
  have hcompl : H.readᶜ.ncard + H.read.ncard = n := by
    have h := ncard_add_ncard_compl H.read
    simpa [Nat.card_eq_fintype_card, add_comm] using h
  have hcycle : (H.cycleRank : ℝ) ≤
      ((r - 1) * c.innerSize : ℕ) - n + Real.logb (Nat.card U) K + 1 := by
    have hs : (H.cycleRank : ℝ) + H.read.ncard ≤ ((r - 1) * c.innerSize : ℕ) + 1 := by
      exact_mod_cast hsum
    have hc : (H.readᶜ.ncard : ℝ) + H.read.ncard = n := by exact_mod_cast hcompl
    linarith
  refine ⟨_, _, inferInstance, inferInstance, H.toMultigraph,
    Compiler.connected I (fun _ => Acc), Compiler.loopless I (fun _ => Acc),
    Compiler.maxDegreeLE I (fun _ => Acc) hr hfan,
    ?_, hcycle, ?_⟩
  · simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
  · intro π w hw
    have h := H.logb_ncard_accepted_le hf hb π hw
      (Compiler.maxDegreeLE I (fun _ => Acc) hr hfan)
      (fun v => (N.ncard_readAt_hide_le v).trans (Compiler.ncard_readAt_le I (fun _ => Acc) v))
    rw [hacc] at h
    convert h using 1
    push_cast
    ring

/-- The frontier lower bound for verifiers, uniformly in the number of existential inputs. -/
theorem lowerBound_nondeterministic {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → NondeterministicDecides c I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_of_graph hr hA hlayout S K hfree hK hdense hε,
    hfree, eventually_card_mul_sq_le_ncard S K hfree hK hdense] with n hn hf hb
  intro k σ I Acc c hfan hS
  obtain ⟨V, E, _, _, G, hc, hl, hd, hV, hrank, hw⟩ :=
    exists_graph_of_nondeterministic_decides hr hfan hS hf hb
  exact hn c.innerSize V E G hc hl hd hV hrank hw

/-- The Gaussian coefficient also holds for nondeterministic circuits of fan-in two. -/
theorem lowerBound_nondeterministic_gaussian (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → NondeterministicDecides c I Acc (S n) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n < c.innerSize := by
  have h := lowerBound_nondeterministic (r := 2) le_rfl
    two_mul_frontierCoefficient_pos layoutBound_gaussian S K hfree hK hdense hε
  rw [Algebraic.Cutwidth.Gaussian.one_add_inv_two_mul_frontierCoefficient] at h
  norm_num at h ⊢
  exact h

end Complexity.Frontier

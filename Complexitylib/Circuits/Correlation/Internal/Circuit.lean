/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Correlation.Internal.Classes
public import Complexitylib.Circuits.Frontier.AverageCase.Network
public import Complexitylib.Circuits.Frontier.Reduction
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite correlation bounds for circuits

Two partitions of the inputs of a circuit into rectangle classes:

* by the output alone, if the circuit ignores the inputs in `D`: each output class is a
  rectangle for the cut `D`;
* by the output and the values on the frontier of a layout of the compiled constraint network
  at time `t`: by the separator lemma each class is a rectangle for the cut `X` of the inputs
  read before time `t`, and there are at most `2 · 2^w` classes for a layout of width `w`.

With a bisection hypothesis on the cut ranks, the inputs read before some time number exactly
`⌊n/2⌋`, since reads grow one at a time.
-/

@[expose] public section

namespace Complexity.Correlation

open Set Complexity.Frontier

section Network

variable {U ι V E : Type*} (N : Network U ι V E)

/-- The inputs read by a set with one more vertex. -/
theorem readIn_insert_subset (v : V) (L : Set V) :
    N.readIn (insert v L) ⊆ N.readIn L ∪ N.readAt v := by
  rintro i ⟨u, hu, hi⟩
  rcases hu with rfl | hu
  · exact Or.inr hi
  · exact Or.inl ⟨u, hu, hi⟩

/-- **Reads grow one at a time.** If each vertex reads at most one input, some initial segment
of every layout reads exactly `k` inputs, for every `k` up to the number read. -/
theorem exists_ncard_readIn_eq [Finite ι] (π : Layout V) (hm : ∀ v, (N.readAt v).ncard ≤ 1)
    {k : ℕ} (hk : k ≤ N.read.ncard) :
    ∃ t ≤ Nat.card V, (N.readIn (π.initial t)).ncard = k := by
  set f : ℕ → ℕ := fun t => (N.readIn (π.initial t)).ncard with hf
  have hstep : ∀ t, f (t + 1) ≤ f t + 1 := by
    intro t
    by_cases ht : t < Nat.card V
    · simp only [hf, π.initial_succ ht]
      calc (N.readIn (insert (π.symm ⟨t, ht⟩) (π.initial t))).ncard
          ≤ (N.readIn (π.initial t) ∪ N.readAt (π.symm ⟨t, ht⟩)).ncard :=
            ncard_le_ncard (readIn_insert_subset N _ _) (toFinite _)
        _ ≤ (N.readIn (π.initial t)).ncard + (N.readAt (π.symm ⟨t, ht⟩)).ncard :=
            ncard_union_le _ _
        _ ≤ _ := Nat.add_le_add_left (hm _) _
    · simp only [hf, π.initial_of_card_le (show Nat.card V ≤ t by omega),
        π.initial_of_card_le (show Nat.card V ≤ t + 1 by omega)]
      omega
  have hzero : f 0 = 0 := by simp [hf]
  have hlast : f (Nat.card V) = N.read.ncard := by
    simp only [hf, π.initial_of_card_le le_rfl]
    rfl
  have hex : ∃ t, k ≤ f t := ⟨Nat.card V, hlast ▸ hk⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (hlast ▸ hk), ?_⟩
  have hspec := Nat.find_spec hex
  rcases hfind : Nat.find hex with _ | s
  · rw [hfind, hzero] at hspec
    change f 0 = k
    omega
  · have hmin := Nat.find_min hex (show s < Nat.find hex by omega)
    rw [hfind] at hspec
    have := hstep s
    change f (s + 1) = k
    omega

end Network

variable {σ : Cslib.Circuits.Signature} {n : ℕ} (I : Cslib.Circuits.Interpretation σ Bool)
  (c : Cslib.Circuits.Circuit σ n 1)

theorem accepted_constraintNetwork_eval (b : Bool) :
    (constraintNetwork I {b} c).accepted = {x | c.eval I x 0 = b} :=
  accepted_constraintNetwork fun _ => Iff.rfl

theorem read_constraintNetwork (b : Bool) :
    (constraintNetwork I {b} c).read = (constraintNetwork I {true} c).read := by
  simp only [constraintNetwork, Compiler.read_network]

/-- **Unread inputs.** If a circuit does not read the inputs in `D`, its two output classes
are rectangles for the cut `D`. -/
theorem sq_corr_mul_le_of_unread (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {D : Set (Fin n)}
    (hD : D ⊆ (constraintNetwork I {true} c).readᶜ) :
    (2 * agreement (quadForm Q) (fun x => c.eval I x 0) - 1) ^ 2 * 2 ^ cutRank Q D ≤ 2 := by
  have H := sq_two_mul_agreement_sub_one_mul_le Q (fun x => c.eval I x 0)
    (fun x => c.eval I x 0) D (fun _ _ h => h) ?_
  · simpa using H
  intro x₀
  set S := {x : Fin n → Bool | c.eval I x 0 = c.eval I x₀ 0}
  refine ⟨univ, Dᶜ.domRestrict '' S, ?_⟩
  have hdep := (constraintNetwork I {c.eval I x₀ 0} c).dependsOn_read
  rw [accepted_constraintNetwork_eval, read_constraintNetwork] at hdep
  have hD' := hdep.mono (subset_compl_comm.mp hD)
  apply subset_antisymm
  · intro x hx
    exact ⟨mem_univ _, x, hx, rfl⟩
  · rintro z ⟨-, y, hy, hyz⟩
    have h : (y ∈ S) = (z ∈ S) := hD' fun i hi => congrFun hyz ⟨i, hi⟩
    exact h ▸ hy

/-- **Frontier classes.** Along a layout of the compiled network, the inputs with a given
output and given values on the frontier at time `t` form a rectangle for the cut of the inputs
read before time `t`. -/
theorem sq_corr_mul_le_of_layout (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (π : Layout (Compiler.Vertex c.program c.outputs)) {t : ℕ}
    (ht : t ≤ Nat.card (Compiler.Vertex c.program c.outputs)) :
    (2 * agreement (quadForm Q) (fun x => c.eval I x 0) - 1) ^ 2 *
        2 ^ cutRank Q ((constraintNetwork I {true} c).readIn (π.initial t)) ≤
      2 * 2 ^ ((constraintNetwork I {true} c).frontier π t).ncard := by
  classical
  set F := (constraintNetwork I {true} c).frontier π t
  set X := (constraintNetwork I {true} c).readIn (π.initial t)
  have : Fintype F := Fintype.ofFinite F
  let msg : (Fin n → Bool) → Bool × (F → Bool) := fun x =>
    (c.eval I x 0, F.domRestrict ((constraintNetwork I {c.eval I x 0} c).witness x))
  have H := sq_two_mul_agreement_sub_one_mul_le Q (fun x => c.eval I x 0) msg X
    (fun _ _ h => (Prod.ext_iff.mp h).1) ?_
  · have hM : Fintype.card (Bool × (F → Bool)) = 2 * 2 ^ F.ncard := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq]
    rw [hM] at H
    exact_mod_cast H
  intro x₀
  set b := c.eval I x₀ 0 with hb
  set N := constraintNetwork I {b} c
  have Hu : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β :=
    fun x α β hα hβ => funext fun e => (Compiler.eq_trace hα e).trans (Compiler.eq_trace hβ e).symm
  have hpeers := Sweep.Coherent.peers_eq_rectangle _ (N.sweep_coherent π Hu) t x₀
  have hrev : (N.sweep π).revealed t = X := by
    change N.revealedBy π t = X
    simp only [Network.revealedBy, ht, ite_true]
    rfl
  have hclass : {x | msg x = msg x₀} = (N.sweep π).peers t x₀ := by
    ext x
    simp only [mem_ofPred_eq, msg, Prod.mk.injEq, Sweep.peers]
    change _ ↔ x ∈ N.accepted ∧ ((), N.frontierValues π t (N.witness x)) =
      ((), N.frontierValues π t (N.witness x₀))
    rw [accepted_constraintNetwork_eval, Prod.mk.injEq, Network.frontierValues_eq_iff,
      domRestrict_eq_domRestrict_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, rfl, ?_⟩
      rw [h1] at h2
      exact h2
    · rintro ⟨h1, -, h2⟩
      refine ⟨h1, ?_⟩
      rw [h1]
      exact h2
  rw [hclass, hpeers]
  have key : ∀ (Y : Set (Fin n)), Y = X → ∀ (A : Set (Y → Bool)) (B : Set (↥Yᶜ → Bool)),
      ∃ (A' : Set (X → Bool)) (B' : Set (↥Xᶜ → Bool)), rectangle Y A B = rectangle X A' B' := by
    rintro Y rfl A B
    exact ⟨A, B, rfl⟩
  exact key _ hrev _ _

/-- **Small sets have large cut rank.** If every set of `⌊n/2⌋` coordinates has cut rank at
least `⌊n/2⌋ - e`, then every set `D` of at most `⌊n/2⌋` coordinates has cut rank at least
`|D| - e`. -/
theorem ncard_le_cutRank_add_of_bisection (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ cutRank Q U + e)
    {D : Set (Fin n)} (hD : D.ncard ≤ n / 2) : (D.ncard : ℝ) ≤ cutRank Q D + e := by
  obtain ⟨U, hDU, -, hU⟩ := exists_subsuperset_card_eq (subset_univ D) hD
    (by rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have h₁ := cutRank_le_add (Q := Q) hDU
  rw [ncard_sdiff hDU, hU] at h₁
  have h₂ : cutRank Q U + D.ncard ≤ cutRank Q D + n / 2 := by
    have := ncard_le_ncard hDU
    omega
  have h₃ := hQ U hU
  have h₄ : (cutRank Q U : ℝ) + D.ncard ≤ cutRank Q D + (n / 2 : ℕ) := by exact_mod_cast h₂
  linarith

/-- A bound `y · 2^ρ ≤ 2 · 2^m` with `ρ ≥ r` gives `y ≤ 2^(1 + m - r)` in real exponents. -/
theorem le_rpow_of_mul_two_pow_le {y : ℝ} {ρ m : ℕ} {r : ℝ} (hy : y * 2 ^ ρ ≤ 2 * 2 ^ m)
    (hr : r ≤ ρ) : y ≤ (2 : ℝ) ^ (1 + m - r) := by
  have hpos : (0 : ℝ) < 2 ^ ρ := by positivity
  have h1 : y ≤ 2 * 2 ^ m / 2 ^ ρ := (le_div_iff₀ hpos).mpr hy
  have h2 : (2 * 2 ^ m / 2 ^ ρ : ℝ) = (2 : ℝ) ^ ((1 + m - ρ : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [h2] at h1
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

/-- **Theorem (unread inputs, finite).** Under the bisection hypothesis, a circuit that leaves
at least `k ≤ ⌊n/2⌋` inputs unread has squared correlation at most `2^(1 + e - k)`. -/
theorem sq_corr_le_of_unread (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ cutRank Q U + e)
    {k : ℕ} (hk : k ≤ n / 2) (hkd : k ≤ (constraintNetwork I {true} c).readᶜ.ncard) :
    (2 * agreement (quadForm Q) (fun x => c.eval I x 0) - 1) ^ 2 ≤ (2 : ℝ) ^ (1 + e - k) := by
  obtain ⟨D, hD, hDk⟩ := exists_subset_card_eq hkd
  have hρ := ncard_le_cutRank_add_of_bisection Q hQ (D := D) (by omega)
  have H := sq_corr_mul_le_of_unread I c Q hD
  have H' : (2 * agreement (quadForm Q) (fun x => c.eval I x 0) - 1) ^ 2 * 2 ^ cutRank Q D ≤
      2 * 2 ^ (0 : ℕ) := by simpa using H
  have := le_rpow_of_mul_two_pow_le H' (r := k - e) (by rw [hDk] at hρ; linarith)
  convert this using 2
  push_cast
  ring

/-- **Theorem (frontier, finite).** Under the bisection hypothesis, if a circuit reads at least
`⌊n/2⌋` inputs and its compiled network has a layout with every frontier of at most `w` edges,
its squared correlation is at most `2^(1 + w + e - ⌊n/2⌋)`. -/
theorem sq_corr_le_of_layout (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {e : ℝ}
    (hQ : ∀ U : Set (Fin n), U.ncard = n / 2 → ((n / 2 : ℕ) : ℝ) ≤ cutRank Q U + e)
    (π : Layout (Compiler.Vertex c.program c.outputs)) {w : ℕ}
    (hw : ∀ t, ((constraintNetwork I {true} c).frontier π t).ncard ≤ w)
    (hread : n / 2 ≤ (constraintNetwork I {true} c).read.ncard) :
    (2 * agreement (quadForm Q) (fun x => c.eval I x 0) - 1) ^ 2 ≤
      (2 : ℝ) ^ (1 + w + e - (n / 2 : ℕ)) := by
  obtain ⟨t, ht, hX⟩ := exists_ncard_readIn_eq (constraintNetwork I {true} c) π
    (Compiler.ncard_readAt_le I _) hread
  have H := sq_corr_mul_le_of_layout I c Q π ht
  have H' : (2 * agreement (quadForm Q) (fun x => c.eval I x 0) - 1) ^ 2 *
      2 ^ cutRank Q ((constraintNetwork I {true} c).readIn (π.initial t)) ≤ 2 * 2 ^ w :=
    H.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (hw t)) (by norm_num))
  have hρ := hQ _ hX
  have := le_rpow_of_mul_two_pow_le H' (r := (n / 2 : ℕ) - e) (by linarith)
  convert this using 2
  ring

end Complexity.Correlation

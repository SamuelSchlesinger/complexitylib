/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Cheeger
public import Complexitylib.Classes.PCP.Internal.PermCount

/-!
# Graphs built from permutations

A tuple of `D` permutations of `Fin n` gives a `2 D`-regular graph: at each
vertex, every permutation contributes a forward dart to its image and a
backward dart to its preimage. Reversal swaps the two, so the rotation map is
an involution with no bookkeeping.

This is the shape in which the expander family is obtained: the permutations
are chosen by counting (a random tuple works), and this module supplies the
translation from a statement about permutations — *some* permutation moves a
constant fraction of any small set out of itself — to the edge expansion the
Cheeger bound consumes.

## Main definitions

- `Complexity.RegGraph.permsGraph` — the `2 D`-regular graph of a tuple
- `Complexity.escape` — how many points of a set a permutation moves out of it

## Main results

- `Complexity.RegGraph.edgeExpansion_permsGraph` — a lower bound on escape for
  every small set gives edge expansion
-/

@[expose] public section

namespace Complexity

variable {n D : ℕ}

namespace RegGraph

/-- The rotation map of a tuple of permutations: a forward dart becomes the
matching backward dart at the image, and conversely. -/
def permsRot (σ : Fin D → Equiv.Perm (Fin n)) :
    Fin n × (Fin D × Bool) → Fin n × (Fin D × Bool) :=
  fun p => if p.2.2 then ((σ p.2.1).symm p.1, (p.2.1, false))
    else (σ p.2.1 p.1, (p.2.1, true))

theorem permsRot_involutive (σ : Fin D → Equiv.Perm (Fin n)) :
    Function.Involutive (permsRot σ) := by
  intro p
  obtain ⟨v, i, b⟩ := p
  cases b with
  | false => simp [permsRot]
  | true => simp [permsRot]

/-- **The graph of a tuple of permutations**, of degree `2 D`. -/
def permsGraph (hD : 0 < D) (σ : Fin D → Equiv.Perm (Fin n)) : RegGraph where
  V := Fin n
  D := Fin D × Bool
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := ⟨(⟨0, hD⟩, false)⟩
  rot := permsRot σ
  rot_involutive := permsRot_involutive σ

@[simp] theorem order_permsGraph (hD : 0 < D) (σ : Fin D → Equiv.Perm (Fin n)) :
    (permsGraph hD σ).order = n := Fintype.card_fin n

theorem deg_permsGraph (hD : 0 < D) (σ : Fin D → Equiv.Perm (Fin n)) :
    (permsGraph hD σ).deg = 2 * D := by
  show Fintype.card (Fin D × Bool) = 2 * D
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem nbr_permsGraph_false (hD : 0 < D) (σ : Fin D → Equiv.Perm (Fin n))
    (v : Fin n) (i : Fin D) : (permsGraph hD σ).nbr v (i, false) = σ i v := rfl

/-- **Forward darts leave.** The darts of the graph that leave `S` include, for
every permutation, one for each point of `S` that permutation moves out. -/
theorem sum_escape_le_dartsBetween (hD : 0 < D) (σ : Fin D → Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    ∑ i : Fin D, escape (σ i) S
      ≤ ((permsGraph hD σ).dartsBetween S Sᶜ).card := by
  classical
  set E : Finset (Fin D × Fin n) :=
    Finset.univ.filter fun p => p.2 ∈ S ∧ σ p.1 p.2 ∉ S with hE
  have hone : ∀ i : Fin D, (∑ v : Fin n, if v ∈ S ∧ σ i v ∉ S then (1 : ℕ) else 0)
      = escape (σ i) S := by
    intro i
    rw [escape, Finset.card_filter]
    simp only [ite_and]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hcard : E.card = ∑ i : Fin D, escape (σ i) S := by
    rw [hE, Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hone i
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => (p.2, (p.1, false))) (fun p hp => ?_) ?_
  · have hp' : p.2 ∈ S ∧ σ p.1 p.2 ∉ S := by simpa [hE] using hp
    have hmem : ((p.2, (p.1, false)) : (permsGraph hD σ).V × (permsGraph hD σ).D)
        ∈ (permsGraph hD σ).dartsBetween S Sᶜ := by
      simp only [RegGraph.dartsBetween, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨hp'.1, Finset.mem_compl.2 hp'.2⟩
    simpa using hmem
  · intro p _ q _ h
    have h1 : p.2 = q.2 := congrArg Prod.fst h
    have h2 : p.1 = q.1 := congrArg (fun x => x.2.1) h
    exact Prod.ext h2 h1

/-- **From escape to expansion.** If every nonempty set of at most half the
vertices is moved out of itself by some permutation, in at least a `1 / c`
fraction, the graph has edge expansion `1 / (2 c D)`. -/
theorem edgeExpansion_permsGraph (hD : 0 < D) (σ : Fin D → Equiv.Perm (Fin n)) (c : ℕ)
    (hc : 0 < c)
    (hesc : ∀ S : Finset (Fin n), 2 * S.card ≤ n → ∃ i : Fin D, S.card ≤ c * escape (σ i) S) :
    (permsGraph hD σ).EdgeExpansion (1 / (2 * (c : ℝ) * D)) := by
  classical
  intro S hS
  rw [order_permsGraph] at hS
  obtain ⟨i, hi⟩ := hesc S hS
  have hcD : (0 : ℝ) < 2 * (c : ℝ) * D := by
    positivity
  have hsum : (escape (σ i) S : ℝ) ≤ ∑ j : Fin D, (escape (σ j) S : ℝ) := by
    refine Finset.single_le_sum (f := fun j => (escape (σ j) S : ℝ)) (fun j _ => ?_)
      (Finset.mem_univ i)
    positivity
  have hbound : (∑ j : Fin D, (escape (σ j) S : ℝ))
      ≤ (((permsGraph hD σ).dartsBetween S Sᶜ).card : ℝ) := by
    have := sum_escape_le_dartsBetween hD σ S
    exact_mod_cast this
  have hi' : (S.card : ℝ) ≤ (c : ℝ) * (escape (σ i) S : ℝ) := by exact_mod_cast hi
  rw [deg_permsGraph]
  have hrw : 1 / (2 * (c : ℝ) * D) * ((2 * D : ℕ) : ℝ) * (S.card : ℝ)
      = (S.card : ℝ) / (c : ℝ) := by
    push_cast
    field_simp
  rw [hrw]
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [div_le_iff₀ hc']
  have hfin : (escape (σ i) S : ℝ) ≤ (((permsGraph hD σ).dartsBetween S Sᶜ).card : ℝ) :=
    le_trans hsum hbound
  nlinarith [hi', hfin, hc']

end RegGraph

end Complexity

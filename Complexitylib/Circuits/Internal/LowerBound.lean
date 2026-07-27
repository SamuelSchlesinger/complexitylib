/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Complexitylib.Circuits.EssentialInput
public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.Dependency.Defs

/-! # Internal: Gate Elimination Lower Bound

This internal module proves the gate elimination lower bound: for any circuit
over a bounded fan-in k AND/OR basis, if the computed function depends on n'
essential variables, the circuit has size at least ⌈n'/k⌉.

The public definitions (`IsEssentialInput`, `essentialInputs`) are in
`Complexitylib.Circuits.EssentialInput`. The public theorems
(`card_essentialInputs_le_mul_size`, `le_mul_size_of_forall_isEssentialInput`)
are stated in
`Complexitylib.Circuits.LowerBound`.
-/

@[expose] public section

namespace Complexity

namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-! ## Core insensitivity lemma -/

/-- If no internal gate reads primary input `i`, wire values at wires
    other than `i` are unchanged when input `i` is modified. -/
private theorem wireValue_eq_of_unreferenced
    (c : Circuit B N M G) (i : Fin N) (b : Bool)
    (hno : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (x : BitString N) (w : Fin (N + G)) (hw : w.val ≠ i.val) :
    c.wireValue x w = c.wireValue (Function.update x i b) w := by
  by_cases h : w.val < N
  · -- Primary input wire, not wire i
    rw [wireValue_of_lt c x w h, wireValue_of_lt c _ w h]
    have hne : (⟨w.val, h⟩ : Fin N) ≠ i := fun heq => hw (congrArg Fin.val heq)
    exact (Function.update_of_ne hne b x).symm
  · -- Gate output wire: recurse on fan-in wires
    have hG : w.val - N < G := by omega
    rw [wireValue_of_not_lt c x w h, wireValue_of_not_lt c _ w h]
    simp only [Gate.eval]
    congr 1; funext k; congr 1
    exact wireValue_eq_of_unreferenced c i b hno x _ (hno ⟨w.val - N, hG⟩ k)
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- If no gate (internal or output) reads primary input `i`, the circuit
    output is unchanged when input `i` is modified. -/
private theorem eval_eq_of_unreferenced
    (c : Circuit B N M G) (i : Fin N) (b : Bool)
    (hno_gates : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (hno_outputs : ∀ j : Fin M, ∀ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val ≠ i.val)
    (x : BitString N) :
    c.eval x = c.eval (Function.update x i b) := by
  funext j; simp only [eval, Gate.eval]
  congr 1; funext k; congr 1
  exact wireValue_eq_of_unreferenced c i b hno_gates x _ (hno_outputs j k)

/-! ## Essential variables must be read -/

/-- If `c` computes `f` and `f` depends on variable `i`, some gate
    (internal or output) directly reads input wire `i`. -/
private theorem exists_gate_reads_input
    (c : Circuit B N M G) (f : BitString N → BitString M)
    (hf : c.eval = f) (i : Fin N) (hdep : IsEssentialInput f i) :
    (∃ g : Fin G, ∃ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val = i.val) ∨
    (∃ j : Fin M, ∃ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val = i.val) := by
  by_contra h
  push Not at h
  obtain ⟨hg, ho⟩ := h
  obtain ⟨x, hx⟩ := hdep
  exact hx (hf ▸ eval_eq_of_unreferenced c i _ hg ho x)

/-! ## Counting argument -/

/-- The set of primary inputs directly wired into a gate. -/
private def coveredInputs (g : Gate B (N + G)) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N =>
    ∃ k : Fin g.fanIn, (g.inputs k).val = i.val

omit [NeZero N] in
/-- Membership in `coveredInputs`: input `i` is covered by gate `g` iff some
    fan-in wire of `g` is the primary input wire `i`. -/
private theorem mem_coveredInputs (g : Gate B (N + G)) (i : Fin N) :
    i ∈ coveredInputs g ↔ ∃ k : Fin g.fanIn, (g.inputs k).val = i.val := by
  simp [coveredInputs]

/-- A gate covers at most `fanIn`-many primary inputs. -/
private theorem card_coveredInputs_le (g : Gate B (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ g.fanIn := by
  -- coveredInputs is contained in the image of a map from Fin g.fanIn
  suffices coveredInputs g ⊆
      (Finset.univ : Finset (Fin g.fanIn)).image
        (fun k => if h : (g.inputs k).val < N
          then ⟨(g.inputs k).val, h⟩
          else ⟨0, NeZero.pos N⟩) by
    calc (coveredInputs g).card
        ≤ _ := Finset.card_le_card this
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = g.fanIn := by simp
  intro i hi
  rw [mem_coveredInputs] at hi
  obtain ⟨k, hk⟩ := hi
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨k, ?_⟩
  have hlt : (g.inputs k).val < N := by omega
  simp [hk]

omit [NeZero N] in
/-- Every gate over the bounded AND/OR basis has fan-in at most `k`. -/
private theorem fanIn_le_of_boundedAndOr {k : Nat}
    (g : Gate (Basis.boundedAndOr k) (N + G)) :
    g.fanIn ≤ k := by
  have h := g.arityOk
  revert h
  cases g.op <;>
    simp [Basis.boundedAndOr, Arity.satisfiedBy]

/-- Gate accessor for internal and output gates uniformly. -/
private def gateAt (c : Circuit B N M G) : Fin G ⊕ Fin M → Gate B (N + G)
  | .inl g => c.gates g
  | .inr j => c.outputs j

/-- Every essential variable is covered by some gate. -/
private theorem essentialInputs_subset_biUnion_coveredInputs
    (c : Circuit B N M G) (f : BitString N → BitString M)
    (hf : c.eval = f) :
    essentialInputs f ⊆ (Finset.univ : Finset (Fin G ⊕ Fin M)).biUnion
      (fun idx => coveredInputs (gateAt c idx)) := by
  intro i hi
  simp only [essentialInputs, Finset.mem_filter] at hi
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rcases exists_gate_reads_input c f hf i hi.2 with ⟨g, k, hk⟩ | ⟨j, k, hk⟩
  · exact ⟨.inl g, (mem_coveredInputs _ _).mpr ⟨k, hk⟩⟩
  · exact ⟨.inr j, (mem_coveredInputs _ _).mpr ⟨k, hk⟩⟩

/-- **Generic counting bound**: every essential variable consumes at least one
gate-input occurrence, so their number is bounded by total fan-in. -/
theorem card_essentialInputs_le_totalFanIn_internal
    (c : Circuit B N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (essentialInputs f).card ≤ c.totalFanIn := by
  calc (essentialInputs f).card
      ≤ ((Finset.univ : Finset (Fin G ⊕ Fin M)).biUnion
          (fun idx => coveredInputs (gateAt c idx))).card :=
        Finset.card_le_card (essentialInputs_subset_biUnion_coveredInputs c f hf)
    _ ≤ ∑ idx : Fin G ⊕ Fin M,
          (coveredInputs (gateAt c idx)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ idx : Fin G ⊕ Fin M, (gateAt c idx).fanIn :=
        Finset.sum_le_sum fun idx _ => card_coveredInputs_le _
    _ = c.totalFanIn := by
        simp [gateAt, totalFanIn]

/-- If every input is essential, total fan-in is at least the input arity. -/
theorem le_totalFanIn_of_forall_isEssentialInput_internal
    (c : Circuit B N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f)
    (hall : ∀ i : Fin N, IsEssentialInput f i) :
    N ≤ c.totalFanIn := by
  have hcard : (essentialInputs f).card = N := by
    have : essentialInputs f = Finset.univ := by
      simp [essentialInputs, Finset.filter_true_of_mem (fun i _ => hall i)]
    rw [this, Finset.card_univ, Fintype.card_fin]
  calc N = (essentialInputs f).card := hcard.symm
    _ ≤ c.totalFanIn :=
      card_essentialInputs_le_totalFanIn_internal c f hf

private theorem totalFanIn_le_mul_size_of_boundedAndOr {k : Nat}
    (c : Circuit (Basis.boundedAndOr k) N M G) :
    c.totalFanIn ≤ k * c.size := by
  unfold totalFanIn
  calc
    (∑ i, (c.gates i).fanIn) + ∑ j, (c.outputs j).fanIn
        ≤ (∑ _ : Fin G, k) + ∑ _ : Fin M, k :=
      Nat.add_le_add
        (Finset.sum_le_sum fun i _ =>
          fanIn_le_of_boundedAndOr (c.gates i))
        (Finset.sum_le_sum fun j _ =>
          fanIn_le_of_boundedAndOr (c.outputs j))
    _ = k * c.size := by
      simp [size, Nat.mul_add, Nat.mul_comm]

/-- **Bounded-fan-in corollary**: the number of essential variables is at
most `k` times circuit size. -/
theorem card_essentialInputs_le_mul_size_internal {k : Nat}
    (c : Circuit (Basis.boundedAndOr k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (essentialInputs f).card ≤ k * c.size :=
  (card_essentialInputs_le_totalFanIn_internal c f hf).trans
    (totalFanIn_le_mul_size_of_boundedAndOr c)

/-- If every input is essential in the bounded-fan-in setting, then
`N ≤ k * size`. -/
theorem le_mul_size_of_forall_isEssentialInput_internal {k : Nat}
    (c : Circuit (Basis.boundedAndOr k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f)
    (hall : ∀ i : Fin N, IsEssentialInput f i) :
    N ≤ k * c.size :=
  (le_totalFanIn_of_forall_isEssentialInput_internal c f hf hall).trans
    (totalFanIn_le_mul_size_of_boundedAndOr c)

end Circuit

end Complexity

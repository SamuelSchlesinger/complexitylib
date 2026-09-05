/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph
public import Complexitylib.Classes.PCP.Internal.CubeBlocks
public import Complexitylib.Classes.PCP.Internal.NumEnc

/-!
# From a many-query test to a binary constraint graph

An assignment tester reads a handful of positions of its proof per random
string, but a constraint graph checks *two* vertices per edge. The standard
repair is to add a vertex for each random string, labelled by the answers the
tester expects to see, and to connect it to each position it reads: the edge
checks that the claimed answer matches the position's actual bit and that the
claimed answers together pass the test. A rejecting random string then has at
least one of its `q` edges violated — either the claimed answers fail the test
outright, or they pass and so must disagree with the proof somewhere.

This module carries out that transformation for a **family** of tests indexed by
a type `E` — one per edge of the outer graph, in the composition — over a shared
set of positions. The edges of the result are the triples `(e, z, i)`: test `e`,
random string `z`, read `i`.

## Main definitions

- `Complexity.MultiTest` — a family of many-query tests on a shared proof
- `Complexity.MultiTest.toGraph` — the binary constraint graph

## Main results

- `Complexity.MultiTest.card_rejects_le_card_unsatEdges` — every rejecting
  random string accounts for a distinct violated edge
- `Complexity.MultiTest.satisfiable_toGraph` — a proof accepted everywhere
  gives a satisfying assignment
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

/-- A family of tests, indexed by `E`, reading a shared proof over positions
`Pos`. A test uses `R` random bits, reads `q` positions chosen from its random
string, and decides from the bits it read. -/
structure MultiTest (Pos E Q : Type) where
  /-- The number of random bits. -/
  R : ℕ
  /-- The positions read, indexed by `Q`, as a function of the test and its
  random string. -/
  pos : E → Cube R → Q → Pos
  /-- The verdict, as a function of the bits read. -/
  check : E → Cube R → (Q → ZMod 2) → Bool

namespace MultiTest

variable {Pos E Q : Type} (M : MultiTest Pos E Q)

/-- A proof: one bit per position. -/
abbrev Table (Pos : Type) : Type := Pos → ZMod 2

/-- Test `e` accepts the proof `T` on random string `z`. -/
def accepts (T : Table Pos) (e : E) (z : Cube M.R) : Bool :=
  M.check e z fun i => T (M.pos e z i)

/-- The random strings on which test `e` rejects `T`. -/
def rejects (T : Table Pos) (e : E) : Finset (Cube M.R) :=
  Finset.univ.filter fun z => M.accepts T e z = false

/-! ### The binary graph -/

/-- The vertices of the binary graph: the positions, and one vertex per
(test, random string). -/
abbrev Vert : Type := Pos ⊕ (E × Cube M.R)

/-- The edges: one per (test, random string, read). -/
abbrev Edge : Type := E × Cube M.R × Q

/-- The alphabet: a bit (used at positions) paired with a tuple of claimed
answers (used at test vertices). -/
abbrev Alpha (Q : Type) : Type := ZMod 2 × (Q → ZMod 2)

/-- A random string is numbered by its own enumeration: the number of random
bits is a constant, so this is a lookup on a bounded key. -/
noncomputable instance (priority := 2000) instNumEncCube (n : ℕ) : NumEnc (Cube n) :=
  NumEnc.ofFintype _

section Graph

variable [Fintype Pos] [Fintype E] [Fintype Q] [NumEnc Pos] [NumEnc E] [NumEnc Q]

/-- The edge a `Fin` index stands for. -/
noncomputable def edgeOf (k : Fin (Fintype.card M.Edge)) : M.Edge :=
  (NumEnc.equivFinCard M.Edge).symm k

/-- The `Fin` index of a vertex. -/
noncomputable def vertIdx (v : M.Vert) : Fin (Fintype.card M.Vert) :=
  NumEnc.equivFinCard M.Vert v

/-- **The binary constraint graph.** Edge `(e, z, i)` runs from the test vertex
`(e, z)` to the position `pos e z i`, and holds when the test vertex's claimed
answers pass test `e` on `z` and its `i`-th claimed answer is the position's
bit. -/
noncomputable def toGraph : ConstraintGraph (Alpha Q) where
  numVerts := Fintype.card M.Vert
  numEdges := Fintype.card M.Edge
  tail := fun k => M.vertIdx (Sum.inr ((M.edgeOf k).1, (M.edgeOf k).2.1))
  head := fun k => M.vertIdx (Sum.inl (M.pos (M.edgeOf k).1 (M.edgeOf k).2.1 (M.edgeOf k).2.2))
  rel := fun k l₁ l₂ =>
    decide (M.check (M.edgeOf k).1 (M.edgeOf k).2.1 l₁.2 = true
      ∧ l₁.2 (M.edgeOf k).2.2 = l₂.1)

/-- The proof an assignment of the binary graph carries at its positions. -/
noncomputable def tableOf (A : M.toGraph.Assignment) : Table Pos :=
  fun p => (A (M.vertIdx (Sum.inl p))).1

/-- The constraint of edge `(e, z, i)`, spelled out. -/
theorem satisfies_toGraph_iff (A : M.toGraph.Assignment) (k : Fin (Fintype.card M.Edge)) :
    M.toGraph.Satisfies A k ↔
      (M.check (M.edgeOf k).1 (M.edgeOf k).2.1
          (A (M.vertIdx (Sum.inr ((M.edgeOf k).1, (M.edgeOf k).2.1)))).2 = true
        ∧ (A (M.vertIdx (Sum.inr ((M.edgeOf k).1, (M.edgeOf k).2.1)))).2 (M.edgeOf k).2.2
          = M.tableOf A (M.pos (M.edgeOf k).1 (M.edgeOf k).2.1 (M.edgeOf k).2.2)) := by
  show decide _ = true ↔ _
  rw [decide_eq_true_iff]
  rfl

/-- The `Fin` index of an edge. -/
noncomputable def edgeIdx (x : M.Edge) : Fin (Fintype.card M.Edge) :=
  NumEnc.equivFinCard M.Edge x

omit [Fintype Pos] [NumEnc Pos] in
@[simp] theorem edgeOf_edgeIdx (x : M.Edge) : M.edgeOf (M.edgeIdx x) = x :=
  Equiv.symm_apply_apply _ _

/-- **A rejecting random string has a violated edge.** Either the claimed
answers fail the test, so every edge of the string is violated, or they pass and
therefore differ from the proof at some read. (With no reads there would be no
edges, so the test must read at least once.) -/
theorem exists_unsat_of_rejects [Nonempty Q] (A : M.toGraph.Assignment) (e : E)
    (z : Cube M.R) (hz : z ∈ M.rejects (M.tableOf A) e) :
    ∃ i : Q, ¬ M.toGraph.Satisfies A (M.edgeIdx (e, z, i)) := by
  classical
  simp only [rejects, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  by_contra hall
  push Not at hall
  have hq' : ∀ i, (A (M.vertIdx (Sum.inr (e, z)))).2 i = M.tableOf A (M.pos e z i) :=
    fun i => by
      have h := (M.satisfies_toGraph_iff A (M.edgeIdx (e, z, i))).1 (hall i)
      simp only [edgeOf_edgeIdx] at h
      exact h.2
  obtain ⟨i₀⟩ := ‹Nonempty Q›
  have h := (M.satisfies_toGraph_iff A (M.edgeIdx (e, z, i₀))).1 (hall i₀)
  simp only [edgeOf_edgeIdx] at h
  have hcheck : M.check e z (A (M.vertIdx (Sum.inr (e, z)))).2 = true := h.1
  rw [funext hq'] at hcheck
  have hz' : M.check e z (fun i => M.tableOf A (M.pos e z i)) = false := hz
  rw [hz'] at hcheck
  exact Bool.false_ne_true hcheck

/-- A violated edge chosen for each rejecting string. -/
noncomputable def witnessEdge [Nonempty Q] (A : M.toGraph.Assignment)
    (x : E × Cube M.R) : Fin (Fintype.card M.Edge) :=
  if h : x.2 ∈ M.rejects (M.tableOf A) x.1 then
    M.edgeIdx (x.1, x.2, Classical.choose (M.exists_unsat_of_rejects A x.1 x.2 h))
  else M.edgeIdx (x.1, x.2, Classical.arbitrary Q)

theorem witnessEdge_mem [Nonempty Q] (A : M.toGraph.Assignment) (x : E × Cube M.R)
    (hx : x.2 ∈ M.rejects (M.tableOf A) x.1) :
    M.witnessEdge A x ∈ M.toGraph.unsatEdges A := by
  classical
  rw [witnessEdge, dite_eq_left hx]
  erw [ConstraintGraph.mem_unsatEdges]
  exact Classical.choose_spec (M.exists_unsat_of_rejects A x.1 x.2 hx)

theorem witnessEdge_injective [Nonempty Q] (A : M.toGraph.Assignment) :
    Function.Injective (M.witnessEdge A) := by
  intro x y hxy
  have hx : M.edgeOf (M.witnessEdge A x) = M.edgeOf (M.witnessEdge A y) := by rw [hxy]
  simp only [witnessEdge] at hx
  split_ifs at hx <;> simp only [edgeOf_edgeIdx, Prod.mk.injEq] at hx <;>
    exact Prod.ext hx.1 hx.2.1

/-- The set of rejecting (test, random string) pairs. -/
def rejectPairs (T : Table Pos) : Finset (E × Cube M.R) :=
  Finset.univ.filter fun x => x.2 ∈ M.rejects T x.1

omit [Fintype Pos] [Fintype Q] [NumEnc Pos] [NumEnc E] [NumEnc Q] in
theorem card_rejectPairs (T : Table Pos) :
    (M.rejectPairs T).card = ∑ e : E, (M.rejects T e).card := by
  classical
  rw [rejectPairs, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  congr 1
  ext z
  simp

/-- **Rejections are counted by violated edges.** -/
theorem card_rejects_le_card_unsatEdges [Nonempty Q] (A : M.toGraph.Assignment) :
    ∑ e : E, (M.rejects (M.tableOf A) e).card ≤ (M.toGraph.unsatEdges A).card := by
  classical
  rw [← card_rejectPairs]
  refine Finset.card_le_card_of_injOn (M.witnessEdge A) ?_
    (M.witnessEdge_injective A).injOn
  intro x hx
  have hx' : x.2 ∈ M.rejects (M.tableOf A) x.1 := by
    have := Finset.mem_coe.1 hx
    simpa [rejectPairs] using this
  exact M.witnessEdge_mem A x hx'

theorem numEdges_toGraph : M.toGraph.numEdges = Fintype.card E * 2 ^ M.R * Fintype.card Q := by
  show Fintype.card (E × Cube M.R × Q) = _
  rw [Fintype.card_prod, Fintype.card_prod]
  have hc : Fintype.card (Cube M.R) = 2 ^ M.R := by
    show Fintype.card (Fin M.R → ZMod 2) = 2 ^ M.R
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hc, mul_assoc]

/-- **Soundness of the transformation.** The violated fraction of the binary
graph is at least the average rejection probability of the tests, divided by
the number of reads. -/
theorem unsatFrac_toGraph_ge [Nonempty Q] (A : M.toGraph.Assignment) :
    (∑ e : E, ((M.rejects (M.tableOf A) e).card : ℚ))
        / ((Fintype.card E : ℚ) * 2 ^ M.R * Fintype.card Q)
      ≤ M.toGraph.unsatFrac A := by
  classical
  have h := M.card_rejects_le_card_unsatEdges A
  have hE : (M.toGraph.numEdges : ℚ)
      = (Fintype.card E : ℚ) * 2 ^ M.R * Fintype.card Q := by
    rw [numEdges_toGraph]; push_cast; ring
  rw [ConstraintGraph.unsatFrac, hE]
  gcongr
  exact_mod_cast h

/-! ### Completeness -/

/-- The honest assignment: positions carry the proof, test vertices carry the
answers the proof gives. -/
noncomputable def honest (T : Table Pos) : M.toGraph.Assignment := fun v =>
  match (NumEnc.equivFinCard M.Vert).symm v with
  | Sum.inl p => (T p, fun _ => 0)
  | Sum.inr (e, z) => (0, fun i => T (M.pos e z i))

theorem honest_inl (T : Table Pos) (p : Pos) :
    M.honest T (M.vertIdx (Sum.inl p)) = (T p, fun _ => 0) := by
  simp [honest, vertIdx]

theorem honest_inr (T : Table Pos) (x : E × Cube M.R) :
    M.honest T (M.vertIdx (Sum.inr x)) = (0, fun i => T (M.pos x.1 x.2 i)) := by
  simp [honest, vertIdx]

/-- **Completeness.** A proof accepted by every test on every random string
gives a satisfying assignment of the binary graph. -/
theorem satisfiable_toGraph (T : Table Pos) (h : ∀ e z, M.accepts T e z = true) :
    M.toGraph.Satisfiable := by
  classical
  refine ⟨M.honest T, fun k => ?_⟩
  erw [satisfies_toGraph_iff]
  refine ⟨?_, ?_⟩
  · rw [honest_inr]
    exact h _ _
  · rw [honest_inr]
    show T _ = (M.honest T (M.vertIdx (Sum.inl _))).1
    rw [honest_inl]

end Graph

/-- The acceptance probability of a test, as a count of rejections. -/
theorem prob_accepts_eq (T : Table Pos) (e : E) :
    Pr[fun z : Cube M.R => M.accepts T e z = true]
      = 1 - ((M.rejects T e).card : ℝ) / 2 ^ M.R := by
  classical
  rw [prob_eq_card_div]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Cube M.R))) (fun z => M.accepts T e z = true)
  have hrej : (M.rejects T e).card
      = (Finset.univ.filter fun z => ¬ (M.accepts T e z = true)).card := by
    congr 1
    ext z
    simp [rejects]
  rw [hrej]
  have hcard : (Finset.univ : Finset (Cube M.R)).card = 2 ^ M.R := by
    rw [Finset.card_univ]
    show Fintype.card (Fin M.R → ZMod 2) = 2 ^ M.R
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard] at hsplit
  have hpos : (0 : ℝ) < 2 ^ M.R := by positivity
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast hsplit

end MultiTest

end Complexity

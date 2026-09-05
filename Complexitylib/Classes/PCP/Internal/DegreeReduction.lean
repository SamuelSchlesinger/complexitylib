/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph
public import Complexitylib.Classes.PCP.Internal.NumEnc
public import Complexitylib.Classes.PCP.Internal.Expander
public import Complexitylib.Classes.PCP.Internal.RegCSP

/-!
# Degree reduction

The first half of Dinur's preprocessing: an arbitrary constraint graph, whose
vertices may have wildly different degrees, is replaced by a *regular* one over
the same alphabet.

The vertices of the new graph are the **half-edges** of the old one — an edge
together with one of its endpoints — so there are exactly `2 · numEdges` of
them, however lopsided the original degrees were. Each half-edge has

* one **edge-link**, to the other half of its own edge, carrying that edge's
  original constraint, and
* `E.degree` **cloud-links**, wiring together the half-edges that share an
  endpoint, by a member of an `ExpanderFamily`, carrying equality constraints.

So the result is `(1 + E.degree)`-regular by construction, with no padding, and
its size is a constant multiple of the original's — which is what the
amplification bookkeeping needs.

## The cloud rotation, without dependent types

A cloud's expander lives on `Fin (cloud size)`, and cloud sizes differ, so the
naive rotation map forces a transport along `owner p' = owner p` that is not
type-correct to rewrite. The fix is `cloudRotAux`, which takes the cloud's
enumeration `l` as a *parameter*: within it the length is fixed, and
involutivity is an ordinary argument about a `Nodup` list. At the top level the
only rewriting needed is `cloudList (owner p') = cloudList (owner p)`, an
equation between plain lists with no dependent type in sight.

## Main definitions

- `ConstraintGraph.owner`, `flipHalf`, `cloud`, `cloudList` — the cloud
  structure on half-edges
- `ConstraintGraph.cloudRotAux`, `cloudRot` — the cloud-link rotation
- `ConstraintGraph.reduceGraph`, `reduce` — the regular graph and system

## Main results

- `ConstraintGraph.cloudRotAux_involutive`, `cloudRot_involutive`
- `ConstraintGraph.cloudRot_getElem` — a cloud, read through its enumeration, is
  a copy of the family's expander
- `ConstraintGraph.order_reduceGraph`, `deg_reduceGraph` — size `2 · numEdges`,
  degree `1 + E.degree`
- `ConstraintGraph.satisfiable_reduce_of_satisfiable` — completeness
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α : Type} (G : ConstraintGraph α)

/-! ### Half-edges and clouds -/

/-- A half-edge: an edge together with one of its two endpoints (`false` is the
tail, `true` the head). These are the vertices of the reduced graph. -/
abbrev HalfEdge (G : ConstraintGraph α) : Type := Fin G.numEdges × Bool

/-- The vertex a half-edge is attached to. -/
def owner (p : G.HalfEdge) : Fin G.numVerts := if p.2 then G.head p.1 else G.tail p.1

/-- The other half of the same edge. -/
def flipHalf (p : G.HalfEdge) : G.HalfEdge := (p.1, !p.2)

theorem flipHalf_involutive : Function.Involutive G.flipHalf := by
  intro p
  simp [flipHalf]

/-- The half-edges attached to `v`. -/
def cloud (v : Fin G.numVerts) : Finset G.HalfEdge :=
  Finset.univ.filter fun p => G.owner p = v

@[simp] theorem mem_cloud {v : Fin G.numVerts} {p : G.HalfEdge} :
    p ∈ G.cloud v ↔ G.owner p = v := by
  simp [cloud]

/-- The number naming a half-edge. The head of an edge is numbered before its
tail, which is the order `Fintype` enumerates `Bool` in. -/
def halfCode (p : G.HalfEdge) : ℕ := 2 * p.1.val + (if p.2 then 0 else 1)

theorem halfCode_injective : Function.Injective G.halfCode := by
  rintro ⟨e, b⟩ ⟨e', b'⟩ h
  simp only [halfCode] at h
  have he : e.val = e'.val := by cases b <;> cases b' <;> simp at h <;> omega
  have hb : b = b' := by cases b <;> cases b' <;> simp at h ⊢ <;> omega
  rw [Fin.ext he, hb]

instance halfLE_trans :
    IsTrans G.HalfEdge (fun p q => G.halfCode p ≤ G.halfCode q) := ⟨fun _ _ _ => le_trans⟩

instance halfLE_antisymm :
    Std.Antisymm (fun p q : G.HalfEdge => G.halfCode p ≤ G.halfCode q) :=
  ⟨fun _ _ h1 h2 => G.halfCode_injective (le_antisymm h1 h2)⟩

instance halfLE_total :
    Std.Total (fun p q : G.HalfEdge => G.halfCode p ≤ G.halfCode q) :=
  ⟨fun _ _ => le_total _ _⟩

/-- The half-edges of a cloud, listed without repetition, in order of their
numbers — the order an algorithm can find them in. -/
noncomputable def cloudList (v : Fin G.numVerts) : List G.HalfEdge :=
  (G.cloud v).sort (fun p q => G.halfCode p ≤ G.halfCode q)

theorem nodup_cloudList (v : Fin G.numVerts) : (G.cloudList v).Nodup :=
  Finset.sort_nodup _ _

theorem pairwise_cloudList (v : Fin G.numVerts) :
    List.Pairwise (fun p q => G.halfCode p ≤ G.halfCode q) (G.cloudList v) :=
  Finset.pairwise_sort _ _

@[simp] theorem mem_cloudList {v : Fin G.numVerts} {p : G.HalfEdge} :
    p ∈ G.cloudList v ↔ p ∈ G.cloud v := Finset.mem_sort _

theorem mem_cloudList_self (p : G.HalfEdge) : p ∈ G.cloudList (G.owner p) := by simp

/-! ### The cloud rotation -/

variable (E : ExpanderFamily)

/-- The cloud-link rotation, with the cloud's enumeration passed in explicitly
so that no dependent rewriting is ever needed. -/
noncomputable def cloudRotAux (l : List G.HalfEdge) (p : G.HalfEdge) (j : Fin E.degree) :
    G.HalfEdge × Fin E.degree :=
  if h : l.idxOf p < l.length then
    let q := E.rot l.length (⟨l.idxOf p, h⟩, j)
    (l.getD q.1.val p, q.2)
  else (p, j)

/-- Inside one cloud, the rotation is an involution: this is the family's own
involutivity, transported through the enumeration. -/
theorem cloudRotAux_involutive {l : List G.HalfEdge} (hnd : l.Nodup) {p : G.HalfEdge}
    (hp : p ∈ l) (j : Fin E.degree) :
    G.cloudRotAux E l (G.cloudRotAux E l p j).1 (G.cloudRotAux E l p j).2 = (p, j) := by
  have hlt : l.idxOf p < l.length := List.idxOf_lt_length_iff.mpr hp
  set q := E.rot l.length (⟨l.idxOf p, hlt⟩, j) with hq
  have hq1 : q.1.val < l.length := q.1.isLt
  have hstep : G.cloudRotAux E l p j = (l.getD q.1.val p, q.2) := by
    rw [cloudRotAux, dite_eq_left hlt]
  have hget : l.getD q.1.val p = l[q.1.val] := (List.getElem_eq_getD p).symm
  have hidx' : l.idxOf l[q.1.val] = q.1.val := hnd.idxOf_getElem _ hq1
  have hlt' : l.idxOf (l.getD q.1.val p) < l.length := by
    rw [hget, hidx']; exact hq1
  rw [hstep, cloudRotAux, dite_eq_left hlt']
  have hval : l.idxOf (l.getD q.1.val p) = q.1.val := by rw [hget, hidx']
  have hfin : (⟨l.idxOf (l.getD q.1.val p), hlt'⟩ : Fin l.length) = q.1 := Fin.ext hval
  rw [hfin]
  have hinv : E.rot l.length (q.1, q.2) = (⟨l.idxOf p, hlt⟩, j) := by
    rw [hq, Prod.mk.eta, E.rot_involutive l.length]
  rw [hinv]
  have hself : ∀ d : G.HalfEdge, l.getD (l.idxOf p) d = p := by
    intro d
    rw [← List.getElem_eq_getD (h := hlt), List.getElem_idxOf hlt]
  exact Prod.ext (hself _) rfl

/-- The cloud-link rotation at a half-edge, using its own cloud. -/
noncomputable def cloudRot (p : G.HalfEdge) (j : Fin E.degree) : G.HalfEdge × Fin E.degree :=
  G.cloudRotAux E (G.cloudList (G.owner p)) p j

/-- A cloud-link lands inside the enumeration it started from. -/
theorem cloudRotAux_mem {l : List G.HalfEdge} {p : G.HalfEdge} (hp : p ∈ l)
    (j : Fin E.degree) : (G.cloudRotAux E l p j).1 ∈ l := by
  have hlt : l.idxOf p < l.length := List.idxOf_lt_length_iff.mpr hp
  have hq1 : (E.rot l.length (⟨l.idxOf p, hlt⟩, j)).1.val < l.length :=
    (E.rot l.length (⟨l.idxOf p, hlt⟩, j)).1.isLt
  rw [cloudRotAux, dite_eq_left hlt]
  dsimp only
  rw [← List.getElem_eq_getD (h := hq1)]
  exact List.getElem_mem hq1

/-- A cloud-link stays inside the cloud. -/
theorem owner_cloudRot (p : G.HalfEdge) (j : Fin E.degree) :
    G.owner (G.cloudRot E p j).1 = G.owner p := by
  have h := G.cloudRotAux_mem E (G.mem_cloudList_self p) j
  rw [cloudRot]
  simpa using h

/-- **The cloud is a copy of the expander.** Reading the cloud through its
enumeration, a cloud-link is exactly the family's rotation map. This is what
lets the expander estimates of `Disagreement` be applied to a cloud. -/
theorem cloudRot_getElem (v : Fin G.numVerts) (i : Fin (G.cloudList v).length)
    (j : Fin E.degree) :
    (G.cloudRot E ((G.cloudList v)[i.val]) j).1
      = (G.cloudList v)[(E.rot (G.cloudList v).length (i, j)).1.val] := by
  have hmem : (G.cloudList v)[i.val] ∈ G.cloudList v := List.getElem_mem i.isLt
  have howner : G.owner ((G.cloudList v)[i.val]) = v :=
    (G.mem_cloud).mp ((G.mem_cloudList).mp hmem)
  have hidx : (G.cloudList v).idxOf ((G.cloudList v)[i.val]) = i.val :=
    (G.nodup_cloudList v).idxOf_getElem _ i.isLt
  have hlt : (G.cloudList v).idxOf ((G.cloudList v)[i.val]) < (G.cloudList v).length := by
    rw [hidx]; exact i.isLt
  rw [cloudRot, howner, cloudRotAux, dite_eq_left hlt]
  have hfin : (⟨(G.cloudList v).idxOf ((G.cloudList v)[i.val]), hlt⟩ :
      Fin (G.cloudList v).length) = i := Fin.ext hidx
  rw [hfin]
  dsimp only
  exact (List.getElem_eq_getD _).symm

theorem cloudRot_involutive (p : G.HalfEdge) (j : Fin E.degree) :
    G.cloudRot E (G.cloudRot E p j).1 (G.cloudRot E p j).2 = (p, j) := by
  have howner : G.owner (G.cloudRot E p j).1 = G.owner p := G.owner_cloudRot E p j
  rw [cloudRot, howner]
  exact G.cloudRotAux_involutive E (G.nodup_cloudList _) (G.mem_cloudList_self p) j

/-! ### The reduced graph -/

/-- The reduced graph: every half-edge has one edge-link to the other half of
its edge, and `E.degree` cloud-links to the half-edges sharing its endpoint. -/
noncomputable def reduceGraph (G : ConstraintGraph α) (E : ExpanderFamily) : RegGraph where
  V := G.HalfEdge
  D := Option (Fin E.degree)
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := ⟨none⟩
  rot x :=
    match x.2 with
    | none => (G.flipHalf x.1, none)
    | some j => ((G.cloudRot E x.1 j).1, some (G.cloudRot E x.1 j).2)
  rot_involutive := by
    rintro ⟨p, _ | j⟩
    · show (G.flipHalf (G.flipHalf p), (none : Option (Fin E.degree))) = (p, none)
      rw [G.flipHalf_involutive p]
    · show ((G.cloudRot E (G.cloudRot E p j).1 (G.cloudRot E p j).2).1,
        some (G.cloudRot E (G.cloudRot E p j).1 (G.cloudRot E p j).2).2) = (p, some j)
      rw [G.cloudRot_involutive E p j]

@[simp] theorem V_reduceGraph : (G.reduceGraph E).V = G.HalfEdge := rfl

@[simp] theorem order_reduceGraph : (G.reduceGraph E).order = 2 * G.numEdges := by
  show Fintype.card (Fin G.numEdges × Bool) = 2 * G.numEdges
  simp [Nat.mul_comm]

/-- The reduced graph is `(1 + E.degree)`-regular. -/
@[simp] theorem deg_reduceGraph : (G.reduceGraph E).deg = 1 + E.degree := by
  show Fintype.card (Option (Fin E.degree)) = 1 + E.degree
  simp [Nat.add_comm]

theorem nbr_reduceGraph_none (p : G.HalfEdge) :
    (G.reduceGraph E).nbr p none = G.flipHalf p := rfl

theorem nbr_reduceGraph_some (p : G.HalfEdge) (j : Fin E.degree) :
    (G.reduceGraph E).nbr p (some j) = (G.cloudRot E p j).1 := rfl

/-! ### The reduced constraint system -/

variable [DecidableEq α]

/-- The reduced constraint system: an edge-link carries the original constraint
of its edge, oriented so that the tail's label comes first, and a cloud-link
demands that the two half-edges agree. -/
noncomputable def reduce (G : ConstraintGraph α) (E : ExpanderFamily) : RegCSP α where
  graph := G.reduceGraph E
  rel p d a b :=
    match d with
    | none => if p.2 then G.rel p.1 b a else G.rel p.1 a b
    | some _ => a == b

@[simp] theorem graph_reduce : (G.reduce E).graph = G.reduceGraph E := rfl

/-- The reduced system's vertices are the half-edges, numbered by their edge and
their side. -/
noncomputable instance : NumEnc (G.reduce E).graph.V :=
  inferInstanceAs (NumEnc (Fin G.numEdges × Bool))

/-- Completeness: labelling every half-edge by its endpoint's label carries a
satisfying assignment of `G` to one of the reduced system. -/
theorem satisfiable_reduce_of_satisfiable (h : G.Satisfiable) : (G.reduce E).Satisfiable := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun p => σ (G.owner p), ?_⟩
  rintro ⟨p, _ | j⟩
  · -- an edge-link carries the original constraint
    rw [RegCSP.Satisfies, RegCSP.satisfies]
    dsimp only
    show (if p.2 then G.rel p.1 (σ (G.owner ((G.reduceGraph E).nbr p none))) (σ (G.owner p))
      else G.rel p.1 (σ (G.owner p)) (σ (G.owner ((G.reduceGraph E).nbr p none)))) = true
    rw [nbr_reduceGraph_none G E p]
    have hedge := hσ p.1
    rw [Satisfies, satisfies] at hedge
    by_cases hb : p.2 = true
    · have h1 : G.owner p = G.head p.1 := by simp [owner, hb]
      have h2 : G.owner (G.flipHalf p) = G.tail p.1 := by simp [owner, flipHalf, hb]
      rw [ite_eq_left hb, h1, h2]
      exact hedge
    · have hb' : p.2 = false := by simpa using hb
      have h1 : G.owner p = G.tail p.1 := by simp [owner, hb']
      have h2 : G.owner (G.flipHalf p) = G.head p.1 := by simp [owner, flipHalf, hb']
      rw [ite_eq_right hb, h1, h2]
      exact hedge
  · -- a cloud-link joins half-edges with the same endpoint
    rw [RegCSP.Satisfies, RegCSP.satisfies]
    dsimp only
    show ((σ (G.owner p) == σ (G.owner ((G.reduceGraph E).nbr p (some j)))) = true)
    rw [nbr_reduceGraph_some G E p j, G.owner_cloudRot E p j]
    simp

end ConstraintGraph

end Complexity

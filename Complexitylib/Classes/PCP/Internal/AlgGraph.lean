/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.UnaryList
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph
public import Complexitylib.Classes.PCP.Internal.Materialize

/-!
# A constraint graph as a string

An algorithm that runs Dinur's amplification has to hold a constraint graph in
its hand. Over a fixed finite alphabet a graph is a small amount of data: how
many vertices, and for each edge its two endpoints and its constraint. The
endpoints are numbers below the vertex count, and the constraint — a predicate
on two symbols — is itself one of finitely many, so it too is a number.

That is the encoding used here: the vertex count in unary, followed by a list of
records, each three unary numbers. Numbering the constraints rather than
tabulating them keeps every record a triple of numbers, so the whole toolkit of
`UnaryList` applies; and because the number of constraints is a constant,
reading one back is a lookup on a bounded key.

## Main definitions

- `Complexity.relOfCode`, `Complexity.codeOfRel` — numbering the constraints
- `Complexity.encGraph` — the graph as a string
- `Complexity.gVerts`, `gEdges`, `gTail`, `gHead`, `gCode` — reading it back

## Main results

- `Complexity.gVerts_encGraph`, `gEdges_encGraph`, `gTail_encGraph`,
  `gHead_encGraph`, `gRel_encGraph` — the reading inverts the writing
- `Complexity.buildGraph_eq`, `Complexity.buildGraph_mem_FP` — a rule for each
  edge writes the graph, in polynomial time
-/

@[expose] public section

namespace Complexity

/-! ### Numbering the constraints -/

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The constraint a code stands for; the always-false constraint for a code
that is out of range. -/
noncomputable def relOfCode (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) : α → α → Bool :=
  if h : r < Fintype.card (α → α → Bool) then (Fintype.equivFin (α → α → Bool)).symm ⟨r, h⟩
  else fun _ _ => false

/-- The code of a constraint. -/
noncomputable def codeOfRel (f : α → α → Bool) : ℕ := (Fintype.equivFin (α → α → Bool) f).val

theorem codeOfRel_lt (f : α → α → Bool) :
    codeOfRel f < Fintype.card (α → α → Bool) := Fin.isLt _

@[simp] theorem relOfCode_codeOfRel (f : α → α → Bool) : relOfCode α (codeOfRel f) = f := by
  rw [relOfCode, dite_eq_left (codeOfRel_lt f)]
  simp only [codeOfRel, Fin.eta, Equiv.symm_apply_apply]

/-! ### The encoding -/

/-- One record for each edge: its two endpoints and the code of its
constraint. -/
noncomputable def edgeRecs (G : ConstraintGraph α) : List (List Bool × List Bool × List Bool) :=
  (List.finRange G.numEdges).map fun e =>
    (List.replicate (G.tail e).val true,
      List.replicate (G.head e).val true, List.replicate (codeOfRel (G.rel e)) true)

@[simp] theorem length_edgeRecs (G : ConstraintGraph α) :
    (edgeRecs G).length = G.numEdges := by
  rw [edgeRecs, List.length_map, List.length_finRange]

/-- **A constraint graph, as a string.** -/
noncomputable def encGraph (G : ConstraintGraph α) : List Bool :=
  pair (List.replicate G.numVerts true) (DataEncode.bitstringEncode (edgeRecs G))

/-! ### Reading it back -/

/-- How many vertices an encoded graph has. -/
def gVerts (z : List Bool) : ℕ := (pairFst z).length

/-- How many edges. -/
noncomputable def gEdges (z : List Bool) : ℕ := (posCount (pairSnd z)).length

/-- The first endpoint of an edge. -/
noncomputable def gTail (z : List Bool) (e : ℕ) : ℕ := (recFst (pairSnd z) e).length

/-- The second endpoint. -/
noncomputable def gHead (z : List Bool) (e : ℕ) : ℕ := (recSnd (pairSnd z) e).length

/-- The code of the constraint. -/
noncomputable def gCode (z : List Bool) (e : ℕ) : ℕ := (recThd (pairSnd z) e).length

variable (G : ConstraintGraph α)

@[simp] theorem gVerts_encGraph : gVerts (encGraph G) = G.numVerts := by
  rw [gVerts, encGraph, pairFst_pair, List.length_replicate]

@[simp] theorem gEdges_encGraph : gEdges (encGraph G) = G.numEdges := by
  rw [gEdges, encGraph, pairSnd_pair, posCount_eq, List.length_replicate,
    length_edgeRecs]

theorem getElem_edgeRecs (e : ℕ) (he : e < G.numEdges) :
    (edgeRecs G)[e]'(by rw [length_edgeRecs]; exact he)
      = (List.replicate (G.tail ⟨e, he⟩).val true,
        List.replicate (G.head ⟨e, he⟩).val true,
        List.replicate (codeOfRel (G.rel ⟨e, he⟩)) true) := by
  simp only [edgeRecs, List.getElem_map, List.getElem_finRange]
  rfl

@[simp] theorem gTail_encGraph (e : ℕ) (he : e < G.numEdges) :
    gTail (encGraph G) e = (G.tail ⟨e, he⟩).val := by
  rw [gTail, encGraph, pairSnd_pair,
    recFst_eq (l3 := edgeRecs G) (by rw [length_edgeRecs]; exact he) (getElem_edgeRecs G e he),
    List.length_replicate]

@[simp] theorem gHead_encGraph (e : ℕ) (he : e < G.numEdges) :
    gHead (encGraph G) e = (G.head ⟨e, he⟩).val := by
  rw [gHead, encGraph, pairSnd_pair,
    recSnd_eq (l3 := edgeRecs G) (by rw [length_edgeRecs]; exact he) (getElem_edgeRecs G e he),
    List.length_replicate]

theorem gCode_encGraph (e : ℕ) (he : e < G.numEdges) :
    gCode (encGraph G) e = codeOfRel (G.rel ⟨e, he⟩) := by
  rw [gCode, encGraph, pairSnd_pair,
    recThd_eq (l3 := edgeRecs G) (by rw [length_edgeRecs]; exact he) (getElem_edgeRecs G e he),
    List.length_replicate]

/-- **The constraint of an edge survives the round trip.** -/
theorem gRel_encGraph (e : ℕ) (he : e < G.numEdges) :
    relOfCode α (gCode (encGraph G) e) = G.rel ⟨e, he⟩ := by
  rw [gCode_encGraph G e he, relOfCode_codeOfRel]

/-- **How long a graph's encoding is**, in terms of its two counts. -/
theorem length_encGraph_le (G : ConstraintGraph α) :
    (encGraph G).length
      ≤ 2 * G.numVerts + 4
        + G.numEdges * (8 * G.numVerts + 4 * Fintype.card (α → α → Bool) + 10) := by
  have hsum : ((edgeRecs G).map fun a => (DataEncode.bitstringEncode a).length).sum
      ≤ G.numEdges * (8 * G.numVerts + 4 * Fintype.card (α → α → Bool) + 10) := by
    refine le_trans (List.sum_le_length_nsmul _
      (8 * G.numVerts + 4 * Fintype.card (α → α → Bool) + 10) ?_) ?_
    · intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      rw [length_edgeRecs] at hi
      rw [getElem_edgeRecs G i hi, ← encTriple_eq, length_encTriple]
      have h3 := codeOfRel_lt (G.rel ⟨i, hi⟩)
      omega
    · rw [List.length_map, length_edgeRecs, smul_eq_mul]
  rw [encGraph, pair_length, List.length_replicate, length_bitstringEncode_list]
  omega

/-! ### Writing one out -/

/-- A graph assembled from a vertex count, an edge count and a rule for each
edge record. -/
noncomputable def buildGraph (nv cnt E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (nv z) (listEncFn E (pair (cnt z) z))

theorem buildGraph_mem_FP {nv cnt E : List Bool → List Bool} (hnv : nv ∈ FP)
    (hcnt : cnt ∈ FP) (hE : E ∈ FP) : buildGraph nv cnt E ∈ FP := by
  have harg := Cobham.pairFn_mem_FP hcnt id_mem_FP
  have hlist := mem_FP_comp harg (materialize_mem_FP hE)
  exact mem_FP_of_eq (Cobham.pairFn_mem_FP hnv hlist) fun _ => rfl

/-- **The rule writes the graph.** -/
theorem buildGraph_eq {nv cnt E : List Bool → List Bool} {z : List Bool}
    {G : ConstraintGraph α} (hnv : nv z = List.replicate G.numVerts true)
    (hcnt : cnt z = List.replicate G.numEdges true)
    (hE : ∀ (e : ℕ) (he : e < G.numEdges),
      E (pair z (List.replicate e true))
        = encTriple (List.replicate (G.tail ⟨e, he⟩).val true)
            (List.replicate (G.head ⟨e, he⟩).val true)
            (List.replicate (codeOfRel (G.rel ⟨e, he⟩)) true)) :
    buildGraph nv cnt E z = encGraph G := by
  rw [buildGraph, encGraph, hnv, hcnt, ← length_edgeRecs G]
  refine congrArg _ (materialize_eq (edgeRecs G) z fun i hi => ?_)
  rw [length_edgeRecs] at hi
  rw [hE i hi, encTriple_eq, getElem_edgeRecs G i hi]

/-! ### Reading one, in polynomial time -/

theorem gVertsFn_mem_FP {g : List Bool → List Bool} (hg : g ∈ FP) :
    (fun z => marks (pairFst (g z))) ∈ FP :=
  marks_mem_FP (mem_FP_comp hg Cobham.fstBlock_mem_FP)

theorem gEdgesFn_mem_FP {g : List Bool → List Bool} (hg : g ∈ FP) :
    (fun z => posCount (pairSnd (g z))) ∈ FP :=
  posCount_mem_FP (mem_FP_comp hg Cobham.sndBlock_mem_FP)

theorem gTailFn_mem_FP {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => recFst (pairSnd (g z)) (f z).length) ∈ FP :=
  recFst_mem_FP hf (mem_FP_comp hg Cobham.sndBlock_mem_FP)

theorem gHeadFn_mem_FP {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => recSnd (pairSnd (g z)) (f z).length) ∈ FP :=
  recSnd_mem_FP hf (mem_FP_comp hg Cobham.sndBlock_mem_FP)

theorem gCodeFn_mem_FP {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => recThd (pairSnd (g z)) (f z).length) ∈ FP :=
  recThd_mem_FP hf (mem_FP_comp hg Cobham.sndBlock_mem_FP)

theorem length_marks_fstBlock (z : List Bool) :
    (marks (pairFst z)).length = gVerts z := by
  rw [marks_eq, List.length_replicate, gVerts]

theorem length_posCount_sndBlock (z : List Bool) :
    (posCount (pairSnd z)).length = gEdges z := rfl

theorem length_recFst_sndBlock (z : List Bool) (e : ℕ) :
    (recFst (pairSnd z) e).length = gTail z e := rfl

theorem length_recSnd_sndBlock (z : List Bool) (e : ℕ) :
    (recSnd (pairSnd z) e).length = gHead z e := rfl

theorem length_recThd_sndBlock (z : List Bool) (e : ℕ) :
    (recThd (pairSnd z) e).length = gCode z e := rfl

end Complexity

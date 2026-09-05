/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Preprocess
public import Complexitylib.Classes.PCP.Internal.CloudCount

/-!
# The preprocessed graph, in numbers

Preprocessing superposes three edge sets on the half-edges of a graph: the
edge-links pairing the two halves of an edge, the cloud-links joining the halves
that share an endpoint, and the expander's own edges, with a self-loop added at
every vertex. This module reads off what each of those does to a *number*.

The numbering is the one `NumEnc` gives: a half-edge is `2 e` or `2 e + 1`
according to which end it is — the same number `DegreeReduction` sorts clouds by
— and a dart is `0` for the self-loop, `1` for the edge-link, `2 + j` for the
`j`-th cloud-link and `2 + degree + j` for the `j`-th expander edge.

## Main results

- `Complexity.ConstraintGraph.enc_halfEdge` — a half-edge's number is its code
- `Complexity.ConstraintGraph.enc_preLoop`, `enc_preEdge`, `enc_preCloud`,
  `enc_preExp` — the four kinds of dart, and `preDart_cases`: there are no
  others
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

open NumEnc

variable {α : Type} [DecidableEq α] (G : ConstraintGraph α) (E : ExpanderFamily)

omit [DecidableEq α] in
/-- **A half-edge's number is the code the clouds are sorted by.** -/
theorem enc_halfEdge (p : G.HalfEdge) : enc p = G.halfCode p := by
  show enc p.1 * 2 + enc p.2 = 2 * p.1.val + (if p.2 then 0 else 1)
  show p.1.val * 2 + (if p.2 then 0 else 1) = _
  omega

/-- The self-loop at a vertex. -/
def preLoop : (G.preprocess E).graph.D := Sum.inl ()

/-- The link to the other half of the same edge. -/
def preEdge : (G.preprocess E).graph.D := Sum.inr (Sum.inl none)

/-- The `j`-th link inside the cloud. -/
def preCloud (j : Fin E.degree) : (G.preprocess E).graph.D := Sum.inr (Sum.inl (some j))

/-- The `j`-th edge of the superposed expander. -/
def preExp (j : Fin E.degree) : (G.preprocess E).graph.D := Sum.inr (Sum.inr j)

/-- The darts of the preprocessed graph: a self-loop, an edge-link, the
cloud-links, and the expander's edges. -/
theorem enc_preLoop : enc (G.preLoop E) = 0 := rfl

theorem enc_preEdge : enc (G.preEdge E) = 1 := by
  show 1 + 0 = 1
  omega

theorem enc_preCloud (j : Fin E.degree) : enc (G.preCloud E j) = 2 + j.val := by
  show 1 + (1 + j.val) = 2 + j.val
  omega

theorem enc_preExp (j : Fin E.degree) : enc (G.preExp E j) = 2 + E.degree + j.val := by
  show 1 + ((E.degree + 1) + j.val) = 2 + E.degree + j.val
  omega

/-- Every dart is one of the four kinds. -/
theorem preDart_cases (d : (G.preprocess E).graph.D) :
    d = G.preLoop E ∨ d = G.preEdge E ∨ (∃ j, d = G.preCloud E j) ∨ ∃ j, d = G.preExp E j := by
  match d with
  | Sum.inl () => exact Or.inl rfl
  | Sum.inr (Sum.inl none) => exact Or.inr (Or.inl rfl)
  | Sum.inr (Sum.inl (some j)) => exact Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))
  | Sum.inr (Sum.inr j) => exact Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))

/-! ### What each kind of dart does -/

theorem rot_preLoop (v : (G.preprocess E).graph.V) :
    (G.preprocess E).graph.rot (v, G.preLoop E) = (v, G.preLoop E) := rfl

theorem rot_preEdge (v : G.HalfEdge) :
    (G.preprocess E).graph.rot (v, G.preEdge E) = (G.flipHalf v, G.preEdge E) := rfl

theorem rot_preCloud (v : G.HalfEdge) (j : Fin E.degree) :
    (G.preprocess E).graph.rot (v, G.preCloud E j)
      = ((G.cloudRot E v j).1, G.preCloud E (G.cloudRot E v j).2) := rfl

theorem rot_preExp (v : G.HalfEdge) (j : Fin E.degree) :
    (G.preprocess E).graph.rot (v, G.preExp E j)
      = (E.vertexEquiv (G.reduce E).graph
            (E.rot (G.reduce E).graph.order
              ((E.vertexEquiv (G.reduce E).graph).symm v, j)).1,
          G.preExp E (E.rot (G.reduce E).graph.order
            ((E.vertexEquiv (G.reduce E).graph).symm v, j)).2) := rfl

/-! ### The three moves, in numbers -/

omit [DecidableEq α] in
/-- **Crossing an edge flips the last bit of the number.** -/
theorem enc_flipHalf (p : G.HalfEdge) :
    enc (G.flipHalf p) = if enc p % 2 = 0 then enc p + 1 else enc p - 1 := by
  rw [enc_halfEdge, enc_halfEdge, halfCode, halfCode, flipHalf]
  cases p.2 <;> simp

/-- **The expander's vertices are numbered as the graph's are.** -/
theorem enc_vertexEquiv (x : Fin (G.reduce E).graph.order) :
    enc (E.vertexEquiv (G.reduce E).graph x) = x.val := by
  show enc ((NumEnc.equivFinCard (G.reduce E).graph.V).symm x) = _
  have h : NumEnc.enc ((NumEnc.equivFinCard (G.reduce E).graph.V).symm x)
      = (NumEnc.equivFinCard (G.reduce E).graph.V
          ((NumEnc.equivFinCard (G.reduce E).graph.V).symm x)).val := rfl
  erw [h, Equiv.apply_symm_apply]

theorem val_vertexEquiv_symm (v : (G.reduce E).graph.V) :
    ((E.vertexEquiv (G.reduce E).graph).symm v).val = enc v := rfl

/-! ### The cloud step, in numbers -/

/-- The cloud step on numbers: count how many of the cloud's half-edges come
before this one, let the expander family move that index, and read off the code
the new index names. -/
noncomputable def cloudStepNum (v : Fin G.numVerts) (c : ℕ) (j : Fin E.degree) : ℕ × ℕ :=
  if h : countBelow (G.cloudCodes v) c < (G.cloudList v).length then
    let q := E.rot (G.cloudList v).length (⟨countBelow (G.cloudCodes v) c, h⟩, j)
    ((G.cloudCodes v).orderEmbOfFin (G.card_cloudCodes_eq_length v) q.1, q.2.val)
  else (c, j.val)

omit [DecidableEq α] in
/-- **The numbers run the cloud step.** -/
theorem cloudStepNum_eq (p : G.HalfEdge) (j : Fin E.degree) :
    G.cloudStepNum E (G.owner p) (enc p) j
      = (enc (G.cloudRot E p j).1, (G.cloudRot E p j).2.val) := by
  have hmem : p ∈ G.cloudList (G.owner p) := G.mem_cloudList_self p
  have hlt : (G.cloudList (G.owner p)).idxOf p < (G.cloudList (G.owner p)).length :=
    List.idxOf_lt_length_iff.mpr hmem
  have hidx : (G.cloudList (G.owner p)).idxOf p
      = countBelow (G.cloudCodes (G.owner p)) (enc p) := by
    rw [G.idxOf_cloudList rfl, enc_halfEdge]
  have hlt' : countBelow (G.cloudCodes (G.owner p)) (enc p)
      < (G.cloudList (G.owner p)).length := by rw [← hidx]; exact hlt
  rw [cloudStepNum, dite_eq_left hlt', cloudRot, cloudRotAux, dite_eq_left hlt]
  simp only [← hidx]
  refine Prod.ext ?_ rfl
  dsimp only
  conv_rhs => rw [enc_halfEdge]
  have hq : (E.rot (G.cloudList (G.owner p)).length
      (⟨(G.cloudList (G.owner p)).idxOf p, hlt⟩, j)).1.val
      < (G.cloudList (G.owner p)).length := Fin.isLt _
  rw [← List.getElem_eq_getD (h := hq)]
  exact G.halfCode_getElem_cloudList _ _ hq

/-! ### The whole rotation map, in numbers -/

/-- The vertex a half-edge number is attached to. -/
noncomputable def ownerNum (v : ℕ) : ℕ :=
  if h : v / 2 < G.numEdges then
    (if v % 2 = 0 then (G.head ⟨v / 2, h⟩).val else (G.tail ⟨v / 2, h⟩).val)
  else 0

omit [DecidableEq α] in
theorem ownerNum_enc (p : G.HalfEdge) : G.ownerNum (enc p) = (G.owner p).val := by
  have hcode : enc p = 2 * p.1.val + (if p.2 then 0 else 1) := by
    rw [enc_halfEdge, halfCode]
  have hdiv : enc p / 2 = p.1.val := by
    rw [hcode]
    cases p.2
    · simp
      omega
    · simp
  have hmod : enc p % 2 = (if p.2 then 0 else 1) := by
    rw [hcode]
    cases p.2 <;> simp
  have hlt : enc p / 2 < G.numEdges := by rw [hdiv]; exact p.1.isLt
  have hfin : (⟨enc p / 2, hlt⟩ : Fin G.numEdges) = p.1 := Fin.ext hdiv
  rw [ownerNum, dite_eq_left hlt, hmod, owner, hfin]
  cases p.2 <;> simp

/-- The cloud step, on numbers throughout. -/
noncomputable def cloudStepN (u c j : ℕ) : ℕ × ℕ :=
  if hu : u < G.numVerts then
    if hj : j < E.degree then G.cloudStepNum E ⟨u, hu⟩ c ⟨j, hj⟩ else (c, j)
  else (c, j)

/-- The expander step, on numbers. -/
noncomputable def expStepN (v j : ℕ) : ℕ × ℕ :=
  if hv : v < (G.reduce E).graph.order then
    if hj : j < E.degree then
      ((E.rot (G.reduce E).graph.order (⟨v, hv⟩, ⟨j, hj⟩)).1.val,
        (E.rot (G.reduce E).graph.order (⟨v, hv⟩, ⟨j, hj⟩)).2.val)
    else (v, j)
  else (v, j)

/-- **The preprocessed graph's rotation map, on numbers.** Dart `0` is the
self-loop, dart `1` crosses the edge, darts `2` to `deg + 1` rotate inside the
cloud, and the rest are the superposed expander's. -/
noncomputable def preRotNum (v d : ℕ) : ℕ × ℕ :=
  if d = 0 then (v, 0)
  else if d = 1 then ((if v % 2 = 0 then v + 1 else v - 1), 1)
  else if d < 2 + E.degree then
    ((G.cloudStepN E (G.ownerNum v) v (d - 2)).1,
      (G.cloudStepN E (G.ownerNum v) v (d - 2)).2 + 2)
  else
    ((G.expStepN E v (d - (2 + E.degree))).1,
      (G.expStepN E v (d - (2 + E.degree))).2 + 2 + E.degree)

/-- **The numbers run the preprocessed graph's rotation map.** -/
theorem preRotNum_eq (v : G.HalfEdge) (d : (G.preprocess E).graph.D) :
    G.preRotNum E (enc v) (enc d)
      = (enc (((G.preprocess E).graph.rot (v, d)).1 : G.HalfEdge),
        enc ((G.preprocess E).graph.rot (v, d)).2) := by
  rcases G.preDart_cases E d with rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · erw [G.enc_preLoop E, preRotNum, ite_eq_left rfl, G.rot_preLoop E]
    rfl
  · erw [G.enc_preEdge E, preRotNum, ite_eq_right one_ne_zero, ite_eq_left rfl, G.rot_preEdge E]
    dsimp only
    exact Prod.ext (G.enc_flipHalf v).symm rfl
  · have hj := j.isLt
    erw [G.enc_preCloud E j, preRotNum, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega), G.rot_preCloud E, G.enc_preCloud E]
    dsimp only
    rw [G.ownerNum_enc]
    have harg : (2 + j.val) - 2 = j.val := by omega
    rw [harg, cloudStepN, dite_eq_left (G.owner v).isLt, dite_eq_left hj]
    have hv : (⟨(G.owner v).val, (G.owner v).isLt⟩ : Fin G.numVerts) = G.owner v := rfl
    have hjj : (⟨j.val, hj⟩ : Fin E.degree) = j := rfl
    rw [hv, hjj, G.cloudStepNum_eq E v j]
    exact Prod.ext rfl (by omega)
  · have hj := j.isLt
    have hvlt : enc v < (G.reduce E).graph.order := by
      have := NumEnc.enc_lt v
      rwa [NumEnc.card_eq_fintype_card] at this
    erw [G.enc_preExp E j, preRotNum, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), G.rot_preExp E, G.enc_preExp E]
    dsimp only
    have harg : 2 + E.degree + j.val - (2 + E.degree) = j.val := by omega
    rw [harg, expStepN, dite_eq_left hvlt, dite_eq_left hj]
    have hv : (⟨enc v, hvlt⟩ : Fin (G.reduce E).graph.order)
        = (E.vertexEquiv (G.reduce E).graph).symm v :=
      Fin.ext (G.val_vertexEquiv_symm E v).symm
    have hjj : (⟨j.val, hj⟩ : Fin E.degree) = j := rfl
    rw [hv, hjj]
    exact Prod.ext (G.enc_vertexEquiv E _).symm (by omega)

end ConstraintGraph

end Complexity

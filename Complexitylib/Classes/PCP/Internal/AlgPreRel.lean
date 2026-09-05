/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgGraph
public import Complexitylib.Classes.PCP.Internal.AlgPreprocess
public import Complexitylib.Classes.PCP.Internal.KilledCSP

/-!
# The preprocessed constraint, in numbers

Preprocessing leaves three kinds of constraint: the original one at an
edge-link, oriented by the half-edge's side; equality inside a cloud; and
nothing at all at a self-loop or an expander edge. So the constraint at a dart
is a fixed function of the dart's number, the half-edge's side, and the code of
the original constraint — a bounded amount of data.

## Main definitions

- `Complexity.preRelCode` — the constraint a dart's number and a code stand for

## Main results

- `Complexity.preRel_eq` — it is the preprocessed system's constraint
- `Complexity.rel_killedPow_preprocess` — the killed power's constraint runs
  those codes along the walk
- `Complexity.rel_killedPow_eq_relOfSteps` — so it depends on the graph only
  through the walk's parities and codes
- `Complexity.rel_killedPow_eq_preRelOfSteps` — the same, with every argument at
  a type that does not mention the graph
-/

@[expose] public section

namespace Complexity

open NumEnc

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The preprocessed system's constraint, from the dart's number `d`, the
half-edge's number `u` and the code `c` of the original constraint. -/
noncomputable def preRelCode (α : Type) [Fintype α] [DecidableEq α]
    (deg c u d : ℕ) (a b : α) : Bool :=
  if d = 0 then true
  else if d = 1 then
    (if u % 2 = 0 then relOfCode α c b a else relOfCode α c a b)
  else if d < 2 + deg then decide (a = b)
  else true

/-- **The numbers give the preprocessed constraint.** -/
theorem preRel_eq (G : ConstraintGraph α) (E : ExpanderFamily) (p : G.HalfEdge)
    (d : (G.preprocess E).graph.D) (a b : α) :
    (G.preprocess E).rel p d a b
      = preRelCode α E.degree (codeOfRel (G.rel p.1)) (enc p) (enc d) a b := by
  have hmod : enc p % 2 = (if p.2 then 0 else 1) := by
    rw [ConstraintGraph.enc_halfEdge, ConstraintGraph.halfCode]
    cases p.2 <;> simp
  rcases G.preDart_cases E d with rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [G.enc_preLoop E, preRelCode, ite_eq_left rfl]
    rfl
  · rw [G.enc_preEdge E, preRelCode, ite_eq_right one_ne_zero, ite_eq_left rfl, relOfCode_codeOfRel,
    hmod]
    show (if p.2 then G.rel p.1 b a else G.rel p.1 a b) = _
    cases hb : p.2 <;> simp
  · have hj := j.isLt
    rw [G.enc_preCloud E j, preRelCode, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
    rfl
  · have hj := j.isLt
    rw [G.enc_preExp E j, preRelCode, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    rfl

/-- Only the parity of a half-edge's number matters. -/
theorem preRelCode_mod (deg c u d : ℕ) (a b : α) :
    preRelCode α deg c (u % 2) d a b = preRelCode α deg c u d a b := by
  rw [preRelCode, preRelCode, Nat.mod_mod_of_dvd u (dvd_refl 2)]

/-- **The killed power's constraint, along the walk.** Each step contributes the
preprocessed constraint at the vertex it stands on, read off that vertex's
number and the code of the original constraint there. -/
theorem rel_killedPow_preprocess (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    (a b : KOpinion (G.preprocess E).graph T α) :
    ((G.preprocess E).killedPow q T hq).rel v x a b
      = decide (∀ i : Fin ((G.preprocess E).graph.kLen x),
          preRelCode α E.degree
              (codeOfRel (G.rel ((G.preprocess E).graph.walkAt
                ((G.preprocess E).graph.kLen x) v ((G.preprocess E).graph.kWalk x) i.val).1))
              (enc ((G.preprocess E).graph.walkAt
                ((G.preprocess E).graph.kLen x) v ((G.preprocess E).graph.kWalk x) i.val))
              (enc ((G.preprocess E).graph.kWalk x i))
              (a ((G.preprocess E).graph.startIdx ((G.preprocess E).graph.kLen_le x)
                ((G.preprocess E).graph.kWalk x) i))
              (b ((G.preprocess E).graph.endIdx ((G.preprocess E).graph.kLen_le x) v
                ((G.preprocess E).graph.kWalk x) i)) = true) := by
  show decide (∀ i : Fin ((G.preprocess E).graph.kLen x), _ = true) = _
  rw [decide_eq_decide]
  exact forall_congr' fun i => by erw [preRel_eq]; rfl

/-- What a killed dart's constraint runs: at each step, the dart it takes, the
parity of the vertex it stands on, the code of the constraint there, and where
the two ends hold their opinions about that step. -/
noncomputable def relOfSteps {Gr : RegGraph} [NumEnc Gr.D] {T : ℕ} (deg n : ℕ)
    (dart : Fin n → Gr.D) (par code : Fin n → ℕ)
    (sIdx eIdx : Fin n → VarWalk Gr T) (a b : KOpinion Gr T α) : Bool :=
  decide (∀ i : Fin n, preRelCode α deg (code i) (par i) (NumEnc.enc (dart i))
    (a (sIdx i)) (b (eIdx i)) = true)

/-- **The killed power's constraint depends on the graph only through the
walk's parities and codes** — a bounded amount of data. -/
theorem rel_killedPow_eq_relOfSteps (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q)) :
    ((G.preprocess E).killedPow q T hq).rel v x
      = relOfSteps (Gr := (G.preprocess E).graph) E.degree
          ((G.preprocess E).graph.kLen x) ((G.preprocess E).graph.kWalk x)
          (fun i => enc ((G.preprocess E).graph.walkAt ((G.preprocess E).graph.kLen x) v
            ((G.preprocess E).graph.kWalk x) i.val) % 2)
          (fun i => codeOfRel (G.rel ((G.preprocess E).graph.walkAt
            ((G.preprocess E).graph.kLen x) v ((G.preprocess E).graph.kWalk x) i.val).1))
          ((G.preprocess E).graph.startIdx ((G.preprocess E).graph.kLen_le x)
            ((G.preprocess E).graph.kWalk x))
          ((G.preprocess E).graph.endIdx ((G.preprocess E).graph.kLen_le x) v
            ((G.preprocess E).graph.kWalk x)) := by
  funext a b
  rw [rel_killedPow_preprocess, relOfSteps]
  simp only [preRelCode_mod]

/-! ### Types that do not mention the graph -/

/-- The darts of a preprocessed system: the self-loop, the edge-link, the
cloud's and the expander's. This is the dart type of `preprocess` for *every*
graph, so data about a preprocessed walk lives at a type that does not grow with
the input. -/
abbrev PreDart (E : ExpanderFamily) : Type := Unit ⊕ (Option (Fin E.degree) ⊕ Fin E.degree)

omit [Fintype α] in
theorem D_preprocess (G : ConstraintGraph α) (E : ExpanderFamily) :
    (G.preprocess E).graph.D = PreDart E := rfl

/-- Walks of length at most `T` in a preprocessed system, likewise. -/
abbrev PreWalk (E : ExpanderFamily) (T : ℕ) : Type :=
  Σ ℓ : Fin (T + 1), Fin ℓ.val → PreDart E

omit [Fintype α] in
theorem varWalk_preprocess (G : ConstraintGraph α) (E : ExpanderFamily) (T : ℕ) :
    VarWalk (G.preprocess E).graph T = PreWalk E T := rfl

/-- The killed constraint, with every argument at a graph-free type. -/
noncomputable def preRelOfSteps (E : ExpanderFamily) (T : ℕ) (deg n : ℕ)
    (dart : Fin n → PreDart E) (par code : Fin n → ℕ)
    (sIdx eIdx : Fin n → PreWalk E T) (a b : PreWalk E T → α) : Bool :=
  decide (∀ i : Fin n, preRelCode α deg (code i) (par i) (NumEnc.enc (dart i))
    (a (sIdx i)) (b (eIdx i)) = true)

/-- **The killed power's constraint, as data at graph-free types.** Two graphs
whose walks show the same darts, parities, codes and opinion indices carry the
same constraint. -/
theorem rel_killedPow_eq_preRelOfSteps (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q)) :
    ((G.preprocess E).killedPow q T hq).rel v x
      = preRelOfSteps E T E.degree ((G.preprocess E).graph.kLen x)
          ((G.preprocess E).graph.kWalk x)
          (fun i => enc ((G.preprocess E).graph.walkAt ((G.preprocess E).graph.kLen x) v
            ((G.preprocess E).graph.kWalk x) i.val) % 2)
          (fun i => codeOfRel (G.rel ((G.preprocess E).graph.walkAt
            ((G.preprocess E).graph.kLen x) v ((G.preprocess E).graph.kWalk x) i.val).1))
          ((G.preprocess E).graph.startIdx ((G.preprocess E).graph.kLen_le x)
            ((G.preprocess E).graph.kWalk x))
          ((G.preprocess E).graph.endIdx ((G.preprocess E).graph.kLen_le x) v
            ((G.preprocess E).graph.kWalk x)) :=
  rel_killedPow_eq_relOfSteps G E hq v x

/-- **Two graphs whose walks show the same data carry the same constraint.**
The walk itself is shared: an algorithm reads it off the dart's number, which is
the same on both sides. -/
theorem rel_eq_of_data (G G' : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V) (v' : (G'.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    (hpar : (fun i : Fin ((G.preprocess E).graph.kLen x) =>
          enc ((G.preprocess E).graph.walkAt ((G.preprocess E).graph.kLen x) v
            ((G.preprocess E).graph.kWalk x) i.val) % 2)
        = fun i : Fin ((G'.preprocess E).graph.kLen x) =>
          enc ((G'.preprocess E).graph.walkAt ((G'.preprocess E).graph.kLen x) v'
            ((G'.preprocess E).graph.kWalk x) i.val) % 2)
    (hcode : (fun i : Fin ((G.preprocess E).graph.kLen x) =>
          codeOfRel (G.rel ((G.preprocess E).graph.walkAt ((G.preprocess E).graph.kLen x) v
            ((G.preprocess E).graph.kWalk x) i.val).1))
        = fun i : Fin ((G'.preprocess E).graph.kLen x) =>
          codeOfRel (G'.rel ((G'.preprocess E).graph.walkAt ((G'.preprocess E).graph.kLen x) v'
            ((G'.preprocess E).graph.kWalk x) i.val).1))
    (hend : (G.preprocess E).graph.endIdx ((G.preprocess E).graph.kLen_le x) v
          ((G.preprocess E).graph.kWalk x)
        = (G'.preprocess E).graph.endIdx ((G'.preprocess E).graph.kLen_le x) v'
          ((G'.preprocess E).graph.kWalk x)) :
    ((G.preprocess E).killedPow q T hq).rel v x
      = ((G'.preprocess E).killedPow q T hq).rel v' x := by
  erw [rel_killedPow_eq_preRelOfSteps, rel_killedPow_eq_preRelOfSteps, hpar, hcode, hend]
  rfl

end Complexity

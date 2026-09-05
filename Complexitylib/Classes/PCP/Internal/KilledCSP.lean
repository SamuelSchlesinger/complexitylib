/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.KilledWalk
public import Complexitylib.Classes.PCP.Internal.NumEncPi
public import Complexitylib.Classes.PCP.Internal.RegCSP

/-!
# Powering a constraint system along killed walks

Dinur's gap amplification, over the walk law of `KilledWalk`. The vertices are
unchanged; the constraints are indexed by killed walks, and the alphabet is
*opinions* — but now indexed by walks of **any** length up to `T`, so that no
padding is ever needed.

## Opinions

A label at `v` is a function `VarWalk G T → α`: for every walk out of `v` of
length at most `T`, a claim about the label of its endpoint. The index type is
finite of size `∑_{ℓ ≤ T} deg ^ ℓ`, so the alphabet stays a constant
`|α| ^ (∑_{ℓ ≤ T} deg ^ ℓ)`, independent of the number of vertices — which is
what makes the alphabet-reduction step afterwards possible.

Variable-length indices are the point of the design. Were the indices instead
walks of one fixed length, a short prefix would have to be padded out with
self-loops, and the padded indices would form a vanishing sub-cube that the
plurality bound cannot see — which sinks soundness. `KilledWalk` records the
counting behind that failure.

## The constraint

On a killed walk `(v, x)` with effective length `ℓ`, **every** step `i < ℓ` is
checked — no window is needed, since the start's opinion reaches `v i` through
the walk's own first `i` steps and the end's reaches `v (i+1)` through the
reversed walk's first `ℓ - (i+1)` steps. Both indices are genuine walks, of the
exact lengths the walk itself provides.

## Main definitions

- `VarWalk`, `KOpinion` — short walks, and the alphabet of opinions about them
- `RegGraph.startIdx`, `RegGraph.endIdx` — the two indices a step is read at
- `RegCSP.killedPow` — the powered system
- `RegCSP.kTruthful` — the opinion assignment induced by an assignment of `R`

## Main results

- `RegGraph.walkEnd_startIdx`, `RegGraph.walkEnd_endIdx` — the two indices name
  the two ends of the `i`-th dart
- `RegCSP.rel_killedPow_iff` — the constraint, unfolded
- `RegCSP.satisfiable_killedPow_of_satisfiable` — perfect completeness
- `RegCSP.not_satisfies_killedPow_of_faulty` — the soundness witness: a failed
  step with truthful opinions at both ends breaks the constraint
-/

@[expose] public section

namespace Complexity

/-- A walk out of a vertex, of any length up to `T`. -/
abbrev VarWalk (G : RegGraph) (T : ℕ) : Type := Σ ℓ : Fin (T + 1), Fin ℓ.val → G.D

/-- A label of the killed power: a claim about the endpoint of every walk of
length at most `T` out of the vertex. -/
abbrev KOpinion (G : RegGraph) (T : ℕ) (α : Type) : Type := VarWalk G T → α

namespace RegGraph

variable (G : RegGraph)

/-! ### The two indices a step is read at -/

/-- Where the start of a killed walk holds its opinion about the walk's `i`-th
vertex: at the walk's own first `i` steps. -/
def startIdx {T ℓ : ℕ} (hℓ : ℓ ≤ T) (w : Fin ℓ → G.D) (i : Fin ℓ) : VarWalk G T :=
  ⟨⟨i.val, by have := i.isLt; omega⟩, fun j => w (Fin.castLE (le_of_lt i.isLt) j)⟩

/-- Where the end of a killed walk holds its opinion about the walk's
`(i+1)`-st vertex: at the reversed walk's first `ℓ - (i+1)` steps. -/
def endIdx {T ℓ : ℕ} (hℓ : ℓ ≤ T) (v : G.V) (w : Fin ℓ → G.D) (i : Fin ℓ) : VarWalk G T :=
  ⟨⟨ℓ - (i.val + 1), by have := i.isLt; omega⟩,
    fun j : Fin (ℓ - (i.val + 1)) => G.revWalk v w ⟨j.val, by have := j.isLt; omega⟩⟩

/-- The start's index names the `i`-th vertex of the walk. -/
theorem walkEnd_startIdx {T ℓ : ℕ} (hℓ : ℓ ≤ T) (v : G.V) (w : Fin ℓ → G.D) (i : Fin ℓ) :
    G.walkEnd (G.startIdx hℓ w i).1.val v (G.startIdx hℓ w i).2 = G.walkAt ℓ v w i.val := by
  rw [G.walkAt_eq_walkEnd_prefix v w i.val (le_of_lt i.isLt)]
  rfl

/-- The end's index names the `(i+1)`-st vertex of the walk. -/
theorem walkEnd_endIdx {T ℓ : ℕ} (hℓ : ℓ ≤ T) (v : G.V) (w : Fin ℓ → G.D) (i : Fin ℓ) :
    G.walkEnd (G.endIdx hℓ v w i).1.val (G.walkEnd ℓ v w) (G.endIdx hℓ v w i).2
      = G.walkAt ℓ v w (i.val + 1) := by
  have hle : ℓ - (i.val + 1) ≤ ℓ := by omega
  have key : G.walkAt ℓ (G.walkEnd ℓ v w) (G.revWalk v w) (ℓ - (i.val + 1))
      = G.walkAt ℓ v w (i.val + 1) := by
    rw [G.walkAt_revWalk v w _ hle]
    congr 1
    have := i.isLt
    omega
  rw [← key, G.walkAt_eq_walkEnd_prefix (G.walkEnd ℓ v w) (G.revWalk v w) _ hle]
  rfl

/-! ### The effective data of a killed dart -/

/-- The effective length of a killed dart. -/
def kLen {T q : ℕ} (x : (Fin T → G.D) × (Fin T → Fin q)) : ℕ := stopAt x.2

theorem kLen_le {T q : ℕ} (x : (Fin T → G.D) × (Fin T → Fin q)) : G.kLen x ≤ T :=
  stopAt_le x.2

/-- The effective walk of a killed dart. -/
def kWalk {T q : ℕ} (x : (Fin T → G.D) × (Fin T → Fin q)) : Fin (G.kLen x) → G.D :=
  G.preWalk x.1 (stopAt_le x.2)

theorem killedEnd_eq {T q : ℕ} (v : G.V) (x : (Fin T → G.D) × (Fin T → Fin q)) :
    G.killedEnd v x.1 x.2 = G.walkEnd (G.kLen x) v (G.kWalk x) := rfl

end RegGraph

namespace RegCSP

variable {α : Type} (R : RegCSP α) (q T : ℕ) (hq : 0 < q)

/-- The killed power of a constraint system: one constraint per killed walk,
checking `R`'s constraint at every step of the effective walk, between the
opinions the two ends hold about that step's two vertices. -/
def killedPow (R : RegCSP α) (q T : ℕ) (hq : 0 < q) : RegCSP (KOpinion R.graph T α) where
  graph := R.graph.killedPower q T hq
  rel v x a b :=
    decide (∀ i : Fin (R.graph.kLen x),
      R.rel (R.graph.walkAt (R.graph.kLen x) v (R.graph.kWalk x) i.val) (R.graph.kWalk x i)
        (a (R.graph.startIdx (R.graph.kLen_le x) (R.graph.kWalk x) i))
        (b (R.graph.endIdx (R.graph.kLen_le x) v (R.graph.kWalk x) i)) = true)

@[simp] theorem graph_killedPow :
    (R.killedPow q T hq).graph = R.graph.killedPower q T hq := rfl

/-- Powering leaves the vertices alone, so they keep their numbering. -/
noncomputable instance [NumEnc R.graph.V] : NumEnc (R.killedPow q T hq).graph.V :=
  inferInstanceAs (NumEnc R.graph.V)

/-- A killed walk is a tuple of darts and a tuple of coins; both are numbered
digit by digit, so an algorithm can read the walk off. -/
noncomputable instance [NumEnc R.graph.D] : NumEnc (R.killedPow q T hq).graph.D :=
  inferInstanceAs (NumEnc ((Fin T → R.graph.D) × (Fin T → Fin q)))

theorem rel_killedPow_iff (v : R.graph.V) (x : (Fin T → R.graph.D) × (Fin T → Fin q))
    (a b : KOpinion R.graph T α) :
    (R.killedPow q T hq).rel v x a b = true
      ↔ ∀ i : Fin (R.graph.kLen x),
          R.rel (R.graph.walkAt (R.graph.kLen x) v (R.graph.kWalk x) i.val) (R.graph.kWalk x i)
            (a (R.graph.startIdx (R.graph.kLen_le x) (R.graph.kWalk x) i))
            (b (R.graph.endIdx (R.graph.kLen_le x) v (R.graph.kWalk x) i)) = true := by
  exact decide_eq_true_iff

/-! ### Completeness -/

/-- The opinion assignment induced by an assignment of `R`: every claim is the
truth. -/
def kTruthful (σ : R.Assignment) : (R.killedPow q T hq).Assignment :=
  fun v w => σ (R.graph.walkEnd w.1.val v w.2)

/-- A satisfying assignment of `R` makes every killed-walk constraint hold. -/
theorem satisfies_killedPow_truthful {σ : R.Assignment} (hσ : ∀ p, R.Satisfies σ p)
    (x : (R.killedPow q T hq).Dart) :
    (R.killedPow q T hq).Satisfies (R.kTruthful q T hq σ) x := by
  obtain ⟨v, y⟩ := x
  rw [Satisfies, satisfies]
  dsimp only
  rw [show (R.killedPow q T hq).graph.nbr v y = R.graph.killedEnd v y.1 y.2 from rfl]
  erw [rel_killedPow_iff]
  intro i
  have hstart : R.kTruthful q T hq σ v
      (R.graph.startIdx (R.graph.kLen_le y) (R.graph.kWalk y) i)
      = σ (R.graph.walkAt (R.graph.kLen y) v (R.graph.kWalk y) i.val) := by
    rw [kTruthful]
    exact congrArg σ (R.graph.walkEnd_startIdx (R.graph.kLen_le y) v (R.graph.kWalk y) i)
  have hend : R.kTruthful q T hq σ (R.graph.killedEnd v y.1 y.2)
      (R.graph.endIdx (R.graph.kLen_le y) v (R.graph.kWalk y) i)
      = σ (R.graph.walkAt (R.graph.kLen y) v (R.graph.kWalk y) (i.val + 1)) := by
    simp only [kTruthful]
    erw [R.graph.killedEnd_eq]
    exact congrArg σ (R.graph.walkEnd_endIdx (R.graph.kLen_le y) v (R.graph.kWalk y) i)
  rw [hstart, hend]
  have hdart := hσ (R.graph.walkAt (R.graph.kLen y) v (R.graph.kWalk y) i.val,
    R.graph.kWalk y i)
  rw [Satisfies, satisfies] at hdart
  dsimp only at hdart
  rw [← R.graph.walkAt_succ_of_lt v (R.graph.kWalk y) i.isLt] at hdart
  exact hdart

/-- **Perfect completeness.** -/
theorem satisfiable_killedPow_of_satisfiable (hR : R.Satisfiable) :
    (R.killedPow q T hq).Satisfiable := by
  obtain ⟨σ, hσ⟩ := hR
  exact ⟨R.kTruthful q T hq σ, fun x => R.satisfies_killedPow_truthful q T hq hσ x⟩

/-! ### The soundness witness -/

/-- A step of the effective walk that `σ` fails, whose two vertices both ends
shape every soundness count is built from. -/
theorem not_satisfies_killedPow_of_faulty {σ : R.Assignment}
    (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (y : (Fin T → R.graph.D) × (Fin T → Fin q)) (i : Fin (R.graph.kLen y))
    (hfault : ¬ R.Satisfies σ
      (R.graph.walkAt (R.graph.kLen y) v (R.graph.kWalk y) i.val, R.graph.kWalk y i))
    (htruth₁ : A v (R.graph.startIdx (R.graph.kLen_le y) (R.graph.kWalk y) i)
      = σ (R.graph.walkAt (R.graph.kLen y) v (R.graph.kWalk y) i.val))
    (htruth₂ : A (R.graph.killedEnd v y.1 y.2)
        (R.graph.endIdx (R.graph.kLen_le y) v (R.graph.kWalk y) i)
      = σ (R.graph.walkAt (R.graph.kLen y) v (R.graph.kWalk y) (i.val + 1))) :
    ¬ (R.killedPow q T hq).Satisfies A (v, y) := by
  intro hsat
  rw [Satisfies, satisfies] at hsat
  dsimp only at hsat
  rw [show (R.killedPow q T hq).graph.nbr v y = R.graph.killedEnd v y.1 y.2 from rfl,
    rel_killedPow_iff] at hsat
  have hi := hsat i
  rw [htruth₁, htruth₂] at hi
  rw [Satisfies, satisfies] at hfault
  dsimp only at hfault
  rw [← R.graph.walkAt_succ_of_lt v (R.graph.kWalk y) i.isLt] at hfault
  exact hfault hi

end RegCSP

end Complexity

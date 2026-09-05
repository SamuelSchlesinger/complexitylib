/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgPosNum
public import Complexitylib.Classes.PCP.Internal.AlgStep

/-!
# The bounded data a composed edge depends on

A composed edge's second endpoint and its constraint depend on the outer graph
only through what one killed walk meets: the darts it takes, the parity of each
vertex it stands on, the code of each constraint there, and the darts it returns
by — together with the random string and the read. All of that lives in finite
types that do not mention the graph, so it is a *key* of bounded length, and the
edge's data is a function of the key alone.

## Main definitions

- `Complexity.StepKey` — that data
- `Complexity.packKey`, `Complexity.keyOfString` — writing it out as a string,
  and reading it back
- `Complexity.relOfKey` — the constraint it describes
- `Complexity.satSetOfKey` — and the satisfying set

## Main results

- `Complexity.keyOfString_packKey` — the reading inverts the writing
- `Complexity.relOfKey_stepKeyOf` — on a walk's own data it is the killed
  constraint
- `Complexity.cubeOfKey_eq`, `Complexity.codeOfKey_eq` — so the data alone gives
  the composed edge's second endpoint and its constraint
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis Tester

/-- The bounded data a composed edge's head and constraint depend on. -/
abbrev StepKey (E : ExpanderFamily) (T q B C : ℕ) : Type :=
  ((Fin T → PreDart E) × (Fin T → Fin q))
    × ((Fin T → Fin 2) × (Fin T → Fin C))
    × ((Fin T → PreDart E) × (Cube (ROf B) × ReadIdx))

namespace StepKey

variable {E : ExpanderFamily} {T q B C : ℕ} (k : StepKey E T q B C)

/-- The walk's darts. -/
def dart : Fin T → PreDart E := k.1.1

/-- Its coins. -/
def coins : Fin T → Fin q := k.1.2

/-- The parity of the vertex each step stands on. -/
def par : Fin T → Fin 2 := k.2.1.1

/-- The code of the constraint each step meets. -/
def code : Fin T → Fin C := k.2.1.2

/-- The darts the walk returns by. -/
def rev : Fin T → PreDart E := k.2.2.1

/-- The tester's random string. -/
def rand : Cube (ROf B) := k.2.2.2.1

/-- The read. -/
def read : ReadIdx := k.2.2.2.2

/-- How long the effective walk is. -/
def len : ℕ := stopAt k.coins

theorem len_le : k.len ≤ T := stopAt_le _

end StepKey

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The constraint the data describes: at each step of the effective walk, the
preprocessed constraint its code and parity stand for. -/
noncomputable def relOfKey {E : ExpanderFamily} {T q B C : ℕ} (k : StepKey E T q B C) :
    (PreWalk E T → α) → (PreWalk E T → α) → Bool :=
  preRelOfSteps E T E.degree k.len
    (fun i => k.dart ⟨i.val, lt_of_lt_of_le i.isLt k.len_le⟩)
    (fun i => (k.par ⟨i.val, lt_of_lt_of_le i.isLt k.len_le⟩).val)
    (fun i => (k.code ⟨i.val, lt_of_lt_of_le i.isLt k.len_le⟩).val)
    (fun i => ⟨⟨i.val, by have := i.isLt; have := k.len_le; omega⟩,
      fun j => k.dart ⟨j.val, by have := j.isLt; have := i.isLt; have := k.len_le; omega⟩⟩)
    (fun i => ⟨⟨k.len - (i.val + 1), by have := i.isLt; have := k.len_le; omega⟩,
      fun j => k.rev ⟨j.val, by have := j.isLt; have := i.isLt; have := k.len_le; omega⟩⟩)

set_option synthInstance.maxSize 400 in
/-- The satisfying set the data describes. -/
noncomputable def satSetOfKey {E : ExpanderFamily} {T q B C : ℕ}
    (encβ : (PreWalk E T → α) → Cube B) (k : StepKey E T q B C) :
    Finset (Cube (kOf B)) :=
  (Finset.univ.filter fun st : (PreWalk E T → α) × (PreWalk E T → α) =>
      relOfKey k st.1 st.2 = true).image fun st => RegCSP.inputVec encβ st.1 st.2

/-! ### Writing the data out -/

/-- The value a number names, or a default. -/
noncomputable def decOr {X : Type} [NumEnc X] (d : X) (n : ℕ) : X := (NumEnc.dec n).getD d

theorem decOr_enc {X : Type} [NumEnc X] (d a : X) : decOr d (NumEnc.enc a) = a := by
  rw [decOr, NumEnc.dec_enc]
  rfl

variable {E : ExpanderFamily} {T q B C : ℕ}

/-- The data written out: one unary number per component. -/
noncomputable def packKey (k : StepKey E T q B C) : List Bool :=
  pair (pair (List.replicate (NumEnc.enc k.dart) true)
      (List.replicate (NumEnc.enc k.coins) true))
    (pair (pair (List.replicate (NumEnc.enc k.par) true)
        (List.replicate (NumEnc.enc k.code) true))
      (pair (List.replicate (NumEnc.enc k.rev) true)
        (pair (List.replicate (NumEnc.enc k.rand) true)
          (List.replicate (NumEnc.enc k.read) true))))

/-- The data read back from a string, falling back on a default. -/
noncomputable def keyOfString (dflt : StepKey E T q B C) (s : List Bool) :
    StepKey E T q B C :=
  ((decOr dflt.dart (pairFst (pairFst s)).length,
      decOr dflt.coins (pairSnd (pairFst s)).length),
    ((decOr dflt.par
          (pairFst (pairFst (pairSnd s))).length,
        decOr dflt.code
          (pairSnd (pairFst (pairSnd s))).length),
      (decOr dflt.rev (pairFst (pairSnd (pairSnd s))).length,
        (decOr dflt.rand (pairFst (pairSnd
            (pairSnd (pairSnd s)))).length,
          decOr dflt.read (pairSnd (pairSnd
            (pairSnd (pairSnd s)))).length))))

/-- **The reading inverts the writing.** -/
theorem keyOfString_packKey (dflt k : StepKey E T q B C) :
    keyOfString dflt (packKey k) = k := by
  rw [keyOfString, packKey]
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, decOr_enc]
  rfl

/-- **A digit sum is a tuple's number**, when the digits are the entries'. -/
theorem length_digitSum_eq_enc {X : Type} [NumEnc X] {T : ℕ} (s : Fin T → X)
    (digit : ℕ → List Bool → List Bool) (w : List Bool)
    (h : ∀ (j : ℕ) (hj : j < T), (digit j w).length = NumEnc.enc (s ⟨j, hj⟩)) :
    (digitSum (NumEnc.card X) digit T w).length = NumEnc.enc s := by
  rw [length_digitSum]
  show _ = ∑ j ∈ Finset.range T, NumEnc.encAt s j * NumEnc.card X ^ j
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [h j hj, NumEnc.encAt, dite_eq_left hj]

/-- The data a killed walk actually shows. -/
noncomputable def stepKeyOf (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    (B : ℕ) (z : Cube (ROf B)) (i : ReadIdx) :
    StepKey E T q B (Fintype.card (α → α → Bool)) :=
  ((x.1, x.2),
    ((fun j => if h : j.val < (G.preprocess E).graph.kLen x then
          ⟨NumEnc.enc ((G.preprocess E).graph.walkAt ((G.preprocess E).graph.kLen x) v
            ((G.preprocess E).graph.kWalk x) j.val) % 2, Nat.mod_lt _ (by omega)⟩
        else 0,
      fun j => if h : j.val < (G.preprocess E).graph.kLen x then
          ⟨codeOfRel (G.rel ((G.preprocess E).graph.walkAt ((G.preprocess E).graph.kLen x) v
            ((G.preprocess E).graph.kWalk x) j.val).1), codeOfRel_lt _⟩
        else 0),
    ((G.preprocess E).graph.killedRev v x.1 x.2, (z, i))))

omit [Nonempty α] in
/-- **The data a walk shows describes that walk's constraint.** -/
theorem relOfKey_stepKeyOf (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    (B : ℕ) (z : Cube (ROf B)) (i : ReadIdx) :
    relOfKey (α := α) (stepKeyOf G E v x B z i)
      = ((G.preprocess E).killedPow q T hq).rel v x := by
  rw [rel_killedPow_eq_preRelOfSteps, relOfKey]
  simp only [stepKeyOf, StepKey.dart, StepKey.par, StepKey.code, StepKey.rev, StepKey.coins,
    StepKey.len, RegGraph.kLen, RegGraph.kWalk]
  congr 1 <;> funext i <;>
    first
      | (congr 1
         funext j
         rw [RegGraph.killedRev, RegGraph.extWalk]
         dsimp only
         rw [dite_eq_left (by have := j.isLt; omega)])
      | (congr 1
         have hi : (i : ℕ) < stopAt x.2 := by have := i.isLt; omega
         simp [hi]
         exact Fin.ext rfl)
      | (have hi : (i : ℕ) < stopAt x.2 := by have := i.isLt; omega
         simp [hi])

set_option synthInstance.maxSize 400 in
omit [Nonempty α] in
/-- **The data a walk shows describes that walk's satisfying set.** -/
theorem satSetOfKey_stepKeyOf (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    {B : ℕ} (z : Cube (ROf B)) (i : ReadIdx) (encβ : (PreWalk E T → α) → Cube B) :
    satSetOfKey encβ (stepKeyOf G E v x B z i)
      = ((G.preprocess E).killedPow q T hq).satSet encβ (v, x) := by
  show (Finset.univ.filter fun st : (PreWalk E T → α) × (PreWalk E T → α) =>
      relOfKey (stepKeyOf G E v x B z i) st.1 st.2 = true).image
      (fun st => RegCSP.inputVec encβ st.1 st.2) = _
  rw [relOfKey_stepKeyOf (hq := hq)]
  rfl

/-- The cube the data names. -/
noncomputable def cubeOfKey {E : ExpanderFamily} {T q B C : ℕ}
    (encβ : (PreWalk E T → α) → Cube B) (k : StepKey E T q B C) : ℕ :=
  RegCSP.cubeOfSet (satSetOfKey encβ k) k.rand k.read

/-- The constraint code the data names. -/
noncomputable def codeOfKey {E : ExpanderFamily} {T q B C : ℕ}
    (encβ : (PreWalk E T → α) → Cube B) (k : StepKey E T q B C) : ℕ :=
  codeOfRel (MultiTest.relOfCheck (RegCSP.checkOfSet (satSetOfKey encβ k) k.rand) k.read)

omit [Nonempty α] in
/-- **The data gives the composed edge's cube.** -/
theorem cubeOfKey_eq (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    {B : ℕ} (z : Cube (ROf B)) (i : ReadIdx) (encβ : (PreWalk E T → α) → Cube B) :
    cubeOfKey encβ (stepKeyOf G E v x B z i)
      = ((G.preprocess E).killedPow q T hq).cubeNum encβ (v, x) z i := by
  rw [cubeOfKey, satSetOfKey_stepKeyOf G E hq v x z i encβ]
  erw [RegCSP.cubeNum_eq_cubeOfSet]
  rfl

omit [Nonempty α] in
/-- **And the composed edge's constraint.** -/
theorem codeOfKey_eq (G : ConstraintGraph α) (E : ExpanderFamily) {q T : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    {B : ℕ} (z : Cube (ROf B)) (i : ReadIdx) (encβ : (PreWalk E T → α) → Cube B) :
    codeOfKey encβ (stepKeyOf G E v x B z i)
      = codeOfRel (MultiTest.relOfCheck
          ((((G.preprocess E).killedPow q T hq).compose encβ).check (v, x) z) i) := by
  rw [codeOfKey, satSetOfKey_stepKeyOf G E hq v x z i encβ]
  erw [RegCSP.check_eq_checkOfSet]
  rfl

end Complexity

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgCompose
public import Complexitylib.Classes.PCP.Internal.AlgPreRel
public import Complexitylib.Classes.PCP.Internal.AlgStep

/-!
# A composed position's number

A read of the assembled tester lands in one of three kinds of block: the
encoding block of a vertex, a dart's linear table, or a dart's quadratic table.
Which kind, and which cube inside the block, depends only on the read and the
random string — with two exceptions, where the cube is shifted by the
arithmetization of the dart's satisfying set. Which *block*, on the other hand,
is a vertex or a dart of the outer graph, so it is the only part that grows with
the input.

This module splits a position's number along that seam.

## Main definitions

- `Complexity.RegCSP.readKind` — which kind of block a read lands in
- `Complexity.RegCSP.blockNum`, `Complexity.RegCSP.cubeNum` — the block and the
  cube inside it
- `Complexity.RegCSP.posNum` — the number the two make

## Main results

- `Complexity.RegCSP.enc_pos_compose` — that number is the position's
- `Complexity.RegCSP.val_head_toGraph_compose` — hence the second endpoint of a
  composed edge
- `Complexity.RegCSP.satSet_congr`, `cubeNum_congr`, `check_congr` — all of it
  depends on the outer system only through the dart's constraint
- `Complexity.satSet_eq_of_data`, `Complexity.cubeNum_eq_of_data`,
  `Complexity.check_eq_of_data` — and for a killed power, only through the
  walk's parities and codes, whatever graph it came from
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis Tester

namespace RegCSP

variable {β : Type} [Fintype β] [DecidableEq β] [Nonempty β] (R : RegCSP β)
  [NumEnc R.graph.V] [NumEnc R.graph.D] {B : ℕ} (enc : β → Cube B)

/-- Which kind of block a read's position lies in: an encoding block (`0`), a
dart's linear table (`1`), or a dart's quadratic table (`2`). -/
def readKind : ReadIdx → ℕ
  | .i5r | .i6r => 0
  | .g2x | .g2y | .g2s | .c3cQ | .c3tQ | .k4qG | .k4tG => 2
  | _ => 1

/-- The number of the vertex or dart whose block a read's position lies in. -/
noncomputable def blockNum (p : R.Dart) : ReadIdx → ℕ
  | .i5r => NumEnc.enc p.1
  | .i6r => NumEnc.enc (R.graph.nbr p.1 p.2)
  | .f1x | .f1y | .f1s | .g2x | .g2y | .g2s | .c3cQ | .c3tQ | .c3cX | .c3xX | .c3cY | .c3yY
  | .k4qG | .k4tG | .k4cF | .k4lF | .i5c | .i5b | .i6c | .i6b => NumEnc.enc p

/-- The cube a read names, from the satisfying set alone. -/
noncomputable def cubeOfSet (S : Finset (Cube (kOf B))) (z : Cube (ROf B)) : ReadIdx → ℕ
  | .f1x => NumEnc.enc (leftBlock (blk1 z))
  | .f1y => NumEnc.enc (rightBlock (blk1 z))
  | .f1s => NumEnc.enc (leftBlock (blk1 z) + rightBlock (blk1 z))
  | .g2x => NumEnc.enc (leftBlock (blk2 z))
  | .g2y => NumEnc.enc (rightBlock (blk2 z))
  | .g2s => NumEnc.enc (leftBlock (blk2 z) + rightBlock (blk2 z))
  | .c3cQ => NumEnc.enc (cQ (blk3 z))
  | .c3tQ => NumEnc.enc (tensor (qX (blk3 z)) (qY (blk3 z)) + cQ (blk3 z))
  | .c3cX => NumEnc.enc (cX (blk3 z))
  | .c3xX => NumEnc.enc (qX (blk3 z) + cX (blk3 z))
  | .c3cY => NumEnc.enc (cY (blk3 z))
  | .c3yY => NumEnc.enc (qY (blk3 z) + cY (blk3 z))
  | .k4qG => NumEnc.enc (rightBlock (rightBlock (blk4 z)))
  | .k4tG => NumEnc.enc ((QuadConstraint.combine (oneHotSystem S)
      (leftBlock (blk4 z))).quad + rightBlock (rightBlock (blk4 z)))
  | .k4cF => NumEnc.enc (leftBlock (rightBlock (blk4 z)))
  | .k4lF => NumEnc.enc ((QuadConstraint.combine (oneHotSystem S)
      (leftBlock (blk4 z))).lin + leftBlock (rightBlock (blk4 z)))
  | .i5r => NumEnc.enc (leftBlock (blk5 z))
  | .i5c => NumEnc.enc (rightBlock (blk5 z))
  | .i5b => NumEnc.enc (basisVec (inTail B (leftBlock (blk5 z))) + rightBlock (blk5 z))
  | .i6r => NumEnc.enc (leftBlock (blk6 z))
  | .i6c => NumEnc.enc (rightBlock (blk6 z))
  | .i6b => NumEnc.enc (basisVec (inHead B (leftBlock (blk6 z))) + rightBlock (blk6 z))

/-- The number of the cube a read's position names inside its block. -/
noncomputable def cubeNum (p : R.Dart) (z : Cube (ROf B)) : ReadIdx → ℕ :=
  cubeOfSet (R.satSet enc p) z

/-- The number a kind, a block and a cube make: encoding blocks first, then the
linear tables, then the quadratic ones. -/
def posNum (cardV cardD cardB cardN cardNN k w c : ℕ) : ℕ :=
  if k = 0 then w * cardB + c
  else if k = 1 then cardV * cardB + (w * cardN + c)
  else cardV * cardB + (cardV * cardD * cardN + (w * cardNN + c))

omit [DecidableEq β] [Nonempty β] in
/-- **A composed position's number.** -/
theorem enc_pos_compose (p : R.Dart) (z : Cube (ROf B)) (i : ReadIdx) :
    NumEnc.enc ((R.compose enc).pos p z i)
      = posNum (NumEnc.card R.graph.V) (NumEnc.card R.graph.D) (NumEnc.card (Cube B))
        (NumEnc.card (Cube (nOf B))) (NumEnc.card (Cube (nOf B * nOf B)))
        (readKind i) (R.blockNum p i) (R.cubeNum enc p z i) := by
  cases i <;> rfl

omit [Fintype β] [DecidableEq β] [Nonempty β] in
/-- **The block of an input read is the dart's tail**, which its number names by
division. -/
theorem blockNum_i5r (p : R.Dart) :
    R.blockNum p .i5r = NumEnc.enc p / NumEnc.card R.graph.D := by
  have hlt : NumEnc.enc p.2 < NumEnc.card R.graph.D := NumEnc.enc_lt p.2
  rw [blockNum, R.enc_dart p, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

omit [Fintype β] [DecidableEq β] [Nonempty β] in
/-- **The block of the other input read is the dart's head.** -/
theorem blockNum_i6r (p : R.Dart) :
    R.blockNum p .i6r = NumEnc.enc (R.graph.rot p).1 := rfl

omit [DecidableEq β] [Nonempty β] in
/-- **The second endpoint of a composed edge.** -/
theorem val_head_toGraph_compose (k : Fin (Fintype.card (R.compose enc).Edge)) :
    ((R.compose enc).toGraph.head k).val
      = posNum (NumEnc.card R.graph.V) (NumEnc.card R.graph.D) (NumEnc.card (Cube B))
        (NumEnc.card (Cube (nOf B))) (NumEnc.card (Cube (nOf B * nOf B)))
        (readKind ((R.compose enc).edgeOf k).2.2)
        (R.blockNum ((R.compose enc).edgeOf k).1 ((R.compose enc).edgeOf k).2.2)
        (R.cubeNum enc ((R.compose enc).edgeOf k).1 ((R.compose enc).edgeOf k).2.1
          ((R.compose enc).edgeOf k).2.2) := by
  erw [MultiTest.val_head_toGraph, enc_pos_compose]

/-- The test's verdict, from the satisfying set alone. -/
noncomputable def checkOfSet (S : Finset (Cube (kOf B))) (z : Cube (ROf B))
    (rd : ReadIdx → ZMod 2) : Bool :=
  decide (bitFormula S z rd)

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **The cube depends on the satisfying set alone.** -/
theorem cubeNum_eq_cubeOfSet (p : R.Dart) (z : Cube (ROf B)) (i : ReadIdx) :
    R.cubeNum enc p z i = cubeOfSet (R.satSet enc p) z i := rfl

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **And so does the verdict.** -/
theorem check_eq_checkOfSet (p : R.Dart) (z : Cube (ROf B)) :
    (R.compose enc).check p z = checkOfSet (R.satSet enc p) z := rfl

omit [DecidableEq β] [Nonempty β] in
set_option maxHeartbeats 800000 in
/-- **An edge's data and all three of its numbers**, in one package: a caller
never has to spell the composed system out, nor match anything against it. -/
theorem edge_facts (e : ℕ) (he : e < (R.compose enc).toGraph.numEdges) :
    ∃ (p : R.Dart) (z : Cube (ROf B)) (i : ReadIdx),
      e = ((NumEnc.enc p.1 * NumEnc.card R.graph.D + NumEnc.enc p.2) * 2 ^ ROf B
            + NumEnc.enc z) * 22 + NumEnc.enc i
        ∧ ((R.compose enc).toGraph.tail ⟨e, he⟩).val = (R.compose enc).tailNum e
        ∧ ((R.compose enc).toGraph.head ⟨e, he⟩).val
            = posNum (NumEnc.card R.graph.V) (NumEnc.card R.graph.D)
                (NumEnc.card (Cube B)) (NumEnc.card (Cube (nOf B)))
                (NumEnc.card (Cube (nOf B * nOf B)))
                (readKind i) (R.blockNum p i) (R.cubeNum enc p z i)
        ∧ (R.compose enc).toGraph.rel ⟨e, he⟩
            = MultiTest.relOfCheck ((R.compose enc).check p z) i := by
  obtain ⟨p, z, i, hp, hz, hi, hsplit⟩ := R.edge_data B enc e he
  refine ⟨p, z, i, hsplit, (MultiTest.tailNum_eq _ ⟨e, he⟩).symm, ?_, ?_⟩
  · erw [hp, hz, hi, MultiTest.val_head_toGraph, enc_pos_compose]
    rfl
  · rw [hp, hz, hi]
    exact MultiTest.rel_toGraph_eq _ _

/-! ### Everything depends on the dart's constraint alone -/

variable {R' : RegCSP β} [NumEnc R'.graph.V] [NumEnc R'.graph.D]

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D]
  [NumEnc R'.graph.V] [NumEnc R'.graph.D] in
/-- **The satisfying set depends only on the dart's constraint.** -/
theorem satSet_congr (p : R.Dart) (p' : R'.Dart)
    (h : R.rel p.1 p.2 = R'.rel p'.1 p'.2) :
    R.satSet enc p = R'.satSet enc p' := by
  rw [satSet, satSet, h]

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **So does the cube a read names**, even across two different systems. -/
-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem cubeNum_congr {β' : Type} [Fintype β'] [DecidableEq β'] [Nonempty β']
    {R' : RegCSP β'} [NumEnc R'.graph.V] [NumEnc R'.graph.D] {enc' : β' → Cube B}
    (p : R.Dart) (p' : R'.Dart) (z : Cube (ROf B)) (i : ReadIdx)
    (h : R.satSet enc p = R'.satSet enc' p') :
    R.cubeNum enc p z i = R'.cubeNum enc' p' z i := by
  rw [cubeNum, cubeNum, h]

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **And so does the test's verdict.** -/
-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem check_congr {β' : Type} [Fintype β'] [DecidableEq β'] [Nonempty β']
    {R' : RegCSP β'} [NumEnc R'.graph.V] [NumEnc R'.graph.D] {enc' : β' → Cube B}
    (p : R.Dart) (p' : R'.Dart) (z : Cube (ROf B))
    (h : R.satSet enc p = R'.satSet enc' p') :
    (R.compose enc).check p z = (R'.compose enc').check p' z := by
  show (fun rd => decide (bitFormula (R.satSet enc p) z rd))
    = fun rd => decide (bitFormula (R'.satSet enc' p') z rd)
  rw [h]

end RegCSP

/-! ### Across two graphs -/

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Nonempty α] in
/-- **Two graphs whose walks show the same data have the same satisfying set.**
Both sides live in `Finset (Cube (kOf B))`, a type that does not mention either
graph. -/
theorem satSet_eq_of_data (G G' : ConstraintGraph α) (E : ExpanderFamily) {q T B : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V) (v' : (G'.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    (encβ : KOpinion (G.preprocess E).graph T α → Cube B)
    (hpar : (fun i : Fin ((G.preprocess E).graph.kLen x) =>
          NumEnc.enc ((G.preprocess E).graph.walkAt ((G.preprocess E).graph.kLen x) v
            ((G.preprocess E).graph.kWalk x) i.val) % 2)
        = fun i : Fin ((G'.preprocess E).graph.kLen x) =>
          NumEnc.enc ((G'.preprocess E).graph.walkAt ((G'.preprocess E).graph.kLen x) v'
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
    ((G.preprocess E).killedPow q T hq).satSet encβ (v, x)
      = ((G'.preprocess E).killedPow q T hq).satSet encβ (v', x) := by
  have h := rel_eq_of_data G G' E hq v v' x hpar hcode hend
  show (Finset.univ.filter fun st : KOpinion (G.preprocess E).graph T α
        × KOpinion (G.preprocess E).graph T α =>
      ((G.preprocess E).killedPow q T hq).rel v x st.1 st.2 = true).image
      (fun st => RegCSP.inputVec encβ st.1 st.2) = _
  rw [h]
  rfl

/-- **The cube a read names is the same across two such graphs.** -/
theorem cubeNum_eq_of_data (G G' : ConstraintGraph α) (E : ExpanderFamily) {q T B : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V) (v' : (G'.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    (encβ : KOpinion (G.preprocess E).graph T α → Cube B) (z : Cube (Tester.ROf B))
    (i : ReadIdx)
    (h : ((G.preprocess E).killedPow q T hq).satSet encβ (v, x)
      = ((G'.preprocess E).killedPow q T hq).satSet encβ (v', x)) :
    ((G.preprocess E).killedPow q T hq).cubeNum encβ (v, x) z i
      = ((G'.preprocess E).killedPow q T hq).cubeNum encβ (v', x) z i :=
  RegCSP.cubeNum_congr (R := (G.preprocess E).killedPow q T hq) (enc := encβ)
    (R' := (G'.preprocess E).killedPow q T hq) (enc' := encβ) (v, x) (v', x) z i h

/-- **And so is the test's verdict.** -/
theorem check_eq_of_data (G G' : ConstraintGraph α) (E : ExpanderFamily) {q T B : ℕ}
    (hq : 0 < q) (v : (G.preprocess E).graph.V) (v' : (G'.preprocess E).graph.V)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    (encβ : KOpinion (G.preprocess E).graph T α → Cube B) (z : Cube (Tester.ROf B))
    (h : ((G.preprocess E).killedPow q T hq).satSet encβ (v, x)
      = ((G'.preprocess E).killedPow q T hq).satSet encβ (v', x)) :
    (((G.preprocess E).killedPow q T hq).compose encβ).check (v, x) z
      = (((G'.preprocess E).killedPow q T hq).compose encβ).check (v', x) z :=
  RegCSP.check_congr (R := (G.preprocess E).killedPow q T hq) (enc := encβ)
    (R' := (G'.preprocess E).killedPow q T hq) (enc' := encβ) (v, x) (v', x) z h

end Complexity

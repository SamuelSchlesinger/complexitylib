/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.KilledCSP
public import Complexitylib.Classes.PCP.Internal.NumEncPi
public import Complexitylib.Classes.PCP.Internal.AlgPreprocess

/-!
# The killed walk, in numbers

A dart of the powered graph is a tuple of steps together with a tuple of coins;
the walk runs until the first coin that is zero. `NumEncPi` numbers both tuples
digit by digit, so an algorithm recovers a step or a coin by dividing and taking
the remainder. This module reads the stopping rule off those digits.

## Main definitions

- `Complexity.stopAtNum` — where a killed walk stops, from the coins' number

## Main results

- `Complexity.stopAtNum_eq` — it is the abstract stopping index
- `Complexity.ConstraintGraph.walkNum_eq` — and following the step digits walks
  the preprocessed graph
- `Complexity.ConstraintGraph.killedRevNum_eq` — the dart a killed walk comes
  back by, digit by digit
- `Complexity.ConstraintGraph.killedRotNum_eq` — the powered graph's rotation
  map, in numbers
-/

@[expose] public section

namespace Complexity

open NumEnc

theorem findIdx_congr {β : Type} {l : List β} {p q : β → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.findIdx p = l.findIdx q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.findIdx_cons, List.findIdx_cons, h a List.mem_cons_self,
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- Where a killed walk stops, read off the coins' number: the first digit that
is zero, or the whole length if there is none. -/
def stopAtNum (T q c : ℕ) : ℕ :=
  (List.finRange T).findIdx fun j => (c / q ^ j.val) % q == 0

/-- **The digits give the stopping index.** -/
theorem stopAtNum_eq {T q : ℕ} (hq : 0 < q) (c : Fin T → Fin q) :
    stopAtNum T q (enc c) = stopAt c := by
  rw [stopAtNum, stopAt]
  refine findIdx_congr fun j _ => ?_
  have hcard : card (Fin q) = q := rfl
  have hdig : (enc c / q ^ j.val) % q = enc (c j) := by
    have h := digit_sum (c := card (Fin q)) hq (encAt c) j.isLt
      (fun i hi => encAt_lt c hi)
    rw [hcard] at h
    rw [show (enc c : ℕ) = ∑ i ∈ Finset.range T, encAt c i * q ^ i from rfl, h, encAt,
      dite_eq_left j.isLt]
  rw [hdig]
  rfl

namespace ConstraintGraph

variable {α : Type} [DecidableEq α] (G : ConstraintGraph α) (E : ExpanderFamily)

/-- How many darts the preprocessed graph has at each vertex. -/
noncomputable def preDeg : ℕ := card (G.preprocess E).graph.D

/-- The vertex reached after `k` steps, following the digits of `s`. -/
noncomputable def walkNum (G : ConstraintGraph α) (E : ExpanderFamily) (s : ℕ) :
    ℕ → ℕ → ℕ
  | 0, v => v
  | k + 1, v =>
      (G.preRotNum E (walkNum G E s k v) ((s / G.preDeg E ^ k) % G.preDeg E)).1

/-- The digits of a tuple's number are its entries' numbers. -/
theorem digit_enc {T : ℕ} (s : Fin T → (G.preprocess E).graph.D) (hpos : 0 < G.preDeg E)
    (k : ℕ) (hk : k < T) : (enc s / G.preDeg E ^ k) % G.preDeg E = enc (s ⟨k, hk⟩) := by
  have h := digit_sum (c := card (G.preprocess E).graph.D) hpos (encAt s) hk
    (fun i hi => encAt_lt s hi)
  rw [show (enc s : ℕ)
    = ∑ i ∈ Finset.range T, encAt s i * card (G.preprocess E).graph.D ^ i from rfl,
    preDeg, h, encAt, dite_eq_left hk]

/-- **Following the digits walks the graph.** The steps are read from any number
whose digits are the tuple's entries, so a prefix of a longer walk may be run
from that walk's own number. -/
theorem walkNum_eq {T : ℕ} (v : G.HalfEdge) (s : Fin T → (G.preprocess E).graph.D) (n : ℕ)
    (hdig : ∀ (k : ℕ) (hk : k < T), (n / G.preDeg E ^ k) % G.preDeg E = enc (s ⟨k, hk⟩)) :
    ∀ {k : ℕ}, k ≤ T →
      G.walkNum E n k (enc v) = enc ((G.preprocess E).graph.walkAt T v s k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hkT : k < T := by omega
      rw [walkNum, ih (by omega), hdig k hkT,
        (G.preprocess E).graph.walkAt_succ_of_lt v s hkT, RegGraph.nbr]
      exact congrArg Prod.fst (G.preRotNum_eq E _ _)

/-! ### The dart the walk comes back by -/

/-- The dart a killed walk comes back by, in numbers: below the stopping index
the digits are the labels pointing back, read in reverse order; above it they
are the original steps. -/
noncomputable def killedRevNum (T q v s c : ℕ) : ℕ :=
  ∑ j ∈ Finset.range T,
    (if j < stopAtNum T q c then
        (G.preRotNum E (G.walkNum E s (stopAtNum T q c - 1 - j) v)
            ((s / G.preDeg E ^ (stopAtNum T q c - 1 - j)) % G.preDeg E)).2
      else (s / G.preDeg E ^ j) % G.preDeg E) * G.preDeg E ^ j

/-- **The digits give the dart the walk comes back by.** -/
theorem killedRevNum_eq {T q : ℕ} (hq : 0 < q) (hpos : 0 < G.preDeg E) (v : G.HalfEdge)
    (s : Fin T → (G.preprocess E).graph.D) (c : Fin T → Fin q) :
    G.killedRevNum E T q (enc v) (enc s) (enc c)
      = enc ((G.preprocess E).graph.killedRev v s c) := by
  have hdig : ∀ (k : ℕ) (hk : k < T),
      (enc s / G.preDeg E ^ k) % G.preDeg E = enc (s ⟨k, hk⟩) := by
    intro k hk
    have h := digit_sum (c := card (G.preprocess E).graph.D) hpos (encAt s) hk
      (fun i hi => encAt_lt s hi)
    rw [show (enc s : ℕ)
      = ∑ i ∈ Finset.range T, encAt s i * card (G.preprocess E).graph.D ^ i from rfl,
      preDeg, h, encAt, dite_eq_left hk]
  have hstop : stopAtNum T q (enc c) = stopAt c := stopAtNum_eq hq c
  have hle : stopAt c ≤ T := stopAt_le c
  rw [killedRevNum, hstop,
    show (enc ((G.preprocess E).graph.killedRev v s c) : ℕ)
      = ∑ j ∈ Finset.range T,
        encAt ((G.preprocess E).graph.killedRev v s c) j * G.preDeg E ^ j from rfl]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  congr 1
  rw [encAt, dite_eq_left hj]
  by_cases hjlt : j < stopAt c
  · rw [ite_eq_left hjlt]
    have hk : stopAt c - 1 - j < T := by omega
    rw [hdig _ hk]
    have hrev : ((G.preprocess E).graph.killedRev v s c) ⟨j, hj⟩
        = (G.preprocess E).graph.backLabel v
            ((G.preprocess E).graph.preWalk s hle) (Fin.rev ⟨j, hjlt⟩) := by
      simp only [RegGraph.killedRev, RegGraph.extWalk, dite_eq_left hjlt,
        RegGraph.revWalk]
    rw [hrev]
    simp only [RegGraph.backLabel]
    have hidx : (Fin.rev (⟨j, hjlt⟩ : Fin (stopAt c))).val = stopAt c - 1 - j := by
      rw [Fin.val_rev]
      show stopAt c - (j + 1) = stopAt c - 1 - j
      omega
    rw [hidx]
    have hwalk : ((G.preprocess E).graph.preWalk s hle) (Fin.rev (⟨j, hjlt⟩ : Fin (stopAt c)))
        = s ⟨stopAt c - 1 - j, hk⟩ := by
      rw [RegGraph.preWalk]
      congr 1
      exact Fin.ext hidx
    rw [hwalk]
    have hpre : ∀ (k : ℕ) (hk : k < stopAt c),
        (enc s / G.preDeg E ^ k) % G.preDeg E
          = enc (((G.preprocess E).graph.preWalk s hle) ⟨k, hk⟩) := by
      intro k hk
      rw [G.digit_enc E s hpos k (lt_of_lt_of_le hk hle), RegGraph.preWalk]
    rw [G.walkNum_eq E v ((G.preprocess E).graph.preWalk s hle) (enc s) hpre (by omega)]
    exact congrArg Prod.snd (G.preRotNum_eq E _ _)
  · rw [ite_eq_right hjlt, hdig _ hj]
    congr 1
    simp only [RegGraph.killedRev, RegGraph.extWalk, dite_eq_right hjlt]

/-! ### The powered graph's rotation map -/

/-- The powered graph's rotation map, in numbers: walk to the end, come back by
the reversed labels, and keep the coins. -/
noncomputable def killedRotNum (T q v s c : ℕ) : ℕ × ℕ :=
  (G.walkNum E s (stopAtNum T q c) v, G.killedRevNum E T q v s c * q ^ T + c)

/-- **The numbers run the powered graph's rotation map.** -/
theorem killedRotNum_eq {T q : ℕ} (hq : 0 < q) (hpos : 0 < G.preDeg E) (v : G.HalfEdge)
    (x : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q))
    {w : G.HalfEdge} {y : (Fin T → (G.preprocess E).graph.D) × (Fin T → Fin q)}
    (hw : ((G.preprocess E).graph.killedPower q T hq).rot (v, x) = (w, y)) :
    G.killedRotNum E T q (enc v) (enc x.1) (enc x.2) = (enc w, enc y) := by
  have hle : stopAt x.2 ≤ T := stopAt_le x.2
  have hstop : stopAtNum T q (enc x.2) = stopAt x.2 := stopAtNum_eq hq x.2
  have hw1 : ((G.preprocess E).graph.killedEnd v x.1 x.2) = w := congrArg Prod.fst hw
  have hw2 : (((G.preprocess E).graph.killedRev v x.1 x.2), x.2) = y := congrArg Prod.snd hw
  refine Prod.ext ?_ ?_
  · show G.walkNum E (enc x.1) (stopAtNum T q (enc x.2)) (enc v) = _
    rw [hstop]
    have hpre : ∀ (k : ℕ) (hk : k < stopAt x.2),
        (enc x.1 / G.preDeg E ^ k) % G.preDeg E
          = enc (((G.preprocess E).graph.preWalk x.1 hle) ⟨k, hk⟩) := by
      intro k hk
      rw [G.digit_enc E x.1 hpos k (lt_of_lt_of_le hk hle), RegGraph.preWalk]
    rw [G.walkNum_eq E v ((G.preprocess E).graph.preWalk x.1 hle) (enc x.1) hpre le_rfl]
    rw [← hw1]
    simp only [RegGraph.killedEnd]
    erw [← RegGraph.walkAt_self_eq_walkEnd]
    rfl
  · show G.killedRevNum E T q (enc v) (enc x.1) (enc x.2) * q ^ T + enc x.2 = _
    rw [G.killedRevNum_eq E hq hpos v x.1 x.2, ← hw2]
    rfl

end ConstraintGraph

end Complexity

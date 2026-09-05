/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TranscriptEnc

/-!
# The walk of an interactive protocol's game tree

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.IPGameTree` reduces membership in a language of `IP`
to a recursion written as two counter loops:

```
gvalR 0       ps = #{coin strings that make the verifier accept below `ps`}
gvalR (n + 1) ps = ∑ over the verifier's messages, of the maximum over the prover's replies
```

This file is the machine that walks it, on an inductive state — the same discipline Savitch's
theorem uses in `Complexitylib.Classes.Containments.Internal.SavitchSem`. A stack holds one frame
per round, carrying the two message counters and the running sum and maximum; the bottom frame is
a leaf, carrying the coin counter and its tally.

Everything the walk needs from the protocol is packed into `Complexity.IPM.Params`: the message
bound, the coin width, and the single test *does this coin string make the verifier accept, below
these rounds*.

## Main definitions

- `Complexity.IPM.Frm`, `Complexity.IPM.Sst` — a frame and the machine's state
- `Complexity.IPM.roundsOf` — the rounds a stack records
- `Complexity.IPM.step` — one step of the walk

## Main results

- the `step_*` lemmas — one for each shape the step can take
-/

@[expose] public section

namespace Complexity

namespace IPM

/-! ## The data the walk needs -/

/-- What the walk needs to know about the protocol. -/
structure Params where
  /-- The bound on either side's message length. -/
  m : ℕ
  /-- The number of coins, so the width of a coin string. -/
  t : ℕ
  /-- Does this coin string make the verifier accept, below these rounds? -/
  ok : List (List Bool × List Bool) → List Bool → Bool

/-- The zero of the width a count is held in: one bit more than the coin width, so that a count
of up to `2 ^ t` fits. -/
def zeroCount (P : Params) : List Bool := List.replicate (P.t + 1) false

/-- The first coin string. -/
def zeroCoin (P : Params) : List Bool := List.replicate P.t false

/-! ## The state -/

/-- A frame of the walk: the rounds still to play, the two message counters, and the running sum
and maximum. At a leaf `a` is the coin string and `sum` its tally. -/
structure Frm where
  /-- The rounds still to play, in unary. -/
  lvl : List Bool
  /-- The verifier message currently being summed over. -/
  v : List Bool
  /-- The prover reply currently being maximized over; the coin string at a leaf. -/
  a : List Bool
  /-- The running sum; the running tally at a leaf. -/
  sum : List Bool
  /-- The running maximum; unused at a leaf. -/
  best : List Bool
  /-- The body of the encoding of the rounds below this frame. Carrying it is what makes the
  leaf's consistency test a per-frame check rather than a walk back down the stack. -/
  body : List Bool

/-- The machine's state. -/
structure Sst where
  /-- The bit the space-bounded iteration watches. -/
  done : Bool
  /-- The answer, once it is known. -/
  ansBit : Bool
  /-- The value a finished subtree is returning. -/
  ret : Option (List Bool)
  /-- The stack, top frame first. -/
  stk : List Frm

/-- The rounds a stack records: the message pair of every frame below the top, in the order they
were played. -/
def roundsOf (fs : List Frm) : List (List Bool × List Bool) :=
  (fs.map fun g => (g.v, g.a)).reverse

@[simp] theorem roundsOf_nil : roundsOf [] = [] := rfl

@[simp] theorem roundsOf_cons (g : Frm) (fs : List Frm) :
    roundsOf (g :: fs) = roundsOf fs ++ [(g.v, g.a)] := by
  rw [roundsOf, roundsOf, List.map_cons, List.reverse_cons]

@[simp] theorem roundsOf_length (fs : List Frm) : (roundsOf fs).length = fs.length := by
  rw [roundsOf, List.length_reverse, List.length_map]

/-- The frame a node starts from: both counters at the first message, both accumulators zero, and
the body of the rounds above it. At a leaf the coin counter starts at the first coin string
instead. -/
def freshFrm (P : Params) (body lvl : List Bool) : Frm :=
  { lvl := lvl
    v := []
    a := if lvl = [] then zeroCoin P else []
    sum := zeroCount P
    best := zeroCount P
    body := body }

/-- The frame a branch pushes: a fresh node for the pair it is currently trying, carrying the
body of the transcript that leads to it. -/
def childFrm (P : Params) (f : Frm) : Frm :=
  freshFrm P (f.body ++ encMsg f.v ++ encMsg f.a) (f.lvl.drop 1)

@[simp] theorem childFrm_lvl (P : Params) (f : Frm) : (childFrm P f).lvl = f.lvl.drop 1 := rfl

/-! ## One step -/

/-- The verdict the walk finishes with: the count `r` exceeds half the coin space. -/
def cmpBit (P : Params) (r : List Bool) : Bool :=
  ltBitsLE false (twoPowBits P.t) (false :: r)

/-- One step of the walk. -/
def step (P : Params) (s : Sst) : Sst :=
  if s.done then ⟨s.ansBit, s.ansBit, s.ret, s.stk⟩
  else
    match s.stk, s.ret with
    | [], r => ⟨true, cmpBit P (r.getD []), r, []⟩
    | f :: fs, none =>
        if f.lvl = [] then
          if bumpOver f.a then
            ⟨false, s.ansBit,
              some (if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum), fs⟩
          else
            ⟨false, s.ansBit, none,
              { f with
                a := bumpBits f.a,
                sum := if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum } :: fs⟩
        else
          ⟨false, s.ansBit, none,
            childFrm P f :: f :: fs⟩
    | f :: fs, some r =>
        if (nextStr f.a).length ≤ P.m then
          ⟨false, s.ansBit, none,
            { f with a := nextStr f.a, best := maxBits f.best r } :: fs⟩
        else
          if (nextStr f.v).length ≤ P.m then
            ⟨false, s.ansBit, none,
              { f with
                v := nextStr f.v,
                a := [],
                sum := addBits f.sum (maxBits f.best r),
                best := zeroCount P } :: fs⟩
          else ⟨false, s.ansBit, some (addBits f.sum (maxBits f.best r)), fs⟩

variable (P : Params)

@[simp] theorem step_of_done (a : Bool) (r : Option (List Bool)) (stk : List Frm) :
    step P ⟨true, a, r, stk⟩ = ⟨a, a, r, stk⟩ := rfl

@[simp] theorem step_of_empty (a : Bool) (r : Option (List Bool)) :
    step P ⟨false, a, r, []⟩ = ⟨true, cmpBit P (r.getD []), r, []⟩ := rfl

theorem step_leaf_last (a : Bool) (f : Frm) (fs : List Frm) (hl : f.lvl = [])
    (hov : bumpOver f.a = true) :
    step P ⟨false, a, none, f :: fs⟩
      = ⟨false, a, some (if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum), fs⟩ := by
  simp [step, hl, hov]

theorem step_leaf_next (a : Bool) (f : Frm) (fs : List Frm) (hl : f.lvl = [])
    (hov : bumpOver f.a = false) :
    step P ⟨false, a, none, f :: fs⟩
      = ⟨false, a, none,
        { f with
          a := bumpBits f.a,
          sum := if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum } :: fs⟩ := by
  simp [step, hl, hov]

theorem step_push (a : Bool) (f : Frm) (fs : List Frm) (hl : f.lvl ≠ []) :
    step P ⟨false, a, none, f :: fs⟩
      = ⟨false, a, none,
        childFrm P f :: f :: fs⟩ := by
  simp [step, hl]

theorem step_ret_more_a (a : Bool) (f : Frm) (fs : List Frm) (r : List Bool)
    (ha : (nextStr f.a).length ≤ P.m) :
    step P ⟨false, a, some r, f :: fs⟩
      = ⟨false, a, none, { f with a := nextStr f.a, best := maxBits f.best r } :: fs⟩ := by
  simp [step, ha]

theorem step_ret_more_v (a : Bool) (f : Frm) (fs : List Frm) (r : List Bool)
    (ha : ¬ (nextStr f.a).length ≤ P.m) (hv : (nextStr f.v).length ≤ P.m) :
    step P ⟨false, a, some r, f :: fs⟩
      = ⟨false, a, none,
        { f with
          v := nextStr f.v,
          a := [],
          sum := addBits f.sum (maxBits f.best r),
          best := zeroCount P } :: fs⟩ := by
  simp [step, ha, hv]

theorem step_ret_pop (a : Bool) (f : Frm) (fs : List Frm) (r : List Bool)
    (ha : ¬ (nextStr f.a).length ≤ P.m) (hv : ¬ (nextStr f.v).length ≤ P.m) :
    step P ⟨false, a, some r, f :: fs⟩
      = ⟨false, a, some (addBits f.sum (maxBits f.best r)), fs⟩ := by
  simp [step, ha, hv]

/-! ## The invariant the encoding needs -/

/-- Nothing is returning only while the stack is nonempty. -/
def StkOk (s : Sst) : Prop := s.stk = [] → s.ret ≠ none

theorem step_stkOk {s : Sst} (h : StkOk s) : StkOk (step P s) := by
  obtain ⟨d, a, r, stk⟩ := s
  cases d
  · cases stk with
    | nil =>
        obtain ⟨b, rfl⟩ : ∃ b, r = some b := by
          cases r with
          | none => exact absurd rfl (h rfl)
          | some b => exact ⟨b, rfl⟩
        rw [step_of_empty]
        intro _
        simp
    | cons f fs =>
      cases r with
      | none =>
          by_cases hl : f.lvl = []
          · by_cases hov : bumpOver f.a = true
            · rw [step_leaf_last P a f fs hl hov]
              intro _
              simp
            · rw [step_leaf_next P a f fs hl (by simpa using hov)]
              intro hc
              simp at hc
          · rw [step_push P a f fs hl]
            intro hc
            simp at hc
      | some r =>
          by_cases ha : (nextStr f.a).length ≤ P.m
          · rw [step_ret_more_a P a f fs r ha]
            intro hc
            simp at hc
          · by_cases hv : (nextStr f.v).length ≤ P.m
            · rw [step_ret_more_v P a f fs r ha hv]
              intro hc
              simp at hc
            · rw [step_ret_pop P a f fs r ha hv]
              intro _
              simp
  · rw [step_of_done]
    exact h

theorem iterate_stkOk : ∀ (j : ℕ) (s : Sst), StkOk s → StkOk ((step P)^[j] s) := by
  intro j
  induction j with
  | zero => intro s h; exact h
  | succ j ih =>
      intro s h
      rw [Function.iterate_succ_apply]
      exact ih _ (step_stkOk P h)

/-! ## What the walk is computing -/

/-- How many messages either side may send. -/
def msgCount (P : Params) : ℕ := 2 ^ (P.m + 1) - 1

/-- The `i`-th message in the enumeration. -/
def msgOf (i : ℕ) : List Bool := nextStr^[i] []

/-- The `k`-th coin string. -/
def coinOf (P : Params) (k : ℕ) : List Bool := bumpBits^[k] (zeroCoin P)

/-- **What a node of the tree is worth**: a count at a leaf, and a sum of maxima above. -/
def treeVal (P : Params) : ℕ → List (List Bool × List Bool) → ℕ
  | 0, ps => ((Finset.range (2 ^ P.t)).filter fun k => P.ok ps (coinOf P k)).card
  | n + 1, ps =>
      ∑ i ∈ Finset.range (msgCount P),
        (Finset.range (msgCount P)).sup fun j => treeVal P n (ps ++ [(msgOf i, msgOf j)])

/-- The best the prover can do at the verifier's `i`-th message, from its `ja`-th reply on. -/
def tailCol (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) (i ja : ℕ) : ℕ :=
  (Finset.Ico ja (msgCount P)).sup fun j => treeVal P n (ps ++ [(msgOf i, msgOf j)])

/-- The best the prover can do at the verifier's `i`-th message. -/
def col (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) (i : ℕ) : ℕ :=
  tailCol P n ps i 0

theorem treeVal_zero (P : Params) (ps : List (List Bool × List Bool)) :
    treeVal P 0 ps = ((Finset.range (2 ^ P.t)).filter fun k => P.ok ps (coinOf P k)).card := rfl

theorem treeVal_succ (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) :
    treeVal P (n + 1) ps = ∑ i ∈ Finset.range (msgCount P), col P n ps i := by
  rw [treeVal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [col, tailCol, Finset.range_eq_Ico]

/-! ## Splitting off one step of a loop -/

theorem Ico_eq_insert {a b : ℕ} (h : a < b) :
    Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
  ext k
  simp only [Finset.mem_Ico, Finset.mem_insert]
  omega

theorem tailCol_succ (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) (i ja : ℕ)
    (h : ja < msgCount P) :
    tailCol P n ps i ja
      = max (treeVal P n (ps ++ [(msgOf i, msgOf ja)])) (tailCol P n ps i (ja + 1)) := by
  classical
  rw [tailCol, tailCol, Ico_eq_insert h, Finset.sup_insert]

theorem tailCol_last (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) (i ja : ℕ)
    (h : msgCount P ≤ ja + 1) (h' : ja < msgCount P) :
    tailCol P n ps i ja = treeVal P n (ps ++ [(msgOf i, msgOf ja)]) := by
  rw [tailCol_succ P n ps i ja h', tailCol, Finset.Ico_eq_empty (by omega)]
  simp

theorem tailCol_empty (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) (i ja : ℕ)
    (h : msgCount P ≤ ja) : tailCol P n ps i ja = 0 := by
  rw [tailCol, Finset.Ico_eq_empty (by omega)]
  simp

theorem sum_col_split (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) (i : ℕ)
    (h : i < msgCount P) :
    ∑ k ∈ Finset.Ico i (msgCount P), col P n ps k
      = col P n ps i + ∑ k ∈ Finset.Ico (i + 1) (msgCount P), col P n ps k := by
  classical
  rw [Ico_eq_insert h, Finset.sum_insert (by simp)]

theorem sum_col_empty (P : Params) (n : ℕ) (ps : List (List Bool × List Bool)) (i : ℕ)
    (h : msgCount P ≤ i) : ∑ k ∈ Finset.Ico i (msgCount P), col P n ps k = 0 := by
  rw [Finset.Ico_eq_empty (by omega)]
  simp

open Classical in
theorem leaf_split (P : Params) (ps : List (List Bool × List Bool)) (k : ℕ) (h : k < 2 ^ P.t) :
    ((Finset.Ico k (2 ^ P.t)).filter fun l => P.ok ps (coinOf P l)).card
      = (if P.ok ps (coinOf P k) then 1 else 0)
        + ((Finset.Ico (k + 1) (2 ^ P.t)).filter fun l => P.ok ps (coinOf P l)).card := by
  classical
  rw [Ico_eq_insert h, Finset.filter_insert]
  by_cases hk : P.ok ps (coinOf P k)
  · rw [ite_eq_left hk, ite_eq_left hk, Finset.card_insert_of_notMem (by simp)]
    omega
  · rw [ite_eq_right hk, ite_eq_right hk]
    omega

open Classical in
theorem leaf_empty (P : Params) (ps : List (List Bool × List Bool)) (k : ℕ) (h : 2 ^ P.t ≤ k) :
    ((Finset.Ico k (2 ^ P.t)).filter fun l => P.ok ps (coinOf P l)).card = 0 := by
  rw [Finset.Ico_eq_empty (by omega)]
  simp

/-! ## What a frame is still worth -/

theorem msgOf_strIdx (w : List Bool) : msgOf (strIdx w) = w :=
  strIdx_injective (by rw [msgOf, strIdx_iterate])

@[simp] theorem strIdx_msgOf (i : ℕ) : strIdx (msgOf i) = i := strIdx_iterate i

theorem coinOf_binValLE (P : Params) (s : List Bool) (hs : s.length = P.t) :
    coinOf P (binValLE s) = s := by
  have hlt : binValLE s < 2 ^ P.t := by
    have := binValLE_lt s
    rwa [hs] at this
  rw [coinOf, zeroCoin, ← bitsOfLenLE_zero, bumpBits_iterate P.t _ hlt, ← hs,
    bitsOfLenLE_binValLE]

theorem msgCount_pos (P : Params) : 0 < msgCount P := by
  have : 1 ≤ 2 ^ (P.m + 1) := Nat.one_le_two_pow
  have h2 : 2 ^ 1 ≤ 2 ^ (P.m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [msgCount]
  omega

/-- **The value a frame will still contribute**: what it has banked, plus what its loops have
left to do. -/
def frameVal (P : Params) (ps : List (List Bool × List Bool)) (f : Frm) : ℕ :=
  match f.lvl with
  | [] =>
      binValLE f.sum
        + ((Finset.Ico (binValLE f.a) (2 ^ P.t)).filter fun k => P.ok ps (coinOf P k)).card
  | _ :: t' =>
      binValLE f.sum
        + max (binValLE f.best) (tailCol P t'.length ps (strIdx f.v) (strIdx f.a))
        + ∑ k ∈ Finset.Ico (strIdx f.v + 1) (msgCount P), col P t'.length ps k

theorem frameVal_leaf (P : Params) (ps : List (List Bool × List Bool)) {f : Frm}
    (h : f.lvl = []) :
    frameVal P ps f
      = binValLE f.sum
        + ((Finset.Ico (binValLE f.a) (2 ^ P.t)).filter fun k => P.ok ps (coinOf P k)).card := by
  rw [frameVal, h]

theorem frameVal_branch (P : Params) (ps : List (List Bool × List Bool)) {f : Frm}
    {b : Bool} {t' : List Bool} (h : f.lvl = b :: t') :
    frameVal P ps f
      = binValLE f.sum
        + max (binValLE f.best) (tailCol P t'.length ps (strIdx f.v) (strIdx f.a))
        + ∑ k ∈ Finset.Ico (strIdx f.v + 1) (msgCount P), col P t'.length ps k := by
  rw [frameVal, h]

/-- **A fresh frame is worth its whole subtree.** -/
theorem frameVal_fresh (P : Params) (ps : List (List Bool × List Bool)) (body lvl : List Bool) :
    frameVal P ps (freshFrm P body lvl) = treeVal P lvl.length ps := by
  rcases lvl with _ | ⟨b, t'⟩
  · have hf : freshFrm P body ([] : List Bool)
        = ⟨[], [], zeroCoin P, zeroCount P, zeroCount P, body⟩ := by simp [freshFrm]
    rw [hf, frameVal_leaf P ps rfl]
    simp only [List.length_nil]
    rw [treeVal_zero]
    simp only [zeroCount, zeroCoin, binValLE_replicate_false]
    rw [Finset.range_eq_Ico]
    simp
  · have hf : freshFrm P body (b :: t')
        = ⟨b :: t', [], [], zeroCount P, zeroCount P, body⟩ := by simp [freshFrm]
    rw [hf, frameVal_branch P ps (b := b) (t' := t') rfl]
    simp only [List.length_cons]
    rw [treeVal_succ]
    simp only [zeroCount, binValLE_replicate_false, strIdx_nil, Nat.zero_add, Nat.zero_max]
    rw [show tailCol P t'.length ps 0 0 = col P t'.length ps 0 from rfl,
      Finset.range_eq_Ico, sum_col_split P t'.length ps 0 (msgCount_pos P)]

/-! ## Runs -/

/-- The done flag is down at every point of the first `T` steps from `s`. -/
def DoneDown (P : Params) (s : Sst) (T : ℕ) : Prop :=
  ∀ j ≤ T, ((step P)^[j] s).done = false

theorem doneDown_zero (P : Params) {s : Sst} (h : s.done = false) : DoneDown P s 0 := by
  intro j hj
  have : j = 0 := Nat.le_zero.mp hj
  subst this
  simpa using h

theorem doneDown_add (P : Params) {s : Sst} {T₁ T₂ : ℕ} (h₁ : DoneDown P s T₁)
    (h₂ : DoneDown P ((step P)^[T₁] s) T₂) : DoneDown P s (T₁ + T₂) := by
  intro j hj
  by_cases hle : j ≤ T₁
  · exact h₁ j hle
  · have hj' : j = (j - T₁) + T₁ := by omega
    rw [hj', Function.iterate_add_apply]
    exact h₂ _ (by omega)

theorem doneDown_succ (P : Params) {s : Sst} {T : ℕ} (h : DoneDown P s T)
    (h' : ((step P)^[T + 1] s).done = false) : DoneDown P s (T + 1) := by
  intro j hj
  rcases Nat.lt_or_ge j (T + 1) with hlt | hge
  · exact h j (by omega)
  · have : j = T + 1 := by omega
    subst this
    exact h'

/-- How many loop iterations a frame still has to make. -/
def mu (P : Params) (f : Frm) : ℕ :=
  match f.lvl with
  | [] => 2 ^ P.t - binValLE f.a
  | _ :: _ => (msgCount P - 1 - strIdx f.v) * msgCount P + (msgCount P - strIdx f.a)

/-- The steps a frame at level `n` costs. -/
def runBound (P : Params) : ℕ → ℕ
  | 0 => 2 ^ P.t
  | n + 1 => msgCount P * msgCount P * (runBound P n + 2)

theorem runBound_pos (P : Params) : ∀ n, 0 < runBound P n := by
  intro n
  induction n with
  | zero => rw [runBound]; exact Nat.two_pow_pos _
  | succ n ih =>
      rw [runBound]
      exact Nat.mul_pos (Nat.mul_pos (msgCount_pos P) (msgCount_pos P)) (by omega)

/-- **The walk takes at most two to a polynomial steps.** -/
theorem runBound_le (P : Params) :
    ∀ n, runBound P n + 2 ≤ 2 ^ (P.t + 2 + (2 * P.m + 3) * n) := by
  intro n
  induction n with
  | zero =>
      have h1 : (1 : ℕ) ≤ 2 ^ P.t := Nat.one_le_two_pow
      have h2 : 2 ^ (P.t + 2) = 4 * 2 ^ P.t := by
        rw [show P.t + 2 = 2 + P.t from by omega, pow_add]
        ring
      rw [runBound]
      simp only [Nat.mul_zero, Nat.add_zero]
      omega
  | succ n ih =>
      have hM : msgCount P ≤ 2 ^ (P.m + 1) := by
        rw [msgCount]
        exact Nat.sub_le _ _
      have hMM : msgCount P * msgCount P + 1 ≤ 2 ^ (2 * P.m + 3) := by
        have h1 : msgCount P * msgCount P ≤ 2 ^ (P.m + 1) * 2 ^ (P.m + 1) :=
          Nat.mul_le_mul hM hM
        have h2 : 2 ^ (P.m + 1) * 2 ^ (P.m + 1) = 2 ^ (2 * P.m + 2) := by
          rw [← pow_add]
          ring_nf
        have h3 : 2 ^ (2 * P.m + 3) = 2 * 2 ^ (2 * P.m + 2) := by
          rw [show 2 * P.m + 3 = 1 + (2 * P.m + 2) from by omega, pow_add]
          ring
        have h4 : (1 : ℕ) ≤ 2 ^ (2 * P.m + 2) := Nat.one_le_two_pow
        omega
      have hc : 2 ≤ runBound P n + 2 := by omega
      have hstep : runBound P (n + 1) + 2
          ≤ (msgCount P * msgCount P + 1) * (runBound P n + 2) := by
        rw [runBound]
        calc msgCount P * msgCount P * (runBound P n + 2) + 2
            ≤ msgCount P * msgCount P * (runBound P n + 2) + (runBound P n + 2) := by omega
          _ = (msgCount P * msgCount P + 1) * (runBound P n + 2) := by ring
      calc runBound P (n + 1) + 2
          ≤ (msgCount P * msgCount P + 1) * (runBound P n + 2) := hstep
        _ ≤ 2 ^ (2 * P.m + 3) * 2 ^ (P.t + 2 + (2 * P.m + 3) * n) := Nat.mul_le_mul hMM ih
        _ = 2 ^ (P.t + 2 + (2 * P.m + 3) * (n + 1)) := by
            rw [← pow_add]
            ring_nf

/-- A frame is well formed when its registers have the right widths, its counters are inside the
enumeration, and what it still owes fits in the coin space. -/
structure FrmOk (P : Params) (ps : List (List Bool × List Bool)) (f : Frm) : Prop where
  /-- The running sum has the count width. -/
  sumLen : f.sum.length = P.t + 1
  /-- So does the running maximum. -/
  bestLen : f.best.length = P.t + 1
  /-- A leaf's coin counter has the coin width. -/
  coinLen : f.lvl = [] → f.a.length = P.t
  /-- A branch's verifier counter is inside the enumeration. -/
  vIdx : f.lvl ≠ [] → strIdx f.v < msgCount P
  /-- So is its prover counter. -/
  aIdx : f.lvl ≠ [] → strIdx f.a < msgCount P
  /-- What the frame still owes fits in the coin space. -/
  bnd : frameVal P ps f ≤ 2 ^ P.t

/-- The frame `f`, pushed on `fs`, is popped again carrying its value after exactly `T` steps,
and the done flag stays down for the whole of that run. -/
def RunsTo (P : Params) (f : Frm) (fs : List Frm) (a : Bool) (T : ℕ) : Prop :=
  0 < T ∧ DoneDown P ⟨false, a, none, f :: fs⟩ T ∧
    ∃ w : List Bool, w.length = P.t + 1 ∧ binValLE w = frameVal P (roundsOf fs) f ∧
      (step P)^[T] ⟨false, a, none, f :: fs⟩ = ⟨false, a, some w, fs⟩

/-- A run that begins by re-entering a frame of the same value. -/
theorem runsTo_prepend (P : Params) {f g : Frm} {fs : List Frm} {a : Bool} {T₀ T₁ : ℕ}
    (hd : DoneDown P ⟨false, a, none, f :: fs⟩ T₀)
    (hs : (step P)^[T₀] ⟨false, a, none, f :: fs⟩ = ⟨false, a, none, g :: fs⟩)
    (hr : RunsTo P g fs a T₁)
    (hval : frameVal P (roundsOf fs) g = frameVal P (roundsOf fs) f) :
    RunsTo P f fs a (T₁ + T₀) := by
  obtain ⟨hpos, hdd, w, hwlen, hwval, hend⟩ := hr
  refine ⟨by omega, ?_, w, hwlen, by rw [hwval, hval], ?_⟩
  · rw [Nat.add_comm]
    exact doneDown_add P hd (by rw [hs]; exact hdd)
  · rw [Function.iterate_add_apply, hs, hend]

theorem mu_leaf (P : Params) {f : Frm} (h : f.lvl = []) :
    mu P f = 2 ^ P.t - binValLE f.a := by rw [mu, h]

theorem mu_branch (P : Params) {f : Frm} {b : Bool} {t' : List Bool} (h : f.lvl = b :: t') :
    mu P f
      = (msgCount P - 1 - strIdx f.v) * msgCount P + (msgCount P - strIdx f.a) := by rw [mu, h]

/-- **A leaf runs its coin loop and pops with the tally.** -/
theorem run_leaf (P : Params) :
    ∀ (M : ℕ) (f : Frm), mu P f ≤ M → f.lvl = [] → ∀ (fs : List Frm),
      FrmOk P (roundsOf fs) f → ∀ a : Bool, ∃ T ≤ mu P f, RunsTo P f fs a T := by
  intro M
  induction M with
  | zero =>
      intro f hmu hl fs hok _
      exfalso
      have hlt : binValLE f.a < 2 ^ P.t := by
        have := binValLE_lt f.a
        rwa [hok.coinLen hl] at this
      rw [mu_leaf P hl] at hmu
      omega
  | succ M ih =>
    intro f hmu hl fs hok a
    have hlen := hok.coinLen hl
    have hlt : binValLE f.a < 2 ^ P.t := by
      have := binValLE_lt f.a
      rwa [hlen] at this
    have hcoin : coinOf P (binValLE f.a) = f.a := coinOf_binValLE P f.a hlen
    have hfv := frameVal_leaf P (roundsOf fs) hl
    have hsplit := leaf_split P (roundsOf fs) (binValLE f.a) hlt
    rw [hcoin] at hsplit
    have hbnd := hok.bnd
    -- bumping the tally never carries
    have hsum : binValLE (if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum)
        = binValLE f.sum + (if P.ok (roundsOf fs) f.a then 1 else 0) := by
      by_cases hokb : P.ok (roundsOf fs) f.a
      · rw [ite_eq_left hokb, ite_eq_left hokb]
        have h1 : binValLE f.sum + 1 ≤ 2 ^ P.t := by
          rw [hfv] at hbnd
          rw [hsplit, ite_eq_left hokb] at hbnd
          omega
        have h2 : binValLE f.sum + 1 < 2 ^ f.sum.length := by
          rw [hok.sumLen, pow_succ]
          have : 0 < 2 ^ P.t := Nat.two_pow_pos _
          omega
        rw [binValLE_bumpBits_of_not_over _ (bumpOver_eq_false_of_lt h2)]
      · rw [ite_eq_right hokb, ite_eq_right hokb]
        omega
    have hsumLen : (if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum).length
        = P.t + 1 := by
      by_cases hokb : P.ok (roundsOf fs) f.a
      · rw [ite_eq_left hokb, bumpBits_length, hok.sumLen]
      · rw [ite_eq_right hokb, hok.sumLen]
    by_cases hov : bumpOver f.a = true
    · -- the last coin string: pop with the tally
      have hka : binValLE f.a = 2 ^ P.t - 1 := by
        have := (bumpOver_iff f.a).mp hov
        rwa [hlen] at this
      have hstep := step_leaf_last P a f fs hl hov
      refine ⟨1, by rw [mu_leaf P hl]; omega, Nat.one_pos, ?_, _, hsumLen, ?_, ?_⟩
      · exact doneDown_succ P (doneDown_zero P rfl) (by rw [Function.iterate_one, hstep])
      · rw [hfv, hsplit, hsum, leaf_empty P _ _ (by omega)]
        omega
      · rw [Function.iterate_one, hstep]
    · -- move on to the next coin string
      have hovf : bumpOver f.a = false := by simpa using hov
      have hstep := step_leaf_next P a f fs hl hovf
      set f' : Frm :=
        { f with
          a := bumpBits f.a,
          sum := if P.ok (roundsOf fs) f.a then bumpBits f.sum else f.sum } with hf'
      have hl' : f'.lvl = [] := hl
      have ha' : binValLE f'.a = binValLE f.a + 1 := by
        rw [hf']
        exact binValLE_bumpBits_of_not_over _ hovf
      have hval : frameVal P (roundsOf fs) f' = frameVal P (roundsOf fs) f := by
        rw [frameVal_leaf P (roundsOf fs) hl', hfv, hsplit, ha', hsum]
        omega
      have hok' : FrmOk P (roundsOf fs) f' :=
        { sumLen := by rw [hf']; exact hsumLen
          bestLen := by rw [hf']; exact hok.bestLen
          coinLen := fun _ => by
            show (bumpBits f.a).length = P.t
            rw [bumpBits_length]
            exact hlen
          vIdx := fun hc => absurd hl' hc
          aIdx := fun hc => absurd hl' hc
          bnd := by rw [hval]; exact hbnd }
      have hmu' : mu P f' = mu P f - 1 := by
        rw [mu_leaf P hl', mu_leaf P hl, ha']
        omega
      have hmupos : 1 ≤ mu P f := by
        rw [mu_leaf P hl]
        omega
      obtain ⟨T', hT', hr'⟩ := ih f' (by omega) hl' fs hok' a
      refine ⟨T' + 1, by omega, ?_⟩
      refine runsTo_prepend P ?_ ?_ hr' hval
      · exact doneDown_succ P (doneDown_zero P rfl) (by rw [Function.iterate_one, hstep])
      · rw [Function.iterate_one, hstep]

/-- Pushing a subtree, running it, and processing the value it returns. -/
theorem child_phase (P : Params) {f : Frm} {fs : List Frm} {a : Bool} {Tc : ℕ}
    {w : List Bool} {s : Sst} (hne : f.lvl ≠ [])
    (hdd : DoneDown P ⟨false, a, none, childFrm P f :: f :: fs⟩ Tc)
    (hend : (step P)^[Tc] ⟨false, a, none, childFrm P f :: f :: fs⟩
        = ⟨false, a, some w, f :: fs⟩)
    (hstep : step P ⟨false, a, some w, f :: fs⟩ = s)
    (hsdone : s.done = false) :
    DoneDown P ⟨false, a, none, f :: fs⟩ (Tc + 1 + 1) ∧
      (step P)^[Tc + 1 + 1] ⟨false, a, none, f :: fs⟩ = s := by
  have hpush : step P ⟨false, a, none, f :: fs⟩
      = ⟨false, a, none, childFrm P f :: f :: fs⟩ := step_push P a f fs hne
  have h1 : (step P)^[Tc + 1] ⟨false, a, none, f :: fs⟩ = ⟨false, a, some w, f :: fs⟩ := by
    rw [Function.iterate_succ_apply, hpush, hend]
  have h2 : (step P)^[Tc + 1 + 1] ⟨false, a, none, f :: fs⟩ = s := by
    rw [Function.iterate_succ_apply', h1, hstep]
  refine ⟨?_, h2⟩
  have d1 : DoneDown P ⟨false, a, none, f :: fs⟩ 1 :=
    doneDown_succ P (doneDown_zero P rfl) (by rw [Function.iterate_one, hpush])
  have d2 : DoneDown P ⟨false, a, none, f :: fs⟩ (Tc + 1) := by
    have := doneDown_add P d1 (by rw [Function.iterate_one, hpush]; exact hdd)
    rwa [Nat.add_comm 1 Tc] at this
  exact doneDown_succ P d2 (by rw [h2]; exact hsdone)

/-- **A branch runs both of its loops and pops with the sum.** -/
theorem run_branch (P : Params) (hval : ∀ (n : ℕ) (ps : List (List Bool × List Bool)),
      treeVal P n ps ≤ 2 ^ P.t) (n : ℕ)
    (ih : ∀ g : Frm, g.lvl.length = n → ∀ gs : List Frm, FrmOk P (roundsOf gs) g →
      ∀ b : Bool, ∃ T ≤ runBound P n, RunsTo P g gs b T) :
    ∀ (M : ℕ) (f : Frm), mu P f ≤ M → f.lvl.length = n + 1 → ∀ fs : List Frm,
      FrmOk P (roundsOf fs) f → ∀ a : Bool,
        ∃ T ≤ mu P f * (runBound P n + 2), RunsTo P f fs a T := by
  intro M
  induction M with
  | zero =>
      intro f hmu hlen fs hok _
      exfalso
      obtain ⟨b, t', hlv⟩ : ∃ b t', f.lvl = b :: t' := by
        cases hc : f.lvl with
        | nil => rw [hc] at hlen; simp at hlen
        | cons b t' => exact ⟨b, t', rfl⟩
      have hne : f.lvl ≠ [] := by rw [hlv]; simp
      have hja := hok.aIdx hne
      rw [mu_branch P hlv] at hmu
      omega
  | succ M inner =>
    intro f hmu hlen fs hok a
    obtain ⟨b, t', hlv⟩ : ∃ b t', f.lvl = b :: t' := by
      cases hc : f.lvl with
      | nil => rw [hc] at hlen; simp at hlen
      | cons b t' => exact ⟨b, t', rfl⟩
    have hne : f.lvl ≠ [] := by rw [hlv]; simp
    have htn : t'.length = n := by rw [hlv] at hlen; simpa using hlen
    have hiv := hok.vIdx hne
    have hja := hok.aIdx hne
    set ps := roundsOf fs with hps
    -- the child
    have hchildlen : (childFrm P f).lvl.length = n := by
      rw [childFrm_lvl, List.length_drop, hlen]
      omega
    have hrounds : roundsOf (f :: fs) = ps ++ [(f.v, f.a)] := roundsOf_cons f fs
    have hchildok : FrmOk P (roundsOf (f :: fs)) (childFrm P f) :=
      { sumLen := by show (zeroCount P).length = P.t + 1; rw [zeroCount, List.length_replicate]
        bestLen := by show (zeroCount P).length = P.t + 1; rw [zeroCount, List.length_replicate]
        coinLen := fun hc => by
          have hc' : f.lvl.drop 1 = [] := hc
          show (if f.lvl.drop 1 = [] then zeroCoin P else []).length = P.t
          rw [ite_eq_left hc', zeroCoin, List.length_replicate]
        vIdx := fun _ => by
          show strIdx [] < msgCount P
          rw [strIdx_nil]
          exact msgCount_pos P
        aIdx := fun hc => by
          have hc' : ¬ (f.lvl.drop 1 = []) := hc
          show strIdx (if f.lvl.drop 1 = [] then zeroCoin P else []) < msgCount P
          rw [ite_eq_right hc', strIdx_nil]
          exact msgCount_pos P
        bnd := by
          rw [childFrm, frameVal_fresh]
          exact hval _ _ }
    obtain ⟨Tc, hTc, hcpos, hcdd, w, hwlen, hwval, hcend⟩ :=
      ih (childFrm P f) hchildlen (f :: fs)
        hchildok a
    rw [childFrm, frameVal_fresh] at hwval
    have hdroplen : (f.lvl.drop 1).length = n := by
      rw [List.length_drop, hlen]
      omega
    have hchildval : binValLE w
        = treeVal P n (ps ++ [(msgOf (strIdx f.v), msgOf (strIdx f.a))]) := by
      rw [hwval, hrounds, hdroplen, msgOf_strIdx, msgOf_strIdx]
    -- the running value the frame owes
    have hfv := frameVal_branch P ps (f := f) hlv
    rw [htn] at hfv
    have hmaxlen : (maxBits f.best w).length = P.t + 1 := by
      rw [maxBits_length _ _ (by rw [hwlen, hok.bestLen]), hok.bestLen]
    have hmaxval : binValLE (maxBits f.best w) = max (binValLE f.best) (binValLE w) :=
      binValLE_maxBits _ _ (by rw [hwlen, hok.bestLen])
    have hcond : ∀ u : List Bool, (nextStr u).length ≤ P.m ↔ strIdx u + 1 < msgCount P := by
      intro u
      rw [msgCount, ← strIdx_lt_iff P.m (nextStr u), strIdx_nextStr]
    by_cases hA : strIdx f.a + 1 < msgCount P
    · -- move on to the next reply
      have hstep := step_ret_more_a P a f fs w ((hcond f.a).mpr hA)
      set f' : Frm := { f with a := nextStr f.a, best := maxBits f.best w } with hf'
      have hlv' : f'.lvl = b :: t' := hlv
      have ha' : strIdx f'.a = strIdx f.a + 1 := strIdx_nextStr f.a
      have hval' : frameVal P ps f' = frameVal P ps f := by
        rw [frameVal_branch P ps (f := f') hlv', htn, hfv, ha']
        show binValLE f.sum + max (binValLE (maxBits f.best w)) _ + _ = _
        rw [hmaxval, tailCol_succ P n ps (strIdx f.v) (strIdx f.a) hja, ← hchildval, max_assoc]
      have hok' : FrmOk P ps f' :=
        { sumLen := hok.sumLen
          bestLen := hmaxlen
          coinLen := fun hc => absurd (hlv'.symm.trans hc) (by simp)
          vIdx := fun _ => hiv
          aIdx := fun _ => by rw [ha']; omega
          bnd := by rw [hval']; exact hok.bnd }
      have hmu' : mu P f' = mu P f - 1 := by
        rw [mu_branch P hlv', mu_branch P hlv]
        show (msgCount P - 1 - strIdx f.v) * msgCount P + (msgCount P - strIdx (nextStr f.a)) = _
        rw [strIdx_nextStr]
        omega
      have hmupos : 1 ≤ mu P f := by
        rw [mu_branch P hlv]
        omega
      obtain ⟨T', hT', hr'⟩ := inner f' (by omega) hlen fs hok' a
      have hexp : mu P f * (runBound P n + 2)
          = mu P f' * (runBound P n + 2) + (runBound P n + 2) := by
        rw [hmu']
        obtain ⟨c, hc⟩ : ∃ c, mu P f = c + 1 := ⟨mu P f - 1, by omega⟩
        rw [hc, Nat.add_sub_cancel]
        ring
      obtain ⟨hd, hs⟩ := child_phase P hne hcdd hcend hstep rfl
      exact ⟨T' + (Tc + 1 + 1), by omega, runsTo_prepend P hd hs hr' hval'⟩
    · have hja1 : msgCount P - strIdx f.a = 1 := by omega
      have htail : tailCol P n ps (strIdx f.v) (strIdx f.a)
          = treeVal P n (ps ++ [(msgOf (strIdx f.v), msgOf (strIdx f.a))]) :=
        tailCol_last P n ps _ _ (by omega) hja
      have hbnd2 : binValLE f.sum + max (binValLE f.best) (binValLE w) ≤ 2 ^ P.t := by
        have := hok.bnd
        rw [hfv, htail, ← hchildval] at this
        omega
      have hsumlen : (maxBits f.best w).length = f.sum.length := by
        rw [hmaxlen, hok.sumLen]
      have hsumval : binValLE (addBits f.sum (maxBits f.best w))
          = binValLE f.sum + max (binValLE f.best) (binValLE w) := by
        rw [binValLE_addBits _ _ hsumlen ?_, hmaxval]
        rw [hmaxval, hok.sumLen, pow_succ]
        have hp : 0 < 2 ^ P.t := Nat.two_pow_pos _
        omega
      have hsumlen' : (addBits f.sum (maxBits f.best w)).length = P.t + 1 := by
        rw [addBits_length _ _ hsumlen, hok.sumLen]
      by_cases hB : strIdx f.v + 1 < msgCount P
      · -- move on to the next verifier message
        have hstep := step_ret_more_v P a f fs w
          (fun hc => hA ((hcond f.a).mp hc)) ((hcond f.v).mpr hB)
        set f'' : Frm :=
          { f with
            v := nextStr f.v,
            a := [],
            sum := addBits f.sum (maxBits f.best w),
            best := zeroCount P } with hf''
        have hlv'' : f''.lvl = b :: t' := hlv
        have hval'' : frameVal P ps f'' = frameVal P ps f := by
          rw [frameVal_branch P ps (f := f'') hlv'', htn, hfv, htail, ← hchildval]
          show binValLE (addBits f.sum (maxBits f.best w))
              + max (binValLE (zeroCount P)) (tailCol P n ps (strIdx (nextStr f.v))
                (strIdx ([] : List Bool)))
              + ∑ k ∈ Finset.Ico (strIdx (nextStr f.v) + 1) (msgCount P), col P n ps k = _
          rw [hsumval, zeroCount, binValLE_replicate_false, strIdx_nextStr, strIdx_nil,
            Nat.zero_max, show tailCol P n ps (strIdx f.v + 1) 0 = col P n ps (strIdx f.v + 1)
              from rfl, sum_col_split P n ps (strIdx f.v + 1) hB]
          omega
        have hok'' : FrmOk P ps f'' :=
          { sumLen := hsumlen'
            bestLen := by
              show (zeroCount P).length = P.t + 1
              rw [zeroCount, List.length_replicate]
            coinLen := fun hc => absurd (hlv''.symm.trans hc) (by simp)
            vIdx := fun _ => by
              show strIdx (nextStr f.v) < msgCount P
              rw [strIdx_nextStr]
              omega
            aIdx := fun _ => by
              show strIdx ([] : List Bool) < msgCount P
              rw [strIdx_nil]
              exact msgCount_pos P
            bnd := by rw [hval'']; exact hok.bnd }
        have hmu'' : mu P f'' = mu P f - 1 := by
          rw [mu_branch P hlv'', mu_branch P hlv]
          show (msgCount P - 1 - strIdx (nextStr f.v)) * msgCount P
              + (msgCount P - strIdx ([] : List Bool)) = _
          rw [strIdx_nextStr, strIdx_nil, hja1]
          have hd : msgCount P - 1 - (strIdx f.v + 1) + 1 = msgCount P - 1 - strIdx f.v := by omega
          calc (msgCount P - 1 - (strIdx f.v + 1)) * msgCount P + (msgCount P - 0)
              = ((msgCount P - 1 - (strIdx f.v + 1)) + 1) * msgCount P := by rw [Nat.sub_zero]; ring
            _ = (msgCount P - 1 - strIdx f.v) * msgCount P := by rw [hd]
            _ = (msgCount P - 1 - strIdx f.v) * msgCount P + 1 - 1 := by omega
        have hmupos : 1 ≤ mu P f := by
          rw [mu_branch P hlv]
          omega
        obtain ⟨T', hT', hr'⟩ := inner f'' (by omega) hlen fs hok'' a
        have hexp : mu P f * (runBound P n + 2)
            = mu P f'' * (runBound P n + 2) + (runBound P n + 2) := by
          rw [hmu'']
          obtain ⟨c, hc⟩ : ∃ c, mu P f = c + 1 := ⟨mu P f - 1, by omega⟩
          rw [hc, Nat.add_sub_cancel]
          ring
        obtain ⟨hd, hs⟩ := child_phase P hne hcdd hcend hstep rfl
        exact ⟨T' + (Tc + 1 + 1), by omega, runsTo_prepend P hd hs hr' hval''⟩
      · -- both loops are done: pop with the sum
        have hstep := step_ret_pop P a f fs w
          (fun hc => hA ((hcond f.a).mp hc)) (fun hc => hB ((hcond f.v).mp hc))
        have hfinal : binValLE (addBits f.sum (maxBits f.best w)) = frameVal P ps f := by
          rw [hfv, htail, ← hchildval, hsumval, sum_col_empty P n ps _ (by omega)]
          omega
        have hmu1 : mu P f = 1 := by
          rw [mu_branch P hlv, hja1]
          have : msgCount P - 1 - strIdx f.v = 0 := by omega
          rw [this]
          omega
        obtain ⟨hd, hs⟩ := child_phase P hne hcdd hcend hstep rfl
        refine ⟨Tc + 1 + 1, ?_, by omega, hd, addBits f.sum (maxBits f.best w),
          hsumlen', hfinal, hs⟩
        rw [hmu1]
        omega

/-- A fresh frame is well formed. -/
theorem frmOk_fresh (P : Params) (hval : ∀ (n : ℕ) (ps : List (List Bool × List Bool)),
      treeVal P n ps ≤ 2 ^ P.t) (ps : List (List Bool × List Bool)) (body lvl : List Bool) :
    FrmOk P ps (freshFrm P body lvl) :=
  { sumLen := by show (zeroCount P).length = P.t + 1; rw [zeroCount, List.length_replicate]
    bestLen := by show (zeroCount P).length = P.t + 1; rw [zeroCount, List.length_replicate]
    coinLen := fun hc => by
      have hc' : lvl = [] := hc
      show (if lvl = [] then zeroCoin P else []).length = P.t
      rw [ite_eq_left hc', zeroCoin, List.length_replicate]
    vIdx := fun _ => by
      show strIdx [] < msgCount P
      rw [strIdx_nil]
      exact msgCount_pos P
    aIdx := fun hc => by
      have hc' : ¬ (lvl = []) := hc
      show strIdx (if lvl = [] then zeroCoin P else []) < msgCount P
      rw [ite_eq_right hc', strIdx_nil]
      exact msgCount_pos P
    bnd := by rw [frameVal_fresh P ps body lvl]; exact hval _ _ }

/-- **Every pushed frame comes back**, carrying its value, within `runBound` steps. -/
theorem run_frame (P : Params) (hval : ∀ (n : ℕ) (ps : List (List Bool × List Bool)),
      treeVal P n ps ≤ 2 ^ P.t) :
    ∀ (n : ℕ) (f : Frm), f.lvl.length = n → ∀ fs : List Frm, FrmOk P (roundsOf fs) f →
      ∀ a : Bool, ∃ T ≤ runBound P n, RunsTo P f fs a T := by
  intro n
  induction n with
  | zero =>
      intro f hlen fs hok a
      have hl : f.lvl = [] := List.length_eq_zero_iff.mp hlen
      obtain ⟨T, hT, hr⟩ := run_leaf P (mu P f) f le_rfl hl fs hok a
      refine ⟨T, ?_, hr⟩
      rw [mu_leaf P hl] at hT
      rw [runBound]
      exact le_trans hT (Nat.sub_le _ _)
  | succ n ih =>
      intro f hlen fs hok a
      obtain ⟨T, hT, hr⟩ := run_branch P hval n ih (mu P f) f le_rfl hlen fs hok a
      refine ⟨T, ?_, hr⟩
      obtain ⟨b, t', hlv⟩ : ∃ b t', f.lvl = b :: t' := by
        cases hc : f.lvl with
        | nil => rw [hc] at hlen; simp at hlen
        | cons b t' => exact ⟨b, t', rfl⟩
      have hne : f.lvl ≠ [] := by rw [hlv]; simp
      have hmu : mu P f ≤ msgCount P * msgCount P := by
        rw [mu_branch P hlv]
        have h1 : (msgCount P - 1 - strIdx f.v) * msgCount P ≤ (msgCount P - 1) * msgCount P :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (msgCount P - 1) * msgCount P + msgCount P = msgCount P * msgCount P := by
          have hp := msgCount_pos P
          obtain ⟨c, hc⟩ : ∃ c, msgCount P = c + 1 := ⟨msgCount P - 1, by omega⟩
          rw [hc, Nat.add_sub_cancel]
          ring
        omega
      rw [runBound]
      exact le_trans hT (Nat.mul_le_mul_right _ hmu)

/-- **The whole walk.** From a single fresh frame the machine keeps its flag down, raises it on
the next step, and one step later the flag *is* the verdict. -/
theorem run_top (P : Params) (hval : ∀ (n : ℕ) (ps : List (List Bool × List Bool)),
      treeVal P n ps ≤ 2 ^ P.t) (lvl : List Bool) :
    ∃ (T : ℕ) (w : List Bool), T ≤ runBound P lvl.length ∧ w.length = P.t + 1 ∧
      binValLE w = treeVal P lvl.length [] ∧
      (∀ j ≤ T, ((step P)^[j] ⟨false, false, none, [freshFrm P [] lvl]⟩).done = false) ∧
      (step P)^[T + 1] ⟨false, false, none, [freshFrm P [] lvl]⟩
        = ⟨true, cmpBit P w, some w, []⟩ ∧
      (step P)^[T + 2] ⟨false, false, none, [freshFrm P [] lvl]⟩
        = ⟨cmpBit P w, cmpBit P w, some w, []⟩ := by
  obtain ⟨T, hT, hpos, hdd, w, hwlen, hwval, hend⟩ :=
    run_frame P hval lvl.length (freshFrm P [] lvl) rfl [] (frmOk_fresh P hval _ [] lvl) false
  rw [roundsOf_nil, frameVal_fresh P [] [] lvl] at hwval
  have h1 : (step P)^[T + 1] ⟨false, false, none, [freshFrm P [] lvl]⟩
      = ⟨true, cmpBit P w, some w, []⟩ := by
    rw [Function.iterate_succ_apply', hend, step_of_empty]
    rfl
  refine ⟨T, w, hT, hwlen, hwval, hdd, h1, ?_⟩
  rw [show T + 2 = T + 1 + 1 from rfl, Function.iterate_succ_apply', h1, step_of_done]

end IPM

end Complexity

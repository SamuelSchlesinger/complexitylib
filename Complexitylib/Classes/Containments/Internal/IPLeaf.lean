/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.IPWalk
public import Complexitylib.Classes.Containments.Internal.PVerdict

/-!
# The leaf test

⚠️ Unreviewed by Bolton

At a leaf the walk asks one question of each coin string: *would the verifier have sent every
message the transcript records, and does it accept?* The first half is
`Complexity.Protocol.replay`, which walks the rounds in play order carrying the encoding body
with it — the wrong direction for a stack, whose top frame is the *last* round.

Carrying each frame's body inside the frame removes the problem: the check a round contributes
depends only on that round's verifier message and its own body, so the conjunction may be taken in
any order. That is what `Complexity.stkCheckB` does, and it is what a scan over the encoded stack
can compute.

## Main definitions

- `Complexity.stkCheckB` — the per-frame form of the consistency test

## Main results

- `Complexity.Protocol.replay_append` — a round appended checks its own message last
- `Complexity.replay_eq_stkCheckB` — the two forms agree
-/

@[expose] public section

namespace Complexity

open Cobham

namespace Protocol

/-- **A round appended checks its own message last**, against the body of everything before it. -/
theorem replay_append (prot : Protocol) (x s : List Bool) :
    ∀ (ps : List (List Bool × List Bool)) (p : List Bool × List Bool) (body : List Bool),
      prot.replay x s (ps ++ [p]) body
        = (prot.replay x s ps body &&
            decide (p.1 = prot.vmsg (pair (pair x s)
              (false :: (body ++ encBodyR ps) ++ [true])))) := by
  intro ps
  induction ps with
  | nil =>
      intro p body
      rw [List.nil_append, replay_cons, replay_nil, encBodyR_nil, List.append_nil]
      simp
  | cons q ps ih =>
      intro p body
      rw [List.cons_append, replay_cons, ih p (body ++ encMsg q.1 ++ encMsg q.2), replay_cons]
      have hbody : body ++ encBodyR (q :: ps)
          = body ++ encMsg q.1 ++ encMsg q.2 ++ encBodyR ps := by
        rw [encBodyR, encBodyR, flatRounds_cons, encBody, encBody]
        simp [List.append_assoc]
      rw [hbody, Bool.and_assoc]

end Protocol

/-- The consistency test as a conjunction over the frames, each checking its own recorded
message against its own body. -/
def stkCheckB (vf : List Bool → List Bool) (x s : List Bool) : List IPM.Frm → Bool
  | [] => true
  | g :: gs =>
      decide (g.v = vf (pair (pair x s) (false :: g.body ++ [true]))) && stkCheckB vf x s gs

@[simp] theorem stkCheckB_nil (vf : List Bool → List Bool) (x s : List Bool) :
    stkCheckB vf x s [] = true := rfl

theorem stkCheckB_cons (vf : List Bool → List Bool) (x s : List Bool) (g : IPM.Frm)
    (gs : List IPM.Frm) :
    stkCheckB vf x s (g :: gs)
      = (decide (g.v = vf (pair (pair x s) (false :: g.body ++ [true]))) &&
          stkCheckB vf x s gs) := rfl

/-- **The two forms of the consistency test agree.** -/
theorem replay_eq_stkCheckB (prot : Protocol) (x s : List Bool) :
    ∀ fs : List IPM.Frm, IPM.BodyOk fs →
      prot.replay x s (IPM.roundsOf fs) [] = stkCheckB prot.vmsg x s fs := by
  intro fs
  induction fs with
  | nil => intro _; rfl
  | cons g gs ih =>
      intro hb
      rw [IPM.roundsOf_cons, prot.replay_append x s (IPM.roundsOf gs) (g.v, g.a) [],
        ih hb.2, stkCheckB_cons, List.nil_append, ← hb.1, Bool.and_comm]

/-! ## Flags as decisions -/

theorem eqFlag_eq_decide (a b : List Bool) : eqFlag a b = [decide (a = b)] := by
  by_cases h : a = b
  · rw [(eqFlag_eq_true_iff a b).mpr h, h]
    simp
  · rcases eqFlag_flag a b with hh | hh
    · exact absurd ((eqFlag_eq_true_iff a b).mp hh) h
    · rw [hh]
      simp [h]

@[simp] theorem andBit_cons (b c : Bool) : andBit [b] [c] = [b && c] := by
  cases b <;> cases c <;> rfl

theorem andBit_length_eq (u v : List Bool) : (andBit u v).length = 1 := by
  rcases andBit_flag u v with h | h <;> rw [h] <;> rfl

/-! ## The scan over the stack -/

/-- The check one frame contributes, on the tape. -/
def chkOneP (vf : List Bool → List Bool) (xu y : List Bool) : List Bool :=
  eqFlag (IPM.fV y) (vf (pair xu (false :: IPM.fBody y ++ [true])))

theorem chkOneP_enc (vf : List Bool → List Bool) (xu : List Bool) (g : IPM.Frm) :
    chkOneP vf xu (IPM.encFrm g)
      = [decide (g.v = vf (pair xu (false :: g.body ++ [true])))] := by
  rw [chkOneP, IPM.fV_enc, IPM.fBody_enc, eqFlag_eq_decide]

/-- One step of the scan: fold the next frame's check into the running flag. -/
def chkStep (vf : List Bool → List Bool) :
    List Bool × List Bool × List Bool → List Bool × List Bool × List Bool :=
  fun s =>
    (s.1,
      selectHead (emptyFlag s.2.2) s.2.1 (andBit s.2.1 (chkOneP vf s.1 (pairFst s.2.2))),
      selectHead (emptyFlag s.2.2) s.2.2 (pairSnd s.2.2))

@[simp] theorem chkStep_nil (vf : List Bool → List Bool) (xu acc : List Bool) :
    chkStep vf (xu, acc, []) = (xu, acc, []) := by
  rw [chkStep]
  simp

theorem chkStep_cons (vf : List Bool → List Bool) (xu acc : List Bool) (g : IPM.Frm)
    (gs : List IPM.Frm) :
    chkStep vf (xu, acc, IPM.encStk (g :: gs))
      = (xu, andBit acc (chkOneP vf xu (IPM.encFrm g)), IPM.encStk gs) := by
  rw [chkStep, IPM.encStk_cons]
  simp only [emptyFlag_pair, selectHead_cons_false, pairFst_pair, pairSnd_pair]

/-- The running flag after folding in a list of frames. -/
def chkFold (vf : List Bool → List Bool) (xu : List Bool) :
    List Bool → List IPM.Frm → List Bool
  | acc, [] => acc
  | acc, g :: gs => chkFold vf xu (andBit acc (chkOneP vf xu (IPM.encFrm g))) gs

theorem chkFold_flag (vf : List Bool → List Bool) (x u : List Bool) :
    ∀ (fs : List IPM.Frm) (b : Bool),
      chkFold vf (pair x u) [b] fs = [b && stkCheckB vf x u fs] := by
  intro fs
  induction fs with
  | nil => intro b; simp [chkFold]
  | cons g gs ih =>
      intro b
      rw [chkFold, chkOneP_enc, andBit_cons, ih, stkCheckB_cons, Bool.and_assoc]

/-- **The scan folds every frame in.** -/
theorem chkStep_iterate (vf : List Bool → List Bool) (xu : List Bool) :
    ∀ (fs : List IPM.Frm) (acc : List Bool) (n : ℕ), fs.length ≤ n →
      (chkStep vf)^[n] (xu, acc, IPM.encStk fs) = (xu, chkFold vf xu acc fs, []) := by
  intro fs
  induction fs with
  | nil =>
      intro acc n _
      have : ∀ m : ℕ, (chkStep vf)^[m] (xu, acc, ([] : List Bool)) = (xu, acc, []) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [Function.iterate_succ_apply, chkStep_nil, ih]
      rw [IPM.encStk_nil, this]
      rfl
  | cons g gs ih =>
      intro acc n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      rw [Function.iterate_succ_apply, chkStep_cons, ih _ m (by simp at hn; omega), chkFold]

/-! ## The packed scan -/

theorem sndBlock_length_le (z : List Bool) : (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨p, q⟩
  · rw [show pairSnd z = [] from by rw [pairSnd, hu]]
    simp
  · have hz : z = pair p q := unpair?_eq_some_iff.mp hu
    rw [show pairSnd z = q from by rw [pairSnd, hu], hz, pair_length]
    omega

/-- The packed scan state: the verifier's fixed arguments, the running flag, and the chain of
frames still to check. -/
def chkPack (xu acc S : List Bool) : List Bool := pair xu (pair acc S)

@[simp] theorem chkPack_length (xu acc S : List Bool) :
    (chkPack xu acc S).length = 2 * xu.length + 2 * acc.length + S.length + 4 := by
  rw [chkPack, pair_length, pair_length]
  omega

/-- One step of the packed scan. -/
def chkStepP (vf : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pairFst z)
    (pair
      (selectHead (emptyFlag (pairSnd (pairSnd z))) (pairFst (pairSnd z))
        (andBit (pairFst (pairSnd z))
          (chkOneP vf (pairFst z) (pairFst (pairSnd (pairSnd z))))))
      (selectHead (emptyFlag (pairSnd (pairSnd z))) (pairSnd (pairSnd z))
        (pairSnd (pairSnd (pairSnd z)))))

theorem chkStepP_pack (vf : List Bool → List Bool) (xu acc S : List Bool) :
    chkStepP vf (chkPack xu acc S)
      = chkPack (chkStep vf (xu, acc, S)).1 (chkStep vf (xu, acc, S)).2.1
          (chkStep vf (xu, acc, S)).2.2 := by
  rw [chkStepP, chkPack, chkStep, chkPack]
  simp only [pairFst_pair, pairSnd_pair]

theorem chkStepP_iterate (vf : List Bool → List Bool)
    (s : List Bool × List Bool × List Bool) (n : ℕ) :
    (chkStepP vf)^[n] (chkPack s.1 s.2.1 s.2.2)
      = chkPack ((chkStep vf)^[n] s).1 ((chkStep vf)^[n] s).2.1 ((chkStep vf)^[n] s).2.2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, chkStepP_pack, ih (chkStep vf s),
        Function.iterate_succ_apply]

theorem chkStepP_iterate_args (vf : List Bool → List Bool) (xu acc S : List Bool) (n : ℕ) :
    (chkStepP vf)^[n] (chkPack xu acc S)
      = chkPack ((chkStep vf)^[n] (xu, acc, S)).1 ((chkStep vf)^[n] (xu, acc, S)).2.1
          ((chkStep vf)^[n] (xu, acc, S)).2.2 :=
  chkStepP_iterate vf (xu, acc, S) n

theorem chkStep_iterate_length (vf : List Bool → List Bool) (xu acc S : List Bool) (n : ℕ) :
    ((chkStep vf)^[n] (xu, acc, S)).1 = xu ∧
      ((chkStep vf)^[n] (xu, acc, S)).2.1.length ≤ max acc.length 1 ∧
      ((chkStep vf)^[n] (xu, acc, S)).2.2.length ≤ S.length := by
  induction n generalizing acc S with
  | zero => exact ⟨rfl, le_max_left _ _, le_rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have hacc : (selectHead (emptyFlag S) acc
          (andBit acc (chkOneP vf xu (pairFst S)))).length ≤ max acc.length 1 := by
        rw [selectHead]
        split
        · exact le_max_left _ _
        · split
          · rw [andBit_length_eq]
            exact le_max_right _ _
          · simp
      have hS : (selectHead (emptyFlag S) S (pairSnd S)).length ≤ S.length := by
        rw [selectHead]
        split
        · exact le_rfl
        · split
          · exact sndBlock_length_le S
          · simp
      obtain ⟨h1, h2, h3⟩ := ih (selectHead (emptyFlag S) acc
        (andBit acc (chkOneP vf xu (pairFst S))))
        (selectHead (emptyFlag S) S (pairSnd S))
      refine ⟨h1, le_trans h2 ?_, le_trans h3 hS⟩
      have hchain := max_le_max_right (α := ℕ) 1 hacc
      omega

/-! ## The leaf test -/

/-- The consistency flag, computed by running the scan against a ruler. -/
def chkFlag (vf : List Bool → List Bool) (rr xu S : List Bool) : List Bool :=
  pairFst (pairSnd ((chkStepP vf)^[rr.length] (chkPack xu [true] S)))

theorem chkFlag_eq (vf : List Bool → List Bool) (rr : List Bool) (x u : List Bool)
    (fs : List IPM.Frm) (h : fs.length ≤ rr.length) :
    chkFlag vf rr (pair x u) (IPM.encStk fs) = [stkCheckB vf x u fs] := by
  rw [chkFlag, chkStepP_iterate_args, chkStep_iterate vf _ fs [true] rr.length h, chkPack]
  simp only [pairSnd_pair, pairFst_pair]
  rw [chkFold_flag vf x u fs true, Bool.true_and]

/-- **The leaf test on the tape**: the transcript replays, and the verifier accepts. -/
def okFn (vf vd : List Bool → List Bool) (rr x S u : List Bool) : List Bool :=
  andBit (chkFlag vf rr (pair x u) (pairSnd S))
    (vd (pair (pair x u) (false :: IPM.fBody (pairFst S) ++ [true])))

open Classical in
/-- **The leaf test computes what the walk asks for.** -/
theorem okFn_eq (prot : Protocol) (vd : List Bool → List Bool)
    (hvd : ∀ z, vd z = [decide (z ∈ prot.verdict)])
    (rr x u : List Bool) (f : IPM.Frm) (fs : List IPM.Frm)
    (hb : IPM.BodyOk (f :: fs)) (hlen : fs.length ≤ rr.length) :
    okFn prot.vmsg vd rr x (IPM.encStk (f :: fs)) u
      = [(prot.walkParams x).ok (IPM.roundsOf fs) u] := by
  classical
  rw [okFn, IPM.encStk_cons, pairSnd_pair, pairFst_pair,
    chkFlag_eq prot.vmsg rr x u fs hlen, IPM.fBody_enc, hvd, andBit_cons, hb.1,
    ← replay_eq_stkCheckB prot x u fs hb.2]
  show _ = [decide (prot.replay x u (IPM.roundsOf fs) [] = true ∧
    pair (pair x u) (false :: encBodyR (IPM.roundsOf fs) ++ [true]) ∈ prot.verdict)]
  simp only [Bool.decide_and, Bool.decide_eq_true]

/-! ## The leaf test is polynomial-time -/

theorem chkOnePFn_mem_FP {vf : List Bool → List Bool} (hvf : vf ∈ FP)
    {XU Y : List Bool → List Bool} (hxu : XU ∈ FP) (hy : Y ∈ FP) :
    (fun z => chkOneP vf (XU z) (Y z)) ∈ FP := by
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    exact this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    exact this
  have hV : (fun z => IPM.fV (Y z)) ∈ FP := hfst (hsnd hy)
  have hBody : (fun z => IPM.fBody (Y z)) ∈ FP := hsnd (hsnd (hsnd (hsnd (hsnd hy))))
  have hcons : (fun z => false :: (IPM.fBody (Y z) ++ [true])) ∈ FP := by
    have hcat := Cobham.appendFn_mem_FP hBody (constFn_mem_FP [true])
    have := mem_FP_comp hcat (Cobham.cons_mem_FP false)
    exact this
  have harg : (fun z => vf (pair (XU z) (false :: (IPM.fBody (Y z) ++ [true])))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP hxu hcons) hvf
    exact this
  exact eqFlagFn_mem_FP hV harg

theorem chkStepPFn_mem_FP {vf : List Bool → List Bool} (hvf : vf ∈ FP) : chkStepP vf ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    exact this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    exact this
  have hxu := hfst hid
  have hw := hsnd hid
  have hacc := hfst hw
  have hS := hsnd hw
  have hflag := emptyFlagFn_mem_FP hS
  exact Cobham.pairFn_mem_FP hxu
    (Cobham.pairFn_mem_FP
      (Cobham.selectHeadFn_mem_FP hflag hacc
        (andBitFn_mem_FP hacc (chkOnePFn_mem_FP hvf hxu (hfst hS))))
      (Cobham.selectHeadFn_mem_FP hflag hS (hsnd hS)))

theorem chkFlagFn_mem_FP {vf : List Bool → List Bool} (hvf : vf ∈ FP)
    {R XU S : List Bool → List Bool} (hR : R ∈ FP) (hxu : XU ∈ FP) (hS : S ∈ FP) :
    (fun z => chkFlag vf (R z) (XU z) (S z)) ∈ FP := by
  have hinit : (fun z => chkPack (XU z) [true] (S z)) ∈ FP :=
    Cobham.pairFn_mem_FP hxu (Cobham.pairFn_mem_FP (constFn_mem_FP [true]) hS)
  have hwidth : (fun z => chkPack (XU z) [false] (S z)) ∈ FP :=
    Cobham.pairFn_mem_FP hxu (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) hS)
  have hbound : ∀ z, ∀ n ≤ (R z).length,
      ((chkStepP vf)^[n] (chkPack (XU z) [true] (S z))).length
        ≤ (chkPack (XU z) [false] (S z)).length := by
    intro z n _
    rw [chkStepP_iterate_args, chkPack_length, chkPack_length]
    obtain ⟨h1, h2, h3⟩ := chkStep_iterate_length vf (XU z) [true] (S z) n
    rw [h1]
    simp only [List.length_cons, List.length_nil] at h2 ⊢
    omega
  have h := Cobham.iterate_mem_FP (chkStepPFn_mem_FP hvf) hinit hR hwidth hbound
  have h1 := mem_FP_comp h Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.fstBlock_mem_FP
  simp [chkFlag]
  exact h2

theorem okFnFn_mem_FP {vf vd : List Bool → List Bool} (hvf : vf ∈ FP) (hvd : vd ∈ FP)
    {R X S U : List Bool → List Bool} (hR : R ∈ FP) (hX : X ∈ FP) (hS : S ∈ FP)
    (hU : U ∈ FP) : (fun z => okFn vf vd (R z) (X z) (S z) (U z)) ∈ FP := by
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    exact this
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    exact this
  have hxu : (fun z => pair (X z) (U z)) ∈ FP := Cobham.pairFn_mem_FP hX hU
  have hBody : (fun z => IPM.fBody (pairFst (S z))) ∈ FP :=
    hsnd (hsnd (hsnd (hsnd (hsnd (hfst hS)))))
  have hcons : (fun z => false :: (IPM.fBody (pairFst (S z)) ++ [true])) ∈ FP := by
    have hcat := Cobham.appendFn_mem_FP hBody (constFn_mem_FP [true])
    have := mem_FP_comp hcat (Cobham.cons_mem_FP false)
    exact this
  have hverd : (fun z => vd (pair (pair (X z) (U z))
      (false :: (IPM.fBody (pairFst (S z)) ++ [true])))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP hxu hcons) hvd
    exact this
  exact andBitFn_mem_FP (chkFlagFn_mem_FP hvf hR hxu (hsnd hS)) hverd

/-! ## The leaf test discharges the walk's hypothesis -/

open Classical in
/-- The verifier's verdict as a one-bit flag. -/
theorem exists_verdictFlag (prot : Protocol) :
    ∃ vd : List Bool → List Bool, vd ∈ FP ∧ ∀ z, vd z = [decide (z ∈ prot.verdict)] := by
  classical
  obtain ⟨g, hg, hgL⟩ := exists_decisionFn_of_mem_P prot.verdict_mem
  refine ⟨fun z => [g z], hg, fun z => ?_⟩
  simp [hgL z]

open Classical in
/-- **The leaf test is exactly what the walk asks for**, for every stack the walk can reach. -/
theorem okFn_hokf (prot : Protocol) (vd : List Bool → List Bool)
    (hvd : ∀ z, vd z = [decide (z ∈ prot.verdict)]) (rr x : List Bool) (D : ℕ)
    (hD : D ≤ rr.length + 1) :
    ∀ (f : IPM.Frm) (fs : List IPM.Frm), IPM.BodyOk (f :: fs) → (f :: fs).length ≤ D →
      ∀ u : List Bool,
        okFn prot.vmsg vd rr x (IPM.encStk (f :: fs)) u
          = [(prot.walkParams x).ok (IPM.roundsOf fs) u] := by
  intro f fs hb hlen u
  refine okFn_eq prot vd hvd rr x u f fs hb ?_
  simp only [List.length_cons] at hlen
  omega

end Complexity

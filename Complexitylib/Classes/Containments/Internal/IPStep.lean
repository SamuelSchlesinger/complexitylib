/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.IPEnc

/-!
# One step of the walk, inside the polynomial-time algebra

⚠️ Unreviewed by Bolton

`Complexity.IPM.step` walks the game tree on an inductive state;
`Complexity.IPM.encSst` writes that state on a tape. This file writes the *step* on the tape, out
of the algebra's operations only, and proves the square commutes.

Everything the step needs from the protocol enters through three arguments: a ruler `mr` whose
length is the message bound, a ruler `cr` whose length is the coin width, and the leaf test `okf`,
which reads the encoded stack below a leaf and a coin string.

## Main definitions

- `Complexity.IPM.ipStep` — the encoded step
- `Complexity.IPM.freshEnc` — the frame a node starts from, on the tape

## Main results

- `Complexity.IPM.ipStep_encSst` — one encoded step is one abstract step
- `Complexity.IPM.ipStepFn_mem_FP` — and it is polynomial-time
-/

@[expose] public section

namespace Complexity

namespace IPM

open Cobham

/-! ## Reading and writing the encoded state -/

/-- The state's four fields, written. -/
def mkS (d ab r stk : List Bool) : List Bool := pair d (pair ab (pair r stk))

/-- A frame's six fields, written. -/
def mkF (lvl v a sum best body : List Bool) : List Bool :=
  pair lvl (pair v (pair a (pair sum (pair best body))))

@[simp] theorem mkS_eq (s : Sst) :
    mkS [s.done] [s.ansBit] (encRet s.ret) (encStk s.stk) = encSst s := rfl

@[simp] theorem mkF_eq (f : Frm) : mkF f.lvl f.v f.a f.sum f.best f.body = encFrm f := rfl

/-- The done flag. -/
def sDone (z : List Bool) : List Bool := pairFst z

/-- The answer bit. -/
def sAns (z : List Bool) : List Bool := pairFst (pairSnd z)

/-- The returning value. -/
def sRet (z : List Bool) : List Bool := pairFst (pairSnd (pairSnd z))

/-- The stack. -/
def sStk (z : List Bool) : List Bool := pairSnd (pairSnd (pairSnd z))

/-- A frame's level. -/
def fLvl (y : List Bool) : List Bool := pairFst y

/-- A frame's verifier counter. -/
def fV (y : List Bool) : List Bool := pairFst (pairSnd y)

/-- A frame's prover counter, or its coin counter. -/
def fA (y : List Bool) : List Bool := pairFst (pairSnd (pairSnd y))

/-- A frame's running sum. -/
def fSum (y : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd y)))

/-- A frame's running maximum. -/
def fBest (y : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd (pairSnd y))))

/-- The body of the encoding of the rounds below a frame. -/
def fBody (y : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd (pairSnd y))))

/-- The frame on top of the stack. -/
def sTop (S : List Bool) : List Bool := pairFst S

/-- The stack below the top frame. -/
def sRest (S : List Bool) : List Bool := pairSnd S

@[simp] theorem sDone_enc (s : Sst) : sDone (encSst s) = [s.done] := by
  rw [sDone, encSst, pairFst_pair]

@[simp] theorem sAns_enc (s : Sst) : sAns (encSst s) = [s.ansBit] := by
  rw [sAns, encSst, pairSnd_pair, pairFst_pair]

@[simp] theorem sRet_enc (s : Sst) : sRet (encSst s) = encRet s.ret := by
  rw [sRet, encSst, pairSnd_pair, pairSnd_pair, pairFst_pair]

@[simp] theorem sStk_enc (s : Sst) : sStk (encSst s) = encStk s.stk := by
  rw [sStk, encSst, pairSnd_pair, pairSnd_pair, pairSnd_pair]

@[simp] theorem fLvl_enc (f : Frm) : fLvl (encFrm f) = f.lvl := by
  rw [fLvl, encFrm, pairFst_pair]

@[simp] theorem fV_enc (f : Frm) : fV (encFrm f) = f.v := by
  rw [fV, encFrm, pairSnd_pair, pairFst_pair]

@[simp] theorem fA_enc (f : Frm) : fA (encFrm f) = f.a := by
  rw [fA, encFrm, pairSnd_pair, pairSnd_pair, pairFst_pair]

@[simp] theorem fSum_enc (f : Frm) : fSum (encFrm f) = f.sum := by
  rw [fSum, encFrm, pairSnd_pair, pairSnd_pair, pairSnd_pair, pairFst_pair]

@[simp] theorem fBest_enc (f : Frm) : fBest (encFrm f) = f.best := by
  rw [fBest, encFrm, pairSnd_pair, pairSnd_pair, pairSnd_pair, pairSnd_pair, pairFst_pair]

@[simp] theorem fBody_enc (f : Frm) : fBody (encFrm f) = f.body := by
  rw [fBody, encFrm, pairSnd_pair, pairSnd_pair, pairSnd_pair, pairSnd_pair, pairSnd_pair]

@[simp] theorem sTop_pair (y S : List Bool) : sTop (pair y S) = y := by
  rw [sTop, pairFst_pair]

@[simp] theorem sRest_pair (y S : List Bool) : sRest (pair y S) = S := by
  rw [sRest, pairSnd_pair]

theorem sTop_cons (f : Frm) (fs : List Frm) : sTop (encStk (f :: fs)) = encFrm f := by
  rw [encStk_cons, sTop_pair]

theorem sRest_cons (f : Frm) (fs : List Frm) : sRest (encStk (f :: fs)) = encStk fs := by
  rw [encStk_cons, sRest_pair]

/-! ## The encoded step -/

/-- The zero of a count's width, from the coin ruler. -/
def zcOf (cr : List Bool) : List Bool := padTo (cr ++ [false]) []

/-- The first coin string, from the coin ruler. -/
def zkOf (cr : List Bool) : List Bool := padTo cr []

/-- The bitstring of `2 ^ t`, from the coin ruler. -/
def tpOf (cr : List Bool) : List Bool := padTo cr [] ++ [true, false]

theorem zcOf_eq (cr : List Bool) (P : Params) (h : cr.length = P.t) :
    zcOf cr = zeroCount P := by
  rw [zcOf, padTo_nil, zeroCount, List.length_append, h]
  simp

theorem zkOf_eq (cr : List Bool) (P : Params) (h : cr.length = P.t) :
    zkOf cr = zeroCoin P := by
  rw [zkOf, padTo_nil, zeroCoin, h]

theorem tpOf_eq (cr : List Bool) (P : Params) (h : cr.length = P.t) :
    tpOf cr = twoPowBits P.t := by
  rw [tpOf, padTo_nil, twoPowBits, h]

/-- The frame a node starts from, written on the tape. -/
def freshEnc (cr body lvl : List Bool) : List Bool :=
  mkF lvl [] (selectHead (emptyFlag lvl) (zkOf cr) []) (zcOf cr) (zcOf cr) body

theorem freshEnc_eq (cr : List Bool) (P : Params) (h : cr.length = P.t) (body lvl : List Bool) :
    freshEnc cr body lvl = encFrm (freshFrm P body lvl) := by
  rw [freshEnc, encFrm, freshFrm, zcOf_eq cr P h]
  rcases lvl with _ | ⟨b, t⟩
  · rw [emptyFlag_nil, selectHead_cons_true, zkOf_eq cr P h]
    simp [mkF]
  · rw [emptyFlag_cons, selectHead_cons_false]
    simp [mkF]

/-- The descending half of the step: a leaf tallies one coin string, a branch pushes a subtree. -/
def ipDescend (cr : List Bool) (okf : List Bool → List Bool → List Bool)
    (z : List Bool) : List Bool :=
  selectHead (emptyFlag (fLvl (sTop (sStk z))))
    (selectHead (bumpFlag (fA (sTop (sStk z))))
      (mkS [false] (sAns z)
        (selectHead (okf (sStk z) (fA (sTop (sStk z))))
          (bumpCode (fSum (sTop (sStk z)))) (fSum (sTop (sStk z))))
        (sRest (sStk z)))
      (mkS [false] (sAns z) []
        (pair
          (mkF (fLvl (sTop (sStk z))) (fV (sTop (sStk z))) (bumpCode (fA (sTop (sStk z))))
            (selectHead (okf (sStk z) (fA (sTop (sStk z))))
              (bumpCode (fSum (sTop (sStk z)))) (fSum (sTop (sStk z))))
            (fBest (sTop (sStk z))) (fBody (sTop (sStk z))))
          (sRest (sStk z)))))
    (mkS [false] (sAns z) []
      (pair
        (freshEnc cr
          (fBody (sTop (sStk z)) ++ encMsg (fV (sTop (sStk z))) ++ encMsg (fA (sTop (sStk z))))
          (dropOne (fLvl (sTop (sStk z)))))
        (sStk z)))

/-- The returning half of the step: advance a counter, or pop with the sum. -/
def ipReturn (mr cr : List Bool) (z : List Bool) : List Bool :=
  selectHead (lenLeFlag mr (nextStr (fA (sTop (sStk z)))))
    (mkS [false] (sAns z) []
      (pair
        (mkF (fLvl (sTop (sStk z))) (fV (sTop (sStk z))) (nextStr (fA (sTop (sStk z))))
          (fSum (sTop (sStk z))) (maxBits (fBest (sTop (sStk z))) (sRet z))
          (fBody (sTop (sStk z))))
        (sRest (sStk z))))
    (selectHead (lenLeFlag mr (nextStr (fV (sTop (sStk z)))))
      (mkS [false] (sAns z) []
        (pair
          (mkF (fLvl (sTop (sStk z))) (nextStr (fV (sTop (sStk z)))) []
            (addBits (fSum (sTop (sStk z))) (maxBits (fBest (sTop (sStk z))) (sRet z)))
            (zcOf cr) (fBody (sTop (sStk z))))
          (sRest (sStk z))))
      (mkS [false] (sAns z)
        (addBits (fSum (sTop (sStk z))) (maxBits (fBest (sTop (sStk z))) (sRet z)))
        (sRest (sStk z))))

/-- **One step of the walk, on the tape.** -/
def ipStep (mr cr : List Bool) (okf : List Bool → List Bool → List Bool)
    (z : List Bool) : List Bool :=
  selectHead (sDone z)
    (mkS (sAns z) (sAns z) (sRet z) (sStk z))
    (selectHead (emptyFlag (sStk z))
      (mkS [true] (ltFlag (tpOf cr) (false :: sRet z)) (sRet z) (sStk z))
      (selectHead (emptyFlag (sRet z))
        (ipDescend cr okf z)
        (ipReturn mr cr z)))

/-- The state the walk starts from, on the tape. -/
def ipInit (cr rr : List Bool) : List Bool :=
  mkS [false] [false] [] (pair (freshEnc cr [] rr) [])

theorem ipInit_eq (cr : List Bool) (P : Params) (h : cr.length = P.t) (rr : List Bool) :
    ipInit cr rr = encSst ⟨false, false, none, [freshFrm P [] rr]⟩ := by
  rw [ipInit, freshEnc_eq cr P h]
  rfl

theorem ipInitFn_mem_FP {CR RR : List Bool → List Bool} (hcr : CR ∈ FP) (hrr : RR ∈ FP) :
    (fun z => ipInit (CR z) (RR z)) ∈ FP := by
  have hzc : (fun z => zcOf (CR z)) ∈ FP :=
    padToFn_mem_FP (Cobham.appendFn_mem_FP hcr (constFn_mem_FP [false])) (constFn_mem_FP [])
  have hzk : (fun z => zkOf (CR z)) ∈ FP := padToFn_mem_FP hcr (constFn_mem_FP [])
  have hfresh : (fun z => freshEnc (CR z) [] (RR z)) ∈ FP :=
    Cobham.pairFn_mem_FP hrr (Cobham.pairFn_mem_FP (constFn_mem_FP [])
      (Cobham.pairFn_mem_FP
        (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hrr) hzk (constFn_mem_FP []))
        (Cobham.pairFn_mem_FP hzc (Cobham.pairFn_mem_FP hzc (constFn_mem_FP [])))))
  exact Cobham.pairFn_mem_FP (constFn_mem_FP [false])
    (Cobham.pairFn_mem_FP (constFn_mem_FP [false])
      (Cobham.pairFn_mem_FP (constFn_mem_FP [])
        (Cobham.pairFn_mem_FP hfresh (constFn_mem_FP []))))

/-! ## The square commutes -/

theorem lenLeFlag_true (mr u : List Bool) (h : u.length ≤ mr.length) :
    lenLeFlag mr u = [true] := (lenLeFlag_eq_true_iff mr u).mpr h

theorem lenLeFlag_false (mr u : List Bool) (h : ¬ u.length ≤ mr.length) :
    lenLeFlag mr u = [false] := by
  rcases lenLeFlag_flag mr u with hh | hh
  · exact absurd ((lenLeFlag_eq_true_iff mr u).mp hh) h
  · exact hh

/-- **One encoded step is one abstract step.** -/
theorem ipStep_encSst (P : Params) (mr cr : List Bool) (hm : mr.length = P.m)
    (hc : cr.length = P.t) (okf : List Bool → List Bool → List Bool)
    (D : ℕ)
    (hokf : ∀ (f : Frm) (fs : List Frm), BodyOk (f :: fs) → (f :: fs).length ≤ D →
      ∀ u : List Bool, okf (encStk (f :: fs)) u = [P.ok (roundsOf fs) u])
    (s : Sst) (h : EncOk P D s) :
    ipStep mr cr okf (encSst s) = encSst (step P s) := by
  obtain ⟨d, a, r, stk⟩ := s
  cases d
  · cases stk with
    | nil =>
        obtain ⟨b, rfl⟩ : ∃ b, r = some b := by
          cases r with
          | none => exact absurd rfl (h.stkOk rfl)
          | some b => exact ⟨b, rfl⟩
        have hblen : b.length = P.t + 1 := h.retLen b rfl
        have hcmp : ltFlag (tpOf cr) (false :: b) = [cmpBit P b] := by
          rw [tpOf_eq cr P hc, cmpBit,
            ltFlag_eq _ _ (by rw [List.length_cons, hblen, twoPowBits_length])]
        rw [step_of_empty, ipStep]
        simp only [sDone_enc, selectHead_cons_false, sStk_enc, encStk_nil, emptyFlag_nil,
          selectHead_cons_true, sRet_enc, encRet_some, sAns_enc, hcmp]
        rfl
    | cons f fs =>
      cases r with
      | none =>
          by_cases hl : f.lvl = []
          · have hokv := hokf f fs h.bodyOk (StkDepth.length_le h.depthOk) f.a
            rw [encStk_cons] at hokv
            by_cases hov : bumpOver f.a = true
            · rw [step_leaf_last P a f fs hl hov, ipStep]
              simp only [sDone_enc, selectHead_cons_false, sStk_enc, encStk_cons,
                emptyFlag_pair, sRet_enc, encRet_none, emptyFlag_nil, selectHead_cons_true,
                ipDescend, sTop_pair, sRest_pair, fLvl_enc, fA_enc, fSum_enc, sAns_enc, hl,
                hokv, bumpFlag_eq, hov, bumpCode_eq]
              cases hokb : P.ok (roundsOf fs) f.a <;> simp [encSst, mkS]
            · have hovf : bumpOver f.a = false := by simpa using hov
              rw [step_leaf_next P a f fs hl hovf, ipStep]
              simp only [sDone_enc, selectHead_cons_false, sStk_enc, encStk_cons,
                emptyFlag_pair, sRet_enc, encRet_none, emptyFlag_nil, selectHead_cons_true,
                ipDescend, sTop_pair, sRest_pair, fLvl_enc, fA_enc, fSum_enc, fV_enc,
                fBest_enc, fBody_enc, sAns_enc, hl, hokv, bumpFlag_eq, hovf, bumpCode_eq]
              cases hokb : P.ok (roundsOf fs) f.a <;> simp [encSst, mkS, mkF, encFrm]
          · obtain ⟨c, tl, hlc⟩ : ∃ c tl, f.lvl = c :: tl := by
              cases hcc : f.lvl with
              | nil => exact absurd hcc hl
              | cons c tl => exact ⟨c, tl, rfl⟩
            rw [step_push P a f fs hl, ipStep]
            simp only [sDone_enc, selectHead_cons_false, sStk_enc, encStk_cons,
              emptyFlag_pair, sRet_enc, encRet_none, emptyFlag_nil, selectHead_cons_true,
              ipDescend, sTop_pair, fLvl_enc, sAns_enc, hlc, emptyFlag_cons,
              selectHead_cons_false]
            rw [dropOne, ← hlc, freshEnc_eq cr P hc]
            rw [childFrm]
            simp [encSst, mkS, encStk_cons]
      | some w =>
          have hew : emptyFlag w = [false] := by
            obtain ⟨b0, t0, rfl⟩ : ∃ b0 t0, w = b0 :: t0 := by
              cases hcw : w with
              | nil => exact absurd (encRet_ne_nil h rfl) (by simp [hcw])
              | cons b0 t0 => exact ⟨b0, t0, rfl⟩
            exact emptyFlag_cons _ _
          by_cases hA : (nextStr f.a).length ≤ P.m
          · have h1 : lenLeFlag mr (nextStr f.a) = [true] :=
              lenLeFlag_true mr (nextStr f.a) (by rw [hm]; exact hA)
            rw [step_ret_more_a P a f fs w hA, ipStep]
            simp only [sDone_enc, selectHead_cons_false, sStk_enc, encStk_cons,
              emptyFlag_pair, sRet_enc, encRet_some, hew, selectHead_cons_false, ipReturn,
              sTop_pair, sRest_pair, fA_enc, fV_enc, fLvl_enc, fSum_enc, fBest_enc,
              fBody_enc, sAns_enc, h1, selectHead_cons_true]
            simp [encSst, mkS, mkF, encFrm]
          · have h1 : lenLeFlag mr (nextStr f.a) = [false] :=
              lenLeFlag_false mr (nextStr f.a) (by rw [hm]; exact hA)
            by_cases hV : (nextStr f.v).length ≤ P.m
            · have h2 : lenLeFlag mr (nextStr f.v) = [true] :=
                lenLeFlag_true mr (nextStr f.v) (by rw [hm]; exact hV)
              rw [step_ret_more_v P a f fs w hA hV, ipStep]
              simp only [sDone_enc, selectHead_cons_false, sStk_enc, encStk_cons,
                emptyFlag_pair, sRet_enc, encRet_some, hew, selectHead_cons_false, ipReturn,
                sTop_pair, sRest_pair, fA_enc, fV_enc, fLvl_enc, fSum_enc, fBest_enc,
                fBody_enc, sAns_enc, h1, h2, selectHead_cons_true]
              rw [zcOf_eq cr P hc]
              simp [encSst, mkS, mkF, encFrm]
            · have h2 : lenLeFlag mr (nextStr f.v) = [false] :=
                lenLeFlag_false mr (nextStr f.v) (by rw [hm]; exact hV)
              rw [step_ret_pop P a f fs w hA hV, ipStep]
              simp only [sDone_enc, selectHead_cons_false, sStk_enc, encStk_cons,
                emptyFlag_pair, sRet_enc, encRet_some, hew, selectHead_cons_false, ipReturn,
                sTop_pair, sRest_pair, fA_enc, fV_enc, fLvl_enc, fSum_enc, fBest_enc,
                fBody_enc, sAns_enc, h1, h2]
              simp [encSst, mkS]
  · rw [step_of_done, ipStep]
    simp only [sDone_enc, selectHead_cons_true, sAns_enc, sRet_enc, sStk_enc]
    rfl

/-- **And so is any number of steps.** -/
theorem ipStep_iterate (P : Params) (mr cr : List Bool) (hm : mr.length = P.m)
    (hc : cr.length = P.t) (okf : List Bool → List Bool → List Bool)
    (D : ℕ)
    (hokf : ∀ (f : Frm) (fs : List Frm), BodyOk (f :: fs) → (f :: fs).length ≤ D →
      ∀ u : List Bool, okf (encStk (f :: fs)) u = [P.ok (roundsOf fs) u]) :
    ∀ (j : ℕ) (s : Sst), EncOk P D s →
      (ipStep mr cr okf)^[j] (encSst s) = encSst ((step P)^[j] s) := by
  intro j
  induction j with
  | zero => intro s _; rfl
  | succ j ih =>
      intro s h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ipStep_encSst P mr cr hm hc okf D hokf s h]
      exact ih _ (step_encOk P D h)

/-! ## The encoded step is polynomial-time -/

theorem ipStepFn_mem_FP {A B C : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hC : C ∈ FP)
    {OK : List Bool → List Bool → List Bool → List Bool}
    (hok : ∀ {u v : List Bool → List Bool}, u ∈ FP → v ∈ FP →
      (fun z => OK z (u z) (v z)) ∈ FP) :
    (fun z => ipStep (A z) (B z) (OK z) (C z)) ∈ FP := by
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    exact this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    exact this
  have hcons : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => false :: a z) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha (Cobham.cons_mem_FP false)
    exact this
  -- the state's fields
  have hD : (fun z => sDone (C z)) ∈ FP := hfst hC
  have hAns : (fun z => sAns (C z)) ∈ FP := hfst (hsnd hC)
  have hR : (fun z => sRet (C z)) ∈ FP := hfst (hsnd (hsnd hC))
  have hS : (fun z => sStk (C z)) ∈ FP := hsnd (hsnd (hsnd hC))
  -- the top frame's fields
  have hT : (fun z => sTop (sStk (C z))) ∈ FP := hfst hS
  have hRest : (fun z => sRest (sStk (C z))) ∈ FP := hsnd hS
  have hLvl : (fun z => fLvl (sTop (sStk (C z)))) ∈ FP := hfst hT
  have hV : (fun z => fV (sTop (sStk (C z)))) ∈ FP := hfst (hsnd hT)
  have hAa : (fun z => fA (sTop (sStk (C z)))) ∈ FP := hfst (hsnd (hsnd hT))
  have hSum : (fun z => fSum (sTop (sStk (C z)))) ∈ FP := hfst (hsnd (hsnd (hsnd hT)))
  have hBest : (fun z => fBest (sTop (sStk (C z)))) ∈ FP := hfst (hsnd (hsnd (hsnd (hsnd hT))))
  have hBody : (fun z => fBody (sTop (sStk (C z)))) ∈ FP := hsnd (hsnd (hsnd (hsnd (hsnd hT))))
  -- the constants built from the coin ruler
  have hzc : (fun z => zcOf (B z)) ∈ FP :=
    padToFn_mem_FP (Cobham.appendFn_mem_FP hB (constFn_mem_FP [false])) (constFn_mem_FP [])
  have hzk : (fun z => zkOf (B z)) ∈ FP := padToFn_mem_FP hB (constFn_mem_FP [])
  have htp : (fun z => tpOf (B z)) ∈ FP :=
    Cobham.appendFn_mem_FP (padToFn_mem_FP hB (constFn_mem_FP [])) (constFn_mem_FP [true, false])
  -- the pieces of the descending half
  have hnew : (fun z => selectHead (OK z (sStk (C z)) (fA (sTop (sStk (C z)))))
      (bumpCode (fSum (sTop (sStk (C z))))) (fSum (sTop (sStk (C z))))) ∈ FP :=
    Cobham.selectHeadFn_mem_FP (hok hS hAa) (bumpCodeFn_mem_FP hSum) hSum
  have hnb : (fun z => fBody (sTop (sStk (C z))) ++ encMsg (fV (sTop (sStk (C z))))
      ++ encMsg (fA (sTop (sStk (C z))))) ∈ FP :=
    Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP hBody (encMsgFn_mem_FP hV))
      (encMsgFn_mem_FP hAa)
  have hfresh : (fun z => freshEnc (B z)
      (fBody (sTop (sStk (C z))) ++ encMsg (fV (sTop (sStk (C z))))
        ++ encMsg (fA (sTop (sStk (C z)))))
      (dropOne (fLvl (sTop (sStk (C z)))))) ∈ FP := by
    refine Cobham.pairFn_mem_FP (dropOneFn_mem_FP hLvl) (Cobham.pairFn_mem_FP
      (constFn_mem_FP []) (Cobham.pairFn_mem_FP
        (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP (dropOneFn_mem_FP hLvl)) hzk
          (constFn_mem_FP []))
        (Cobham.pairFn_mem_FP hzc (Cobham.pairFn_mem_FP hzc hnb))))
  have hdesc : (fun z => ipDescend (B z) (OK z) (C z)) ∈ FP :=
    Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hLvl)
      (Cobham.selectHeadFn_mem_FP (bumpFlagFn_mem_FP hAa)
        (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) (Cobham.pairFn_mem_FP hAns
          (Cobham.pairFn_mem_FP hnew hRest)))
        (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) (Cobham.pairFn_mem_FP hAns
          (Cobham.pairFn_mem_FP (constFn_mem_FP [])
            (Cobham.pairFn_mem_FP
              (Cobham.pairFn_mem_FP hLvl (Cobham.pairFn_mem_FP hV
                (Cobham.pairFn_mem_FP (bumpCodeFn_mem_FP hAa)
                  (Cobham.pairFn_mem_FP hnew (Cobham.pairFn_mem_FP hBest hBody)))))
              hRest)))))
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) (Cobham.pairFn_mem_FP hAns
        (Cobham.pairFn_mem_FP (constFn_mem_FP []) (Cobham.pairFn_mem_FP hfresh hS))))
  -- the pieces of the returning half
  have hmax : (fun z => maxBits (fBest (sTop (sStk (C z)))) (sRet (C z))) ∈ FP :=
    maxBitsFn_mem_FP hBest hR
  have hadd : (fun z => addBits (fSum (sTop (sStk (C z))))
      (maxBits (fBest (sTop (sStk (C z)))) (sRet (C z)))) ∈ FP := addBitsFn_mem_FP hSum hmax
  have hret : (fun z => ipReturn (A z) (B z) (C z)) ∈ FP :=
    Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hA (nextStrFn_mem_FP hAa))
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) (Cobham.pairFn_mem_FP hAns
        (Cobham.pairFn_mem_FP (constFn_mem_FP [])
          (Cobham.pairFn_mem_FP
            (Cobham.pairFn_mem_FP hLvl (Cobham.pairFn_mem_FP hV
              (Cobham.pairFn_mem_FP (nextStrFn_mem_FP hAa)
                (Cobham.pairFn_mem_FP hSum (Cobham.pairFn_mem_FP hmax hBody)))))
            hRest))))
      (Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hA (nextStrFn_mem_FP hV))
        (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) (Cobham.pairFn_mem_FP hAns
          (Cobham.pairFn_mem_FP (constFn_mem_FP [])
            (Cobham.pairFn_mem_FP
              (Cobham.pairFn_mem_FP hLvl (Cobham.pairFn_mem_FP (nextStrFn_mem_FP hV)
                (Cobham.pairFn_mem_FP (constFn_mem_FP [])
                  (Cobham.pairFn_mem_FP hadd (Cobham.pairFn_mem_FP hzc hBody)))))
              hRest))))
        (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) (Cobham.pairFn_mem_FP hAns
          (Cobham.pairFn_mem_FP hadd hRest))))
  exact Cobham.selectHeadFn_mem_FP hD
    (Cobham.pairFn_mem_FP hAns (Cobham.pairFn_mem_FP hAns (Cobham.pairFn_mem_FP hR hS)))
    (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hS)
      (Cobham.pairFn_mem_FP (constFn_mem_FP [true])
        (Cobham.pairFn_mem_FP (ltFlagFn_mem_FP htp (hcons hR))
          (Cobham.pairFn_mem_FP hR hS)))
      (Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hR) hdesc hret))

end IPM

end Complexity

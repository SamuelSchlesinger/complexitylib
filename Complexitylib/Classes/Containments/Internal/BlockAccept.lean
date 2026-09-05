/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.CodeAccept
public import Complexitylib.Classes.Containments.Internal.BlockMember

/-!
# Scanning the visited string for an accepting record

⚠️ Unreviewed by Bolton

The last step of the search is a scan of the visited string that ORs the
accepting-record test of
`Complexitylib.Classes.Containments.Internal.CodeAccept` over its records. It is
the scan of `Complexitylib.Classes.Containments.Internal.BlockMember` with a
different test, so its correctness comes straight from `anyStepPair`.

Two rulers travel in the state: the block ruler, which the test slices a record
with, and the rewind ruler, which says how long to drive the output head left.
The record width is `2(k+2)+1` block rulers, so it need not be carried.

## Main definitions

- `Complexity.acceptPack`, `Complexity.acceptStep` — the packed scan
- `Complexity.acceptScan` — its verdict

## Main results

- `Complexity.acceptStep_pack`, `Complexity.acceptStep_iterate` — packed is
  unpacked
- `Complexity.acceptScan_eq_true_iff` — what the scan decides
- `Complexity.acceptStep_mem_FP`, `Complexity.acceptScanFn_mem_FP` — both are
  polynomial-time
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The packed scan -/

/-- The packed accept-scan state: the two rulers, then the flag and the rest. -/
def acceptPack (R ruler flag rest : List Bool) : List Bool :=
  pair (pair R ruler) (pair flag rest)

@[simp] theorem acceptPack_length (R ruler flag rest : List Bool) :
    (acceptPack R ruler flag rest).length
      = 2 * (2 * R.length + ruler.length + 2) + 2 * flag.length + rest.length + 4 := by
  rw [acceptPack, pair_length, pair_length, pair_length]
  omega

/-- One step of the accept scan. -/
noncomputable def acceptStep (k : ℕ) (qcode z : List Bool) : List Bool :=
  pair (pairFst z)
    (selectHead
      (lenLeFlag (pairSnd (pairSnd z))
        (wideRuler (codeBlocks k) (pairFst (pairFst z))))
      (pair
        (orBit (pairFst (pairSnd z))
          (acceptFlag qcode (pairFst (pairFst z)) (pairSnd (pairFst z))
            ((pairSnd (pairSnd z)).take
              (wideRuler (codeBlocks k) (pairFst (pairFst z))).length)))
        ((pairSnd (pairSnd z)).drop
          (wideRuler (codeBlocks k) (pairFst (pairFst z))).length))
      (pairSnd z))

/-- The unpacked step the packed one performs. -/
noncomputable def acceptPairStep (k : ℕ) (qcode R ruler : List Bool) :
    List Bool × List Bool → List Bool × List Bool :=
  anyStepPair (wideRuler (codeBlocks k) R) (acceptFlag qcode R ruler)

/-- **The packed step is the unpacked step.** -/
theorem acceptStep_pack (k : ℕ) (qcode R ruler flag rest : List Bool) :
    acceptStep k qcode (acceptPack R ruler flag rest)
      = acceptPack R ruler (acceptPairStep k qcode R ruler (flag, rest)).1
          (acceptPairStep k qcode R ruler (flag, rest)).2 := by
  rw [acceptStep, acceptPack]
  simp only [pairFst_pair, pairSnd_pair]
  by_cases hle : (wideRuler (codeBlocks k) R).length ≤ rest.length
  · rw [acceptPairStep, anyStepPair_pos _ (acceptFlag qcode R ruler) (flag, rest) hle,
      Cobham.selectHead,
      ite_eq_left (by
        rw [(Cobham.lenLeFlag_eq_true_iff rest (wideRuler (codeBlocks k) R)).mpr hle]
        rfl)]
    rfl
  · rw [acceptPairStep, anyStepPair_neg _ (acceptFlag qcode R ruler) (flag, rest) hle,
      Cobham.selectHead]
    have hflag : Cobham.lenLeFlag rest (wideRuler (codeBlocks k) R) = [false] := by
      rcases Cobham.lenLeFlag_flag rest (wideRuler (codeBlocks k) R) with h | h
      · rw [Cobham.lenLeFlag_eq_true_iff] at h
        omega
      · exact h
    rw [ite_eq_right (by rw [hflag]; simp), ite_eq_left (by rw [hflag]; rfl)]
    rfl

/-- **The packed iteration is the unpacked one.** -/
theorem acceptStep_iterate (k : ℕ) (qcode R ruler : List Bool)
    (s : List Bool × List Bool) (n : ℕ) :
    (acceptStep k qcode)^[n] (acceptPack R ruler s.1 s.2)
      = acceptPack R ruler ((acceptPairStep k qcode R ruler)^[n] s).1
          ((acceptPairStep k qcode R ruler)^[n] s).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, acceptStep_pack,
        ih (acceptPairStep k qcode R ruler s), Function.iterate_succ_apply]

/-! ## The verdict -/

/-- Does any record of `V` pass the accepting test? -/
noncomputable def acceptScan (k : ℕ) (qcode R ruler V : List Bool) : List Bool :=
  pairFst (pairSnd ((acceptStep k qcode)^[V.length] (acceptPack R ruler [false] V)))

theorem acceptScan_flag (k : ℕ) (qcode R ruler V : List Bool) :
    acceptScan k qcode R ruler V = [true] ∨ acceptScan k qcode R ruler V = [false] := by
  rw [acceptScan, show V = ((([false] : List Bool), V)).2 from rfl,
    show ([false] : List Bool) = ((([false] : List Bool), V)).1 from rfl,
    acceptStep_iterate, acceptPack]
  simp only [pairFst_pair, pairSnd_pair]
  exact anyStepPair_flag _ (fun z => acceptFlag_flag qcode R ruler z) (Or.inr rfl) _

/-- **The scan finds an accepting record exactly when there is one.** -/
theorem acceptScan_eq_true_iff (k : ℕ) (qcode R ruler V : List Bool)
    (hR : 0 < R.length) :
    acceptScan k qcode R ruler V = [true] ↔
      ∃ i, i * (wideRuler (codeBlocks k) R).length
            + (wideRuler (codeBlocks k) R).length ≤ V.length ∧
        acceptFlag qcode R ruler (blockAt (wideRuler (codeBlocks k) R) V i) = [true] := by
  have hw : 0 < (wideRuler (codeBlocks k) R).length := by
    rw [wideRuler_length, codeBlocks]
    positivity
  rw [acceptScan, show V = ((([false] : List Bool), V)).2 from rfl,
    show ([false] : List Bool) = ((([false] : List Bool), V)).1 from rfl,
    acceptStep_iterate, acceptPack]
  simp only [pairFst_pair, pairSnd_pair]
  rw [acceptPairStep,
    anyStepPair_flag_eq_true_iff _ (fun z => acceptFlag_flag qcode R ruler z) _ (Or.inr rfl)]
  constructor
  · rintro (h | ⟨i, -, hlen, hblk⟩)
    · simp at h
    · exact ⟨i, hlen, hblk⟩
  · rintro ⟨i, hlen, hblk⟩
    refine Or.inr ⟨i, ?_, hlen, hblk⟩
    calc i ≤ i * (wideRuler (codeBlocks k) R).length :=
          Nat.le_mul_of_pos_right _ hw
      _ < V.length := by omega

/-! ## The scan is polynomial-time -/

theorem acceptStep_mem_FP (k : ℕ) (qcode : List Bool) : acceptStep k qcode ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP →
      (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    exact this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP →
      (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    exact this
  have hhead := hfst hid
  have hR := hfst hhead
  have hruler := hsnd hhead
  have htail := hsnd hid
  have hflag := hfst htail
  have hrest := hsnd htail
  have hwide := wideRulerFn_mem_FP hR (codeBlocks k)
  have htake : (fun z => (pairSnd (pairSnd z)).take
      (wideRuler (codeBlocks k) (pairFst (pairFst z))).length) ∈ FP :=
    Cobham.takeLenFn_mem_FP hwide hrest
  have hdrop : (fun z => (pairSnd (pairSnd z)).drop
      (wideRuler (codeBlocks k) (pairFst (pairFst z))).length) ∈ FP :=
    dropLenFn_mem_FP hwide hrest
  exact Cobham.pairFn_mem_FP hhead
    (Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP hrest hwide)
      (Cobham.pairFn_mem_FP
        (orBitFn_mem_FP hflag (acceptFlagFn_mem_FP qcode hR hruler htake)) hdrop)
      htail)

/-- The scan's state never grows. -/
theorem acceptStep_iterate_length_le (k : ℕ) (qcode R ruler : List Bool)
    (s : List Bool × List Bool) (hf : s.1 = [true] ∨ s.1 = [false]) (n : ℕ) :
    ((acceptStep k qcode)^[n] (acceptPack R ruler s.1 s.2)).length
      ≤ (acceptPack R ruler s.1 s.2).length := by
  rw [acceptStep_iterate, acceptPack_length, acceptPack_length]
  have hflen : ((acceptPairStep k qcode R ruler)^[n] s).1.length = s.1.length := by
    have hcase := anyStepPair_flag (wideRuler (codeBlocks k) R)
      (fun z => acceptFlag_flag qcode R ruler z) (s := s) hf n
    rw [acceptPairStep] at *
    rcases hcase with h | h <;> rw [h] <;> rcases hf with h' | h' <;> rw [h'] <;> rfl
  have hrest : ((acceptPairStep k qcode R ruler)^[n] s).2.length ≤ s.2.length := by
    rw [acceptPairStep]
    exact anyStepPair_rest_length _ _ s n
  omega

/-- **The accept scan is polynomial-time.** -/
theorem acceptScanFn_mem_FP (k : ℕ) (qcode : List Bool)
    {Rf rulerf Vf : List Bool → List Bool} (hR : Rf ∈ FP) (hruler : rulerf ∈ FP)
    (hV : Vf ∈ FP) :
    (fun w => acceptScan k qcode (Rf w) (rulerf w) (Vf w)) ∈ FP := by
  have hinit : (fun w => acceptPack (Rf w) (rulerf w) [false] (Vf w)) ∈ FP :=
    Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP hR hruler)
      (Cobham.pairFn_mem_FP (constFn_mem_FP [false]) hV)
  have hbound : ∀ w, ∀ n ≤ (Vf w).length,
      ((acceptStep k qcode)^[n] (acceptPack (Rf w) (rulerf w) [false] (Vf w))).length
        ≤ (acceptPack (Rf w) (rulerf w) [false] (Vf w)).length :=
    fun w n _ => acceptStep_iterate_length_le k qcode (Rf w) (rulerf w)
      ([false], Vf w) (Or.inr rfl) n
  have h := Cobham.iterate_mem_FP (acceptStep_mem_FP k qcode) hinit hV hinit hbound
  have h1 := mem_FP_comp h Cobham.sndBlock_mem_FP
  have h2 := mem_FP_comp h1 Cobham.fstBlock_mem_FP
  refine mem_FP_of_eq h2 fun w => ?_
  rw [Function.comp_apply, Function.comp_apply, acceptScan]

end Complexity

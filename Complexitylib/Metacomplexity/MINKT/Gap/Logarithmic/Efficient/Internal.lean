/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Efficient.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Internal
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Metacomplexity.Kolmogorov

/-!
# Efficient threshold search for logarithmic-gap MINKT -- proof internals
-/


public section

namespace Complexity

namespace GapMINKT

namespace Logarithmic

namespace Efficient

private theorem thresholdInstance_encode (inst : MINKT.Instance)
    (threshold : ℕ) :
    (thresholdInstance inst threshold).encode =
      pair inst.encode (List.replicate threshold true) := by
  rfl

private def firstAcceptedBefore (decide : List Bool → Bool)
    (base : List Bool) : ℕ → Option ℕ
  | 0 => none
  | limit + 1 =>
      match firstAcceptedBefore decide base limit with
      | some threshold => some threshold
      | none =>
          if decide (pair base (List.replicate limit true)) then some limit
          else none

private def stateAt (decide : List Bool → Bool) (base : List Bool)
    (iterations : ℕ) : List Bool :=
  let result := firstAcceptedBefore decide base iterations
  let found := match result with
    | some _ => [true]
    | none => [false]
  let best := match result with
    | some threshold => List.replicate threshold true
    | none => pairSnd base
  pair base (pair (List.replicate iterations true) (pair found best))

private theorem firstAcceptedBefore_spec (decide : List Bool → Bool)
    (base : List Bool) (iterations : ℕ) :
    match firstAcceptedBefore decide base iterations with
    | none => ∀ threshold < iterations,
        decide (pair base (List.replicate threshold true)) = false
    | some first =>
        first < iterations ∧
          decide (pair base (List.replicate first true)) = true ∧
          ∀ threshold < iterations,
            decide (pair base (List.replicate threshold true)) = true →
              first ≤ threshold := by
  induction iterations with
  | zero => simp [firstAcceptedBefore]
  | succ limit ih =>
      cases hprevious : firstAcceptedBefore decide base limit with
      | none =>
          rw [hprevious] at ih
          by_cases hcurrent :
              decide (pair base (List.replicate limit true)) = true
          · simp [firstAcceptedBefore, hprevious, hcurrent]
            intro threshold hthreshold haccept
            rcases Nat.lt_or_eq_of_le hthreshold with
              hlt | rfl
            · have hfalse := ih threshold hlt
              exact (Bool.false_ne_true (hfalse.symm.trans haccept)).elim
            · exact le_rfl
          · have hcurrentFalse :
                decide (pair base (List.replicate limit true)) = false := by
              cases hvalue : decide (pair base (List.replicate limit true)) <;>
                simp_all
            simp [firstAcceptedBefore, hprevious, hcurrent]
            intro threshold hthreshold
            rcases Nat.lt_or_eq_of_le hthreshold with
              hlt | rfl
            · exact ih threshold hlt
            · exact hcurrentFalse
      | some first =>
          rw [hprevious] at ih
          rcases ih with ⟨hfirst, haccept, hminimal⟩
          simp only [firstAcceptedBefore, hprevious]
          exact ⟨by omega, haccept, fun threshold hthreshold hthresholdAccept => by
            by_cases hlt : threshold < limit
            · exact hminimal threshold hlt hthresholdAccept
            · omega⟩

private theorem sweepStep_stateAt (decide : List Bool → Bool)
    (base : List Bool) (iterations : ℕ) :
    sweepStep decide (stateAt decide base iterations) =
      stateAt decide base (iterations + 1) := by
  cases hresult : firstAcceptedBefore decide base iterations with
  | none =>
      by_cases haccept :
          decide (pair base (List.replicate iterations true)) = true
      · simp [stateAt, sweepStep, firstAcceptedBefore, hresult, haccept,
          chooseHead, List.replicate_succ]
      · simp [stateAt, sweepStep, firstAcceptedBefore, hresult, haccept,
          chooseHead, List.replicate_succ]
  | some threshold =>
      simp [stateAt, sweepStep, firstAcceptedBefore, hresult, chooseHead,
        List.replicate_succ]

private theorem sweepStep_iterate_init (decide : List Bool → Bool)
    (base : List Bool) (iterations : ℕ) :
    (sweepStep decide)^[iterations] (sweepInit base) =
      stateAt decide base iterations := by
  induction iterations with
  | zero => simp [sweepInit, stateAt, firstAcceptedBefore]
  | succ iterations ih =>
      rw [Function.iterate_succ_apply', ih,
        sweepStep_stateAt decide base iterations]

private theorem sweepStep_mem_FP (decide : List Bool → Bool)
    (hdecide : (fun bits => [decide bits]) ∈ FP) :
    sweepStep decide ∈ FP := by
  have hfst : pairFst ∈ FP := Cobham.fstBlock_mem_FP
  have hsnd : pairSnd ∈ FP := Cobham.sndBlock_mem_FP
  have hcounter : (fun state => pairFst (pairSnd state)) ∈ FP :=
    mem_FP_comp hsnd hfst
  have hsndSnd : (fun state => pairSnd (pairSnd state)) ∈ FP :=
    mem_FP_comp hsnd hsnd
  have hfound :
      (fun state => pairFst (pairSnd (pairSnd state))) ∈ FP :=
    mem_FP_comp hsndSnd hfst
  have hbest :
      (fun state => pairSnd (pairSnd (pairSnd state))) ∈ FP :=
    mem_FP_comp hsndSnd hsnd
  have hquery :
      (fun state => pair (pairFst state) (pairFst (pairSnd state))) ∈ FP :=
    Cobham.pairFn_mem_FP hfst hcounter
  have haccepted : (fun state =>
      [decide (pair (pairFst state) (pairFst (pairSnd state)))]) ∈ FP := by
    exact mem_FP_comp hquery hdecide
  have hnextCounter :
      (fun state => true :: pairFst (pairSnd state)) ∈ FP := by
    exact mem_FP_comp hcounter (Cobham.cons_mem_FP true)
  have htrue : (fun _ : List Bool => [true]) ∈ FP := by
    exact mem_FP_comp Cobham.const_nil_mem_FP (Cobham.cons_mem_FP true)
  have hfirstChoice : (fun state => chooseHead
      [decide (pair (pairFst state) (pairFst (pairSnd state)))]
      (pairFst (pairSnd state))
      (pairSnd (pairSnd (pairSnd state)))) ∈ FP := by
    simpa [chooseHead, Cobham.selectHead] using
      Cobham.selectHeadFn_mem_FP haccepted hcounter hbest
  have hnextBest : (fun state => chooseHead
      (pairFst (pairSnd (pairSnd state)))
      (pairSnd (pairSnd (pairSnd state)))
      (chooseHead
        [decide (pair (pairFst state) (pairFst (pairSnd state)))]
        (pairFst (pairSnd state))
        (pairSnd (pairSnd (pairSnd state))))) ∈ FP := by
    simpa [chooseHead, Cobham.selectHead] using
      Cobham.selectHeadFn_mem_FP hfound hbest hfirstChoice
  have hnextFound : (fun state => chooseHead
      (pairFst (pairSnd (pairSnd state))) [true]
      [decide (pair (pairFst state) (pairFst (pairSnd state)))]) ∈ FP := by
    simpa [chooseHead, Cobham.selectHead] using
      Cobham.selectHeadFn_mem_FP hfound htrue haccepted
  have hpacked := Cobham.pairFn_mem_FP hfst
    (Cobham.pairFn_mem_FP hnextCounter
      (Cobham.pairFn_mem_FP hnextFound hnextBest))
  exact hpacked

private theorem sweepInit_mem_FP : sweepInit ∈ FP := by
  have hnil : (fun _ : List Bool => ([] : List Bool)) ∈ FP :=
    Cobham.const_nil_mem_FP
  have hfalse : (fun _ : List Bool => [false]) ∈ FP := by
    exact mem_FP_comp hnil (Cobham.cons_mem_FP false)
  have hpacked := Cobham.pairFn_mem_FP id_mem_FP
    (Cobham.pairFn_mem_FP hnil
      (Cobham.pairFn_mem_FP hfalse Cobham.sndBlock_mem_FP))
  exact hpacked

private theorem sweepRuler_mem_FP : sweepRuler ∈ FP := by
  have h := mem_FP_comp Cobham.sndBlock_mem_FP
    (Cobham.cons_mem_FP false)
  exact h

private theorem sweepWidth_mem_FP : sweepWidth ∈ FP := by
  have hbaseOne : (fun base : List Bool => true :: base) ∈ FP := by
    simpa [Function.comp] using mem_FP_comp id_mem_FP
      (Cobham.cons_mem_FP true)
  have hbaseTwo : (fun base : List Bool => true :: true :: base) ∈ FP := by
    exact mem_FP_comp hbaseOne (Cobham.cons_mem_FP true)
  have hclockOne :
      (fun base : List Bool => true :: pairSnd base) ∈ FP := by
    exact mem_FP_comp Cobham.sndBlock_mem_FP (Cobham.cons_mem_FP true)
  have hpacked := Cobham.pairFn_mem_FP hbaseTwo
    (Cobham.pairFn_mem_FP hclockOne hclockOne)
  exact hpacked

private theorem sweep_iterate_length_le_width (decide : List Bool → Bool)
    (base : List Bool) (iterations : ℕ)
    (hiterations : iterations ≤ (sweepRuler base).length) :
    ((sweepStep decide)^[iterations] (sweepInit base)).length ≤
      (sweepWidth base).length := by
  rw [sweepStep_iterate_init]
  cases hresult : firstAcceptedBefore decide base iterations with
  | none =>
      simp [stateAt, hresult, sweepWidth, sweepRuler] at hiterations ⊢
      omega
  | some first =>
      have hspec := firstAcceptedBefore_spec decide base iterations
      rw [hresult] at hspec
      simp [stateAt, hresult, sweepWidth, sweepRuler] at hiterations ⊢
      omega

theorem encodedTimeSearchEstimator_mem_FP_internal
    (decide : List Bool → Bool)
    (hdecide : (fun bits => [decide bits]) ∈ FP) :
    encodedTimeSearchEstimator decide ∈ FP := by
  have hiter := Cobham.iterate_mem_FP
    (sweepStep_mem_FP decide hdecide) sweepInit_mem_FP
    sweepRuler_mem_FP sweepWidth_mem_FP
    (sweep_iterate_length_le_width decide)
  have hsndSnd : (fun state => pairSnd (pairSnd state)) ∈ FP :=
    mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP
  have hbest :
      (fun state => pairSnd (pairSnd (pairSnd state))) ∈ FP :=
    mem_FP_comp hsndSnd Cobham.sndBlock_mem_FP
  have hout := mem_FP_comp hiter hbest
  exact hout

theorem encodedTimeSearchEstimator_encode_internal
    (decide : List Bool → Bool) (inst : MINKT.Instance) :
    encodedTimeSearchEstimator decide inst.encode =
      List.replicate (timeSearchEstimator decide inst) true := by
  have hclock : pairSnd inst.encode =
      List.replicate inst.time true := by
    simp [MINKT.Instance.encode, MINKT.Instance.unaryClock]
  have hruler : (sweepRuler inst.encode).length = inst.time + 1 := by
    simp [sweepRuler, hclock]
  change pairSnd (pairSnd (pairSnd
    ((sweepStep decide)^[(sweepRuler inst.encode).length]
      (sweepInit inst.encode)))) = _
  rw [hruler, sweepStep_iterate_init]
  cases hresult : firstAcceptedBefore decide inst.encode (inst.time + 1) with
  | none =>
      have hscan := firstAcceptedBefore_spec
        decide inst.encode (inst.time + 1)
      rw [hresult] at hscan
      have hfind : (Fin.find? fun threshold : Fin (inst.time + 1) =>
          decide (thresholdInstance inst threshold.val).encode) = none := by
        rw [Fin.find?_eq_dite]
        split
        · rename_i hexists
          obtain ⟨threshold, haccept⟩ := hexists
          have hreject := hscan threshold.val threshold.isLt
          have haccept' : decide (pair inst.encode
              (List.replicate threshold.val true)) = true := by
            simpa [thresholdInstance_encode] using haccept
          exact (Bool.false_ne_true (hreject.symm.trans haccept')).elim
        · rfl
      simp [stateAt, hresult, timeSearchEstimator, estimatorOfSolver,
        firstAcceptedThreshold, hfind, hclock]
  | some first =>
      have hscan := firstAcceptedBefore_spec
        decide inst.encode (inst.time + 1)
      rw [hresult] at hscan
      have hfirstLe : first ≤ inst.time := by omega
      have hfirstAccept :
          decide (thresholdInstance inst first).encode = true := by
        simpa [thresholdInstance_encode] using hscan.2.1
      have hsearch := firstAcceptedThreshold_spec_of_accepted_internal
        decide inst hfirstLe hfirstAccept
      have hsearchAccept : decide
          (thresholdInstance inst (timeSearchEstimator decide inst)).encode =
            true := by
        simpa [timeSearchEstimator, estimatorOfSolver] using hsearch.1
      have hsearchLe : timeSearchEstimator decide inst ≤ first := by
        simpa [timeSearchEstimator, estimatorOfSolver] using hsearch.2
      have hsearchLt : timeSearchEstimator decide inst < inst.time + 1 :=
        lt_of_le_of_lt hsearchLe hscan.1
      have hsearchAccept' : decide (pair inst.encode
          (List.replicate (timeSearchEstimator decide inst) true)) = true := by
        simpa [thresholdInstance_encode] using hsearchAccept
      have hfirstLeSearch : first ≤ timeSearchEstimator decide inst :=
        hscan.2.2 _ hsearchLt hsearchAccept'
      have heq : timeSearchEstimator decide inst = first :=
        Nat.le_antisymm hsearchLe hfirstLeSearch
      have hreplicate := congrArg
        (fun threshold => List.replicate threshold true) heq.symm
      simpa [stateAt, hresult] using hreplicate

theorem encodedTimeSearchEstimator_length_encode_internal
    (decide : List Bool → Bool) (inst : MINKT.Instance) :
    (encodedTimeSearchEstimator decide inst.encode).length =
      timeSearchEstimator decide inst := by
  have hlength := congrArg List.length
    (encodedTimeSearchEstimator_encode_internal decide inst)
  simpa using hlength

theorem executableEstimator_eq_timeSearchEstimator_internal
    (decide : List Bool → Bool) :
    executableEstimator decide = timeSearchEstimator decide := by
  funext inst
  exact encodedTimeSearchEstimator_length_encode_internal decide inst

theorem fp_and_satisfiesBoundsOn_printerClock_internal
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    (huniversal : machine.IsEfficientlyUniversal)
    {decide : List Bool → Bool}
    (hdecide : (fun bits => [decide bits]) ∈ FP)
    (haccept : ∀ bits ∈ yesLanguage machine, decide bits = true)
    (hreject : ∀ bits ∈ noLanguage machine parameters,
      decide bits = false) :
    ∃ coefficient exponent,
      encodedTimeSearchEstimator decide ∈ FP ∧
        (executableEstimator decide).SatisfiesBoundsOn machine parameters
          (fun inst => coefficient *
            (2 * inst.output.length + 3) ^ exponent ≤ inst.time) := by
  obtain ⟨constant, coefficient, exponent, hprinter⟩ :=
    huniversal.timeBoundedKolmogorovComplexity_printer
  refine ⟨coefficient, exponent,
    encodedTimeSearchEstimator_mem_FP_internal decide hdecide, ?_⟩
  rw [executableEstimator_eq_timeSearchEstimator_internal]
  apply timeSearchEstimator_satisfiesBoundsOn_internal haccept hreject
  intro inst heligible
  exact ne_top_of_le_ne_top
    (show ((inst.output.length + constant : ℕ) : WithTop ℕ) ≠ ⊤ from
      WithTop.coe_ne_top)
    (hprinter inst.output inst.time heligible)

end Efficient

end Logarithmic

end GapMINKT

end Complexity

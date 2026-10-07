/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeInputGuardLength
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeUnaryCompare
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageParser
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: tape input guard

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeInputGuard.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeInputGuard

open TapeMultiProgram TapeRouting TapeUnary

/-- Read whether the unary comparison returned strictly greater. -/
def positiveResult : TapeUnaryCompare.State → Bool
  | .done o => decide (o = .gt)
  | _ => false

/-- Read whether the unary comparison returned greater or equal. -/
def atLeastResult : TapeUnaryCompare.State → Bool
  | .done o => decide (o ≠ .lt)
  | _ => false

/-- Read whether the unary comparison returned less or equal. -/
def atMostResult : TapeUnaryCompare.State → Bool
  | .done o => decide (o ≠ .gt)
  | _ => false

@[simp] theorem positiveResult_result (d : ℕ) :
    positiveResult (.done (TapeUnaryCompareScan.result d 0)) = decide (0 < d) := by
  simp [positiveResult, TapeUnaryCompareScan.result_eq_gt_iff]

@[simp] theorem atLeastResult_result (t : ℕ) :
    atLeastResult (.done (TapeUnaryCompareScan.result t 2)) = decide (2 ≤ t) := by
  simp [atLeastResult, TapeUnaryCompareScan.result_eq_lt_iff]
  omega

@[simp] theorem atMostResult_result (L n : ℕ) :
    atMostResult (.done (TapeUnaryCompareScan.result L n)) = decide (L ≤ n) := by
  simp [atMostResult, TapeUnaryCompareScan.result_eq_gt_iff]

/-- Control states for the check stage of the input guard routine. -/
inductive CheckState where
  | data (q : TapeUnaryCompare.State)
  | order (dataOK : Bool) (q : TapeUnaryCompare.State)
  | space (smallOK : Bool) (q : TapeUnaryCompare.State)
  | clear (accepted : Bool) (q : TapeErase.State)
  | done (accepted : Bool)
  deriving DecidableEq, Fintype

/-- Transition function for the check stage of the input guard routine. -/
def checkProgram : TapeMultiProgram CheckState
  | .data q, h =>
      match TapeUnaryCompare.program 2 5 q h with
      | some out => some (.data out.1, out.2)
      | none => jump (.order (positiveResult q) (.scan .beginR)) h
  | .order b q, h =>
      match TapeUnaryCompare.program 4 6 q h with
      | some out => some (.order b out.1, out.2)
      | none => jump (.space (b && atLeastResult q) (.scan .beginR)) h
  | .space b q, h =>
      match TapeUnaryCompare.program 8 1 q h with
      | some out => some (.space b out.1, out.2)
      | none => jump (.clear (b && atMostResult q) .start) h
  | .clear b q, h =>
      match TapeErase.code 6 q h with
      | some out => some (.clear b out.1, out.2)
      | none => jump (.done b) h
  | .done _, _ => none

/-- Initial control state of the check stage of the input guard routine. -/
def checkStart : CheckState := .data (.scan .beginR)

theorem runs_checks (σ : TapeStore) (n d t L : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = List.replicate d true)
    (h4 : σ 4 = List.replicate t true) (h5 : σ 5 = [])
    (h6 : σ 6 = List.replicate 2 true) (h8 : σ 8 = List.replicate L true) :
    RunsIn checkProgram.step (cfg checkStart (storeTapes σ))
      (cfg (.done (decide (0 < d ∧ 2 ≤ t ∧ L ≤ n)))
        (storeTapes (Function.update σ 6 []))) (4*n+42) := by
  let od := TapeUnaryCompareScan.result d 0
  let ot := TapeUnaryCompareScan.result t 2
  let oL := TapeUnaryCompareScan.result L n
  let bd := positiveResult (.done od)
  let bt := bd && atLeastResult (.done ot)
  let bL := bt && atMostResult (.done oL)
  have hd := TapeUnaryCompare.runs_compare (r := 2) (s := 5) (by decide)
    (storeTapes σ) d 0 (by simp [storeTapes, h2]) (by simp [storeTapes, h5])
  simp only [Nat.min_zero, Nat.mul_zero, Nat.zero_add] at hd
  have hd' := runs_map (TapeUnaryCompare.program 2 5) checkProgram CheckState.data (by
    intro q h q' writes moves he
    simp only [checkProgram, he]) hd
  have hdl := RunsIn.single (step_jump checkProgram (.data (.done od))
    (.order bd (.scan .beginR)) (storeTapes σ) rfl)
  have ht := TapeUnaryCompare.runs_compare (r := 4) (s := 6) (by decide)
    (storeTapes σ) t 2 (by simp [storeTapes, h4]) (by simp [storeTapes, h6])
  have ht0 := ht.mono (show 4 * min t 2 + 7 ≤ 15 by
    have hm := Nat.min_le_right t 2
    omega)
  have ht' := runs_map (TapeUnaryCompare.program 4 6) checkProgram (CheckState.order bd) (by
    intro q h q' writes moves he
    simp only [checkProgram, he]) ht0
  have htl := RunsIn.single (step_jump checkProgram (.order bd (.done ot))
    (.space bt (.scan .beginR)) (storeTapes σ) rfl)
  have hL := TapeUnaryCompare.runs_compare (r := 8) (s := 1) (by decide)
    (storeTapes σ) L n (by simp [storeTapes, h8]) (by simp [storeTapes, h1])
  have hL0 := hL.mono (show 4 * min L n + 7 ≤ 4*n+7 by
    have hm := Nat.min_le_right L n
    omega)
  have hL' := runs_map (TapeUnaryCompare.program 8 1) checkProgram (CheckState.space bt) (by
    intro q h q' writes moves he
    simp only [checkProgram, he]) hL0
  have hLl := RunsIn.single (step_jump checkProgram (.space bt (.done oL))
    (.clear bL .start) (storeTapes σ) rfl)
  have he := TapeStoreRuns.erase 6 σ
  simp only [h6, List.length_replicate] at he
  have he' := runs_map (TapeErase.code 6) checkProgram (CheckState.clear bL) (by
    intro q h q' writes moves heq
    simp only [checkProgram, heq]) he
  have hel := RunsIn.single (step_jump checkProgram (.clear bL .done) (.done bL)
    (storeTapes (Function.update σ 6 [])) rfl)
  have hall := ((((((hd'.trans hdl).trans ht').trans htl).trans hL').trans hLl).trans he').trans hel
  have hb : bL = decide (0 < d ∧ 2 ≤ t ∧ L ≤ n) := by
    simp [bL, bt, bd, od, ot, oL, Bool.and_assoc]
  have hc : ((((((7+1)+15)+1)+(4*n+7))+1)+(2*2+5))+1 = 4*n+42 := by omega
  simpa only [mapCfg, cfg, checkStart, hb, hc] using hall

/-- Control states for the two stage of the input guard routine. -/
abbrev TwoState := IncState ⊕ IncState
/-- Transition function for the two stage of the input guard routine. -/
def twoProgram : TapeMultiProgram TwoState :=
  joinCode (incProgram 6) (incProgram 6) (fun _ => IncState.start)
/-- Initial control state of the two stage of the input guard routine. -/
def twoStart : TwoState := .inl .start
/-- Terminal control state of the two stage of the input guard routine. -/
def twoDone : TwoState := .inr .done

theorem runs_two (σ : TapeStore) (h6 : σ 6 = []) :
    RunsIn twoProgram.step (cfg twoStart (storeTapes σ))
      (cfg twoDone (storeTapes (Function.update σ 6 (List.replicate 2 true)))) 5 := by
  let σ1 := Function.update σ 6 (List.replicate 1 true)
  have h1 := increment 6 (storeTapes σ) 0 (by simp [storeTapes, counterTape, h6])
  have h1' : RunsIn (incProgram 6).step (cfg IncState.start (storeTapes σ))
      (cfg IncState.done (storeTapes σ1)) 2 := by
    simpa only [σ1, storeTapes_update, counterTape] using h1
  have h2 := increment 6 (storeTapes σ1) 1 (by simp [σ1, storeTapes, counterTape])
  have h2' : RunsIn (incProgram 6).step (cfg IncState.start (storeTapes σ1))
      (cfg IncState.done (storeTapes (Function.update σ 6 (List.replicate 2 true)))) 2 := by
    simpa only [σ1, ← storeTapes_update, counterTape, Function.update_idem] using h2
  exact join_runs (incProgram 6) (incProgram 6) (fun _ => IncState.start) h1' rfl h2'

/-- Control states for the test stage of the input guard routine. -/
abbrev TestState := TwoState ⊕ CheckState
/-- Transition function for the test stage of the input guard routine. -/
def testProgram : TapeMultiProgram TestState :=
  joinCode twoProgram checkProgram (fun _ => checkStart)
/-- Initial control state of the test stage of the input guard routine. -/
def testStart : TestState := .inl twoStart
/-- Terminal control state of the test stage of the input guard routine. -/
def testDone (b : Bool) : TestState := .inr (.done b)

theorem runs_test (σ : TapeStore) (n d t L : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = List.replicate d true)
    (h4 : σ 4 = List.replicate t true) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h8 : σ 8 = List.replicate L true) :
    RunsIn testProgram.step (cfg testStart (storeTapes σ))
      (cfg (testDone (decide (0 < d ∧ 2 ≤ t ∧ L ≤ n))) (storeTapes σ)) (4*n+48) := by
  let τ := Function.update σ 6 (List.replicate 2 true)
  have htwo := runs_two σ h6
  have hc := runs_checks τ n d t L (by simp [τ, h1]) (by simp [τ, h2])
    (by simp [τ, h4]) (by simp [τ, h5]) (by simp [τ]) (by simp [τ, h8])
  have hrestore : Function.update τ 6 [] = σ := by
    dsimp [τ]
    rw [Function.update_idem, ← h6, Function.update_eq_self]
  rw [hrestore] at hc
  have h := join_runs twoProgram checkProgram (fun _ => checkStart) htwo rfl hc
  have ht : 5+1+(4*n+42) = 4*n+48 := by omega
  simpa only [testProgram, testStart, testDone, ht] using h

/-- Control states of the input guard routine. -/
abbrev State := LengthState ⊕ TestState
/-- Transition function of the input guard routine. -/
def program : TapeMultiProgram State :=
  joinCode lengthProgram testProgram (fun _ => testStart)
/-- Initial control state of the input guard routine. -/
def start : State := .inl lengthStart
/-- Terminal control state of the input guard routine. -/
def done (accepted : Bool) : State := .inr (testDone accepted)

/-- Transition budget for the input guard routine. -/
def cost (n d r t : ℕ) : ℕ := lengthCost d r t + 4*n + 49

theorem cost_eq (n d r t : ℕ) :
    cost n d r t = 12*d + 20*r + 16*t + 10*(t*r) + 4*n + 94 := by
  unfold cost lengthCost
  omega

theorem cost_le_square (n d r t : ℕ) (hd : d ≤ n+1) (hr : r ≤ n+1) (ht : t ≤ n+1) :
    cost n d r t ≤ 200 * (n+1)^2 := by
  rw [cost_eq]
  have hm : t*r ≤ (n+1)*(n+1) := Nat.mul_le_mul ht hr
  nlinarith

theorem cost_parameters_le (n : ℕ) :
    cost n (dataDimension n) (hashDimension (dataDimension n))
      (independenceOrder (dataDimension n)) ≤ 200 * (n+1)^2 := by
  have hd : dataDimension n ≤ n+1 := by unfold dataDimension; omega
  exact cost_le_square n _ _ _ hd ((hashDimension_le _).trans hd)
    ((independenceOrder_le _).trans hd)

theorem runs_guard (σ : TapeStore) (n d r t : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = List.replicate d true)
    (h3 : σ 3 = List.replicate r true) (h4 : σ 4 = List.replicate t true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (decide (0 < d ∧ 2 ≤ t ∧ requiredLength d r t ≤ n)))
        (storeTapes (outputStore σ d r t))) (cost n d r t) := by
  have hl := runs_length σ d r t h2 h3 h4 h5 h6 h8
  have ht := runs_test (outputStore σ d r t) n d t (requiredLength d r t)
    (by simp [outputStore, h1]) (by simp [outputStore, h2])
    (by simp [outputStore, h4]) (by simp [outputStore, h5])
    (by simp [outputStore, h6]) (by simp [outputStore])
  have h := join_runs lengthProgram testProgram (fun _ => testStart) hl rfl ht
  have hc : lengthCost d r t + 1 + (4*n+48) = cost n d r t := by
    unfold cost
    omega
  simpa only [program, start, done, hc] using h

theorem runs_inputFits (w : List Bool) (σ : TapeStore)
    (h1 : σ 1 = List.replicate w.length true)
    (h2 : σ 2 = List.replicate (dataDimension w.length) true)
    (h3 : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (h4 : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (decide (InputFits w)))
        (storeTapes (outputStore σ (dataDimension w.length)
          (hashDimension (dataDimension w.length)) (independenceOrder (dataDimension w.length)))))
      (cost w.length (dataDimension w.length) (hashDimension (dataDimension w.length))
        (independenceOrder (dataDimension w.length))) := by
  have hguard : decide (InputFits w) =
      decide (0 < dataDimension w.length ∧
        2 ≤ independenceOrder (dataDimension w.length) ∧
        requiredLength (dataDimension w.length) (hashDimension (dataDimension w.length))
          (independenceOrder (dataDimension w.length)) ≤ w.length) := by
    apply decide_eq_decide.mpr
    simp only [InputFits, requiredLength_parameters]
  rw [hguard]
  exact runs_guard σ w.length (dataDimension w.length) (hashDimension (dataDimension w.length))
    (independenceOrder (dataDimension w.length)) h1 h2 h3 h4 h5 h6 h8

theorem runs_inputFits_quadratic (w : List Bool) (σ : TapeStore)
    (h1 : σ 1 = List.replicate w.length true)
    (h2 : σ 2 = List.replicate (dataDimension w.length) true)
    (h3 : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (h4 : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (decide (InputFits w)))
        (storeTapes (outputStore σ (dataDimension w.length)
          (hashDimension (dataDimension w.length)) (independenceOrder (dataDimension w.length)))))
      (200 * (w.length+1)^2) :=
  (runs_inputFits w σ h1 h2 h3 h4 h5 h6 h8).mono (cost_parameters_le w.length)

@[simp] theorem program_done (b : Bool) (h : TapeHeads) : program (done b) h = none := rfl

end TapeInputGuard
end DepthThreeLowerBound

end Complexity

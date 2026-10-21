/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.FP

/-!
# Canonical TM2-to-FP API checks

Only the public surface is imported. A one-step stack program prepends a bit;
its certificate covers every word, including empty input, and needs no separate
output-length certificate. Prepending also distinguishes the two string orders.
-/

namespace Complexity.TM2FPApiCheck

open Turing

/-- The one-stack identity machine with one push before halting. -/
def prependMachine : FinTM2 :=
  { idComputer Bool with m := fun _ => .push () (fun _ => false) .halt }

/-- A source certificate for prepending a bit on every binary string. -/
noncomputable def prependComputer :
    TM2ComputableInPolyTime id id (fun w : List Bool => false :: w) where
  tm := prependMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun _ := ⟨⟨1, rfl⟩, by simp⟩

example : (fun w : List Bool => false :: w) ∈ FP := by
  let : ∀ k, Fintype (prependComputer.tm.Γ k) := fun _ => by
    change Fintype Bool
    infer_instance
  exact MathlibTM2.mem_FP prependComputer

example : (fun w : List Bool => w) ∈ FP := by
  let computer := idComputableInPolyTime (fun w : List Bool => w)
  let : ∀ k, Fintype (computer.tm.Γ k) := fun _ => by
    change Fintype Bool
    infer_instance
  exact MathlibTM2.mem_FP computer

/-- A regular domain that is not invariant under reversal. -/
def startsTrue : DFA Bool (Option Bool) where
  step q b := match q with
    | none => some b
    | some x => some x
  start := none
  accept := {some true}

lemma startsTrue_accepts (w : List Bool) :
    w ∈ startsTrue.accepts ↔ w.head? = some true := by
  have stable (b : Bool) (bs : List Bool) : startsTrue.evalFrom (some b) bs = some b := by
    induction bs <;> simp_all [DFA.evalFrom_cons, DFA.evalFrom_nil, startsTrue]
  cases w with
  | nil => rfl
  | cons b bs =>
      change startsTrue.evalFrom (some b) bs = some true ↔ some b = some true
      rw [stable]

/-- On true-headed inputs prepend false; otherwise loop forever. -/
def partialMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .peek () (fun _ b => b.getD false)
    (.branch id (.load (fun _ => false) (.push () (fun _ => false) .halt))
      (.goto (fun _ => ())))

example (w : List Bool) (hw : w.head? ≠ some true) :
    partialMachine.step (initList partialMachine w) = some (initList partialMachine w) := by
  cases w with
  | nil => rfl
  | cons b bs =>
      cases b with
      | false => rfl
      | true => exact False.elim (hw rfl)

example : (fun w : List Bool => if w.head? = some true then false :: w else []) ∈ FP := by
  classical
  let computer : TM2ComputableAux Bool Bool :=
    ⟨partialMachine, Equiv.refl Bool, Equiv.refl Bool⟩
  let : ∀ k, Fintype (computer.tm.Γ k) := fun _ => by
    change Fintype Bool
    infer_instance
  have h : (fun w => if w ∈ startsTrue.accepts then false :: w else []) ∈ FP := by
    apply MathlibTM2.mem_FP_on_dfa computer startsTrue (p := 1)
    intro w hw
    have hh := (startsTrue_accepts w).mp hw
    cases w with
    | nil => simp at hh
    | cons b bs =>
        have hb : b = true := Option.some.inj hh
        subst b
        exact ⟨⟨1, rfl⟩, by simp⟩
  simpa only [startsTrue_accepts] using h

/-- Explicit four-letter code; the choice of numbering is visible to clients. -/
def fourCode : FiniteAlphabetCode (Fin 4) := ⟨4, Equiv.refl _⟩

/-- A different output alphabet with just one letter. -/
def oneCode : FiniteAlphabetCode (Fin 1) := ⟨1, Equiv.refl _⟩

example : fourCode.encode [0, 3, 1] =
    [false, false, false, true, true, true, false, false, true, false] := rfl

example : fourCode.decode [true] = none := rfl
example : fourCode.decode [false] = none := rfl
example : fourCode.decode [false, true, true, true, true, false] = none := rfl
example : fourCode.decode [] = some [] := rfl

example (xs : List (Fin 4)) : fourCode.decode (fourCode.encode xs) = some xs :=
  fourCode.decode_encode xs

/-- Prepending a nonzero letter distinguishes word reversal from symbol coding. -/
def prependFourMachine : FinTM2 :=
  { idComputer (Fin 4) with m := fun _ => .push () (fun _ => (3 : Fin 4)) .halt }

/-- A four-letter source certificate, with no encoded-output size premise. -/
noncomputable def prependFourComputer :
    TM2ComputableInPolyTime id id (fun xs : List (Fin 4) => 3 :: xs) where
  tm := prependFourMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 1
  outputsFun _ := ⟨⟨1, rfl⟩, by simp⟩

example : fourCode.map fourCode (fun xs => 3 :: xs) ∈ FP := by
  let : ∀ k, Fintype (prependFourComputer.tm.Γ k) := fun _ => by
    change Fintype (Fin 4)
    infer_instance
  exact MathlibTM2.mem_FP_encoded fourCode fourCode prependFourComputer

example : fourCode.map fourCode (fun xs => 3 :: xs) [true] = [] := rfl

/-- A domain sensitive to the second bit, hence to which end of the word is read first. -/
def secondTrue : DFA Bool (Option (Option Bool)) where
  step q b := match q with
    | none => some none
    | some none => some (some b)
    | some (some a) => some (some a)
  start := none
  accept := {some (some true)}

noncomputable instance : DecidablePred (· ∈ secondTrue.accepts) := Classical.decPred _

example :
    (fun bits => if bits ∈ secondTrue.accepts then
      fourCode.map fourCode (fun xs => 3 :: xs) bits else []) ∈ FP := by
  classical
  let computer : TM2ComputableAux (Fin 4) (Fin 4) :=
    ⟨prependFourMachine, Equiv.refl _, Equiv.refl _⟩
  let : ∀ k, Fintype (computer.tm.Γ k) := fun _ => by
    change Fintype (Fin 4)
    infer_instance
  exact MathlibTM2.mem_FP_encoded_on_dfa fourCode fourCode computer secondTrue
    (p := 1) (fun _ _ => ⟨⟨1, rfl⟩, by simp⟩)

/-- Clear a four-letter input stack, then return one letter on a different singleton stack. -/
public abbrev constantMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ k := match k with
    | false => Fin 4
    | true => Fin 1
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .pop false (fun _ a => a.isSome)
    (.branch id (.goto (fun _ => ())) (.push true (fun _ => (0 : Fin 1)) .halt))

/-- Source states while consuming the input. -/
def constantCfg (xs : List (Fin 4)) (v : Bool) : constantMachine.Cfg where
  l := some ()
  var := v
  stk k := match k with
    | false => xs
    | true => []

lemma constant_nil (v : Bool) :
    constantMachine.step (constantCfg [] v) = some (haltList constantMachine [(0 : Fin 1)]) := by
  apply congrArg some
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

lemma constant_cons (a : Fin 4) (xs : List (Fin 4)) (v : Bool) :
    constantMachine.step (constantCfg (a :: xs) v) = some (constantCfg xs true) := by
  apply congrArg some
  change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
  congr 1
  funext k
  cases k <;> rfl

lemma constant_iterate (xs : List (Fin 4)) (v : Bool) :
    (fun s : Option constantMachine.Cfg => s.bind constantMachine.step)^[xs.length + 1]
      (some (constantCfg xs v)) = some (haltList constantMachine [(0 : Fin 1)]) := by
  induction xs generalizing v with
  | nil => exact constant_nil v
  | cons a xs ih =>
      change (fun s : Option constantMachine.Cfg => s.bind constantMachine.step)^[xs.length + 1 + 1]
        (some (constantCfg (a :: xs) v)) = _
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some, constant_cons]
      exact ih true

/-- A polynomial source certificate whose input and output alphabet sizes differ. -/
noncomputable def constantComputer :
    TM2ComputableInPolyTime id id (fun _ : List (Fin 4) => [(0 : Fin 1)]) where
  tm := constantMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun xs := by
    refine ⟨⟨xs.length + 1, ?_⟩, by simp⟩
    have hi : initList constantMachine xs = constantCfg xs false := by
      change TM2.Cfg.mk _ _ _ = TM2.Cfg.mk _ _ _
      congr 1
      funext k
      cases k <;> rfl
    simp only [Equiv.refl, id_eq, Option.map_some]
    change (fun s : Option constantMachine.Cfg => s.bind constantMachine.step)^[xs.length + 1]
      (some (initList constantMachine (xs.map (@id (Fin 4))))) =
        some (haltList constantMachine [(0 : Fin 1)])
    rw [List.map_id, hi]
    exact constant_iterate xs false

example : fourCode.map oneCode (fun _ => [(0 : Fin 1)]) ∈ FP := by
  let : ∀ k, Fintype (constantComputer.tm.Γ k) := fun k => by
    change Fintype (constantMachine.Γ k)
    cases k with
    | false => change Fintype (Fin 4); infer_instance
    | true => change Fintype (Fin 1); infer_instance
  exact MathlibTM2.mem_FP_encoded fourCode oneCode constantComputer

example : fourCode.map oneCode (fun _ => [(0 : Fin 1)]) [] = [false, false] := rfl
example : fourCode.map oneCode (fun _ => [(0 : Fin 1)]) [false] = [] := rfl

example :
    (FiniteAlphabetCode.ofFintype Empty).map (FiniteAlphabetCode.ofFintype Empty)
      (fun xs => xs) ∈ FP := by
  let computer := idComputableInPolyTime (fun xs : List Empty => xs)
  let : ∀ k, Fintype (computer.tm.Γ k) := fun _ => by
    change Fintype Empty
    infer_instance
  exact MathlibTM2.mem_FP_encoded _ _ computer

end Complexity.TM2FPApiCheck

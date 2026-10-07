/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.TaylorComputation

/-!
# Rational hitting lists: lift computation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/LiftComputation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open scoped BigOperators
namespace Runtime

/-- The signed entry of the cyclotomic multiplication representation. -/
def signed (q z i j : ℕ) : ℤ :=
  if (z+j)%q=i then (-1)^((z+j)/q) else 0

/-- One integer summand in the finite Fourier lift. -/
def liftTerm (m N q : ℕ) (a t p r : ℤ) (u v i j x y k : ℕ) : ℤ :=
  if u=(v+y)%m then
    padded m N a t k ((k+(m-y)%m)%m)*
      signed q (((m-(x*k)%m)%m+(x*u)%m)%m) i j*p^x*r^y
  else 0

/-- The integer lift obtained by summing the Fourier terms. -/
def lift (m N q : ℕ) (a t p r : ℤ) (u v i j : ℕ) : ℤ :=
  ((List.range m).map (fun x =>
    ((List.range m).map (fun y =>
      ((List.range m).map (fun k => liftTerm m N q a t p r u v i j x y k)).sum)).sum)).sum

/-- An entry of the complete integral regular representation. -/
def entry (m N q : ℕ) (a t p r : ℤ) (I J : ℕ) : ℤ :=
  lift m N q a t p r (I/q) (J/q) (I%q) (J%q)

/-- Encoded parameters for an integral Fourier lift. -/
abbrev LiftArgs := (Unary×Unary×Unary)×(ℤ×ℤ×ℤ×ℤ)×(Unary×Unary×Unary×Unary)
/-- Encoded parameters and summation indices for one lift term. -/
abbrev LiftTermArgs := ((LiftArgs×Unary)×Unary)×Unary

@[fun_prop] theorem signed_poly : Poly (fun a : (Unary×Unary)×(Unary×Unary) =>
    signed a.1.1.val a.1.2.val a.2.1.val a.2.2.val) := by
  have hc : Poly (fun a : (Unary×Unary)×(Unary×Unary) =>
    Unary.eqb ((a.1.2+a.2.2)%a.1.1) a.2.1) := by fun_prop
  have hf : Poly (fun a : (Unary×Unary)×(Unary×Unary) =>
    Unary.powInt (-1) ((a.1.2+a.2.2)/a.1.1)) := by fun_prop
  exact (hc.cond hf (Poly.const 0)).of_eq (by intro a;simp only [Unary.eqb,decide_eq_true_eq];rfl)

@[fun_prop] theorem liftTerm_poly : Poly (fun a : LiftTermArgs =>
    liftTerm a.1.1.1.1.1.val a.1.1.1.1.2.1.val a.1.1.1.1.2.2.val
      a.1.1.1.2.1.1 a.1.1.1.2.1.2.1 a.1.1.1.2.1.2.2.1 a.1.1.1.2.1.2.2.2
      a.1.1.1.2.2.1.val a.1.1.1.2.2.2.1.val a.1.1.1.2.2.2.2.1.val a.1.1.1.2.2.2.2.2.val
      a.1.1.2.val a.1.2.val a.2.val) := by
  let pars (a : LiftTermArgs) : Unary×TaylorArgs :=
    (a.1.1.1.1.2.1,a.1.1.1.1.1,a.1.1.1.2.1.1,a.1.1.1.2.1.2.1,a.2,
      (a.2+(a.1.1.1.1.1-a.1.2)%a.1.1.1.1.1)%a.1.1.1.1.1)
  have hpars : Poly pars := by unfold pars;fun_prop
  have ht := padded_poly.comp hpars
  let sp (a : LiftTermArgs) : (Unary×Unary)×(Unary×Unary) :=
    ((a.1.1.1.1.2.2,((a.1.1.1.1.1-(a.1.1.2*a.2)%a.1.1.1.1.1)%a.1.1.1.1.1+
      (a.1.1.2*a.1.1.1.2.2.1)%a.1.1.1.1.1)%a.1.1.1.1.1),
      (a.1.1.1.2.2.2.2.1,a.1.1.1.2.2.2.2.2))
  have hsp : Poly sp := by unfold sp;fun_prop
  have hs := signed_poly.comp hsp
  have hp : Poly (fun a : LiftTermArgs => Unary.powInt a.1.1.1.2.1.2.2.1 a.1.1.2) := by fun_prop
  have hr : Poly (fun a : LiftTermArgs => Unary.powInt a.1.1.1.2.1.2.2.2 a.1.2) := by fun_prop
  have hv := Poly.intMul.comp ((Poly.intMul.comp ((Poly.intMul.comp (ht.pair hs)).pair hp)).pair hr)
  have hc : Poly (fun a : LiftTermArgs =>
    Unary.eqb a.1.1.1.2.2.1 ((a.1.1.1.2.2.2.1+a.1.2)%a.1.1.1.1.1)) := by fun_prop
  exact (hc.cond hv (Poly.const 0)).of_eq (by intro a;simp only [Unary.eqb,decide_eq_true_eq];rfl)

@[fun_prop] theorem lift_poly : Poly (fun a : LiftArgs =>
    lift a.1.1.val a.1.2.1.val a.1.2.2.val
      a.2.1.1 a.2.1.2.1 a.2.1.2.2.1 a.2.1.2.2.2
      a.2.2.1.val a.2.2.2.1.val a.2.2.2.2.1.val a.2.2.2.2.2.val) := by
  have h1 := Poly.sumUp (show Poly (fun a : (LiftArgs×Unary)×Unary => a.1.1.1.1) by fun_prop)
    liftTerm_poly
  have h2 := Poly.sumUp (show Poly (fun a : LiftArgs×Unary => a.1.1.1) by fun_prop) h1
  exact Poly.sumUp (show Poly (fun a : LiftArgs => a.1.1) by fun_prop) h2

/-- Encoded parameters for one entry of the integral representation. -/
abbrev EntryArgs := (Unary×Unary×Unary)×(ℤ×ℤ×ℤ×ℤ)×(Unary×Unary)
@[fun_prop] theorem entry_poly : Poly (fun a : EntryArgs =>
    entry a.1.1.val a.1.2.1.val a.1.2.2.val
      a.2.1.1 a.2.1.2.1 a.2.1.2.2.1 a.2.1.2.2.2 a.2.2.1.val a.2.2.2.val) := by
  exact lift_poly.comp (show Poly (fun a : EntryArgs =>
    (a.1,a.2.1,(a.2.2.1/a.1.2.2,a.2.2.2/a.1.2.2,a.2.2.1%a.1.2.2,a.2.2.2%a.1.2.2))) by fun_prop)

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open scoped BigOperators

lemma range_sum_zmod_val {A : Type} [AddCommMonoid A] (m : ℕ) [NeZero m] (f : ℕ → A) :
    ((List.range m).map f).sum=∑ z : ZMod m, f z.val := by
  rw [range_sum_fin]
  exact Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ (fun i => by
    change f i.val=f ((ZMod.finEquiv m) i).val
    rw [finEquiv_val])

namespace Runtime
lemma signed_eq (e : ℕ) (z : ZMod (CyclotomicRing.dimension e))
    (i j : Fin (CyclotomicRing.degree e)) :
    signed (CyclotomicRing.degree e) z.val i.val j.val = CyclotomicRing.signedEntry e z i j := rfl

lemma integerTest_apply (N e : ℕ) (a t : ℤ) (i j : ZMod (CyclotomicRing.dimension e)) :
    Generator.integerTest N e a t i j=
      padded (CyclotomicRing.dimension e) N a t i.val j.val := by
  change IntegralTest.padded _ _ _ _ ((ZMod.finEquiv _).symm i) ((ZMod.finEquiv _).symm j)=_
  rw [←padded_eq,finEquiv_symm_val,finEquiv_symm_val]

lemma liftTerm_eq (N e : ℕ) (a t p r : ℤ)
    (u v x y k : ZMod (CyclotomicRing.dimension e)) (i j : Fin (CyclotomicRing.degree e)) :
    liftTerm (CyclotomicRing.dimension e) N (CyclotomicRing.degree e) a t p r
      u.val v.val i.val j.val x.val y.val k.val =
      if u=v+y then Generator.integerTest N e a t k (k-y)*
        CyclotomicRing.signedEntry e (-x*k+x*u) i j*p^x.val*r^y.val else 0 := by
  have hz : (-x*k+x*u).val=
      (((CyclotomicRing.dimension e-(x.val*k.val)%CyclotomicRing.dimension
        e)%CyclotomicRing.dimension e+
        (x.val*u.val)%CyclotomicRing.dimension e)%CyclotomicRing.dimension e) := by
    rw [neg_mul,ZMod.val_add,ZMod.neg_val',ZMod.val_mul,ZMod.val_mul]
  unfold liftTerm
  simp only [←ZMod.val_add, (ZMod.val_injective _).eq_iff,←hz,←zmod_val_sub,signed_eq,
    ←integerTest_apply]

lemma lift_eq (N e : ℕ) (a t p r : ℤ)
    (u v : ZMod (CyclotomicRing.dimension e)) (i j : Fin (CyclotomicRing.degree e)) :
    lift (CyclotomicRing.dimension e) N (CyclotomicRing.degree e) a t p r
      u.val v.val i.val j.val=
      IntegralLift.entry e (Generator.integerTest N e a t) p r u v i j := by
  unfold lift IntegralLift.entry
  rw [range_sum_zmod_val]
  apply Finset.sum_congr rfl
  intro x _
  rw [range_sum_zmod_val]
  apply Finset.sum_congr rfl
  intro y _
  rw [range_sum_zmod_val]
  apply Finset.sum_congr rfl
  intro k _
  exact liftTerm_eq N e a t p r u v x y k i j

lemma entry_eq (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n+1)) (i j : Fin (Generator.matrixDimension
    e)) :
    entry (CyclotomicRing.dimension e) N (CyclotomicRing.degree e)
      a.val (x 0) (x 1) (x 2) i.val j.val = Generator.integralLift n N e x a i j := by
  have hi := coordinate_vals e i
  have hj := coordinate_vals e j
  have hi1 := congrArg Prod.fst hi
  have hi2 := congrArg Prod.snd hi
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  simp only [] at hi1 hi2 hj1 hj2
  unfold entry Generator.integralLift
  rw [←hi1,←hi2,←hj1,←hj2]
  exact lift_eq N e a.val (x 0) (x 1) (x 2) _ _ _ _

end Runtime
end RationalHitting.StackLanguage

end Complexity

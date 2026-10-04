/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Aggregate
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Boolean, modular, threshold, and symmetric aggregate gates

AND and OR use multiplication in the two-element ring as a commutative monoid.
Their zero updates are noninvertible. Modular gates instead use its additive
monoid (written multiplicatively through `Multiplicative`), with an arbitrary
Boolean predicate on the residue. Slot-dependent contributions allow weighted
modular sums. Saturating addition computes nonnegative weighted thresholds,
and an arity-capped counter computes every predicate of the Hamming weight.
Each operation has unrestricted finite fan-in.
-/

@[expose] public section

namespace Algebraic.Aggregate

/-- A two-state noncancellative aggregate computing conjunction. -/
def andGate (arity : Nat) : Op (fun _ : Unit => ZMod 2) :=
  .special () arity (fun _ b => if b then 1 else 0) (fun z => decide (z ≠ 0))

/-- A two-state noncancellative aggregate computing disjunction. -/
def orGate (arity : Nat) : Op (fun _ : Unit => ZMod 2) :=
  .special () arity (fun _ b => if b then 0 else 1) (fun z => decide (z = 0))

/-- Conjunction has the expected semantics, including its nullary value `true`. -/
theorem andGate_eval (arity : Nat) (x : Fin arity → Bool) :
    interpretation (andGate arity) x = decide (∀ i, x i = true) := by
  simp only [interpretation, andGate]
  congr 1
  rw [Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_implies]
  apply propext
  apply forall_congr'
  intro i
  cases x i <;> simp

/-- Disjunction has the expected semantics, including its nullary value `false`. -/
theorem orGate_eval (arity : Nat) (x : Fin arity → Bool) :
    interpretation (orGate arity) x = decide (∃ i, x i = true) := by
  simp only [interpretation, orGate]
  congr 1
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  apply propext
  apply exists_congr
  intro i
  cases x i <;> simp

/-- Any residue predicate on a slot-weighted modular sum is an aggregate gate. -/
def modularGate (modulus arity : Nat) (weight : Fin arity → ZMod modulus)
    (readout : ZMod modulus → Bool) : Op (fun _ : Unit => Multiplicative (ZMod modulus)) :=
  .special () arity (fun i b => Multiplicative.ofAdd (if b then weight i else 0))
    (fun z => readout z.toAdd)

/-- Modular gate evaluation is precisely the weighted modular sum. -/
theorem modularGate_eval (modulus arity : Nat) (weight : Fin arity → ZMod modulus)
    (readout : ZMod modulus → Bool) (x : Fin arity → Bool) :
    interpretation (modularGate modulus arity weight readout) x =
      readout (∑ i, if x i then weight i else 0) := by
  simp [interpretation, modularGate]

/-- AND uses two aggregate states regardless of its fan-in. -/
theorem card_andGate_register (arity : Nat) : Fintype.card (andGate arity).Register = 2 := by
  exact (Fintype.card_congr (Equiv.refl (ZMod 2))).trans (ZMod.card 2)

/-- OR uses two aggregate states regardless of its fan-in. -/
theorem card_orGate_register (arity : Nat) : Fintype.card (orGate arity).Register = 2 := by
  exact (Fintype.card_congr (Equiv.refl (ZMod 2))).trans (ZMod.card 2)

/-- A finite counter whose addition saturates at `cap`. -/
@[ext]
structure Capped (cap : Nat) where
  /-- The stored value lies between zero and the cap, inclusively. -/
  toFin : Fin (cap + 1)
  deriving DecidableEq

namespace Capped

/-- Capped counters enumerate exactly the integers from zero through the cap. -/
def equivFin (cap : Nat) : Capped cap ≃ Fin (cap + 1) where
  toFun := Capped.toFin
  invFun := Capped.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance (cap : Nat) : Fintype (Capped cap) :=
  Fintype.ofEquiv (Fin (cap + 1)) (equivFin cap).symm

/-- The natural number stored in a capped counter. -/
def val {cap : Nat} (x : Capped cap) : Nat := x.toFin.val

/-- Insert a natural number, saturating at the cap. -/
def ofNat (cap value : Nat) : Capped cap :=
  ⟨⟨min cap value, Nat.lt_succ_of_le (min_le_left _ _)⟩⟩

/-- Equality of capped counters is equality of their stored values. -/
theorem ext_val {cap : Nat} {x y : Capped cap} (h : x.val = y.val) : x = y :=
  Capped.ext (Fin.ext h)

/-- Capped addition, written multiplicatively for the aggregate interface. -/
instance (cap : Nat) : CommMonoid (Capped cap) where
  one := ofNat cap 0
  mul x y := ofNat cap (x.val + y.val)
  mul_assoc x y z := by
    apply ext_val
    change min cap (min cap (x.val + y.val) + z.val) =
      min cap (x.val + min cap (y.val + z.val))
    lia
  one_mul x := by
    apply ext_val
    change min cap (min cap 0 + x.val) = x.val
    have := x.toFin.isLt
    dsimp [val]
    lia
  mul_one x := by
    apply ext_val
    change min cap (x.val + min cap 0) = x.val
    have := x.toFin.isLt
    dsimp [val]
    lia
  mul_comm x y := by
    apply ext_val
    change min cap (x.val + y.val) = min cap (y.val + x.val)
    rw [Nat.add_comm]

/-- The register has exactly `cap + 1` states. -/
theorem card (cap : Nat) : Fintype.card (Capped cap) = cap + 1 := by
  exact (Fintype.card_congr (equivFin cap)).trans (Fintype.card_fin (cap + 1))

/-- Saturation commutes with addition. -/
theorem ofNat_add (cap a b : Nat) :
    ofNat cap (a + b) = ofNat cap a * ofNat cap b := by
  apply ext_val
  change min cap (a + b) = min cap (min cap a + min cap b)
  lia

/-- A product of inserted values is their capped sum. -/
theorem prod_ofNat {ι : Type*} (cap : Nat) (s : Finset ι) (f : ι → Nat) :
    (∏ i ∈ s, ofNat cap (f i)) = ofNat cap (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih => simp [Finset.prod_insert hi, Finset.sum_insert hi, ih, ofNat_add]

end Capped

/-- A nonnegative weighted threshold uses a counter capped at the threshold. -/
def thresholdGate (threshold arity : Nat) (weight : Fin arity → Nat) :
    Op (fun _ : Unit => Capped threshold) :=
  .special () arity (fun i b => Capped.ofNat threshold (if b then weight i else 0))
    (fun z => decide (z.val = threshold))

/-- A capped counter computes the threshold predicate exactly. -/
theorem thresholdGate_eval (threshold arity : Nat) (weight : Fin arity → Nat)
    (x : Fin arity → Bool) :
    interpretation (thresholdGate threshold arity weight) x =
      decide (threshold ≤ ∑ i, if x i then weight i else 0) := by
  simp only [interpretation, thresholdGate]
  rw [Capped.prod_ofNat]
  change decide (min threshold (∑ i, if x i then weight i else 0) = threshold) = _
  congr 1
  apply propext
  lia

/-- A symmetric gate stores the exact Hamming weight in an arity-capped counter. -/
def symmetricGate (arity : Nat) (readout : Nat → Bool) :
    Op (fun _ : Unit => Capped arity) :=
  .special () arity (fun _ b => Capped.ofNat arity (if b then 1 else 0))
    (fun z => readout z.val)

/-- No saturation occurs when at most `arity` Boolean contributions are counted. -/
theorem symmetricGate_eval (arity : Nat) (readout : Nat → Bool)
    (x : Fin arity → Bool) :
    interpretation (symmetricGate arity readout) x =
      readout (∑ i, if x i then 1 else 0) := by
  have h : (∑ i, if x i then 1 else 0 : Nat) ≤ arity := by
    calc
      _ ≤ ∑ _ : Fin arity, 1 := Finset.sum_le_sum (fun i _ => by cases x i <;> simp)
      _ = arity := by simp
  simp only [interpretation, symmetricGate]
  rw [Capped.prod_ofNat]
  change readout (min arity (∑ i, if x i then 1 else 0)) = _
  rw [min_eq_right h]

/-- Threshold register size depends on the threshold, not the fan-in or weights. -/
theorem card_thresholdGate_register (threshold arity : Nat) (weight : Fin arity → Nat) :
    Fintype.card (thresholdGate threshold arity weight).Register = threshold + 1 := by
  exact (Fintype.card_congr (Equiv.refl (Capped threshold))).trans (Capped.card threshold)

/-- An arbitrary symmetric predicate uses exactly `arity + 1` aggregate states. -/
theorem card_symmetricGate_register (arity : Nat) (readout : Nat → Bool) :
    Fintype.card (symmetricGate arity readout).Register = arity + 1 := by
  exact (Fintype.card_congr (Equiv.refl (Capped arity))).trans (Capped.card arity)

/-- A positive-modulus weighted modular gate has exactly `modulus` states. -/
theorem card_modularGate_register (modulus arity : Nat) [NeZero modulus]
    (weight : Fin arity → ZMod modulus) (readout : ZMod modulus → Bool) :
    Fintype.card (modularGate modulus arity weight readout).Register = modulus := by
  exact (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card modulus)

end Algebraic.Aggregate

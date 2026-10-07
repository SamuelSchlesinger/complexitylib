/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HashAffine

/-!
# Unrestricted depth-three lower bound: hash bool

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HashBool.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound.BinaryHash

open BinaryAlgebra

variable {d r : ℕ}

theorem hashBool_eq_iff (u : Fin (d + r - 1) → Bool)
    (x : Fin d → Bool) (a : Fin r → Bool) :
    hashBool u x = a ↔
      hashF2 (bitsEquivF2 (Fin (d + r - 1)) u) (bitsEquivF2 (Fin d) x) =
        bitsEquivF2 (Fin r) a := by
  rw [← bitsEquivF2_hashBool]
  exact (bitsEquivF2 (Fin r)).injective.eq_iff.symm

theorem hashBool_collision_iff (u : Fin (d + r - 1) → Bool)
    (x y : Fin d → Bool) :
    hashBool u x = hashBool u y ↔
      hashF2 (bitsEquivF2 (Fin (d + r - 1)) u) (bitsEquivF2 (Fin d) x) =
        hashF2 (bitsEquivF2 (Fin (d + r - 1)) u) (bitsEquivF2 (Fin d) y) := by
  rw [← bitsEquivF2_hashBool, ← bitsEquivF2_hashBool]
  exact (bitsEquivF2 (Fin r)).injective.eq_iff.symm

/-- Transfer hash fibers between Boolean and field-vector presentations. -/
def hashBoolFiberEquiv (x : Fin d → Bool) (a : Fin r → Bool) :
    {u : Fin (d + r - 1) → Bool // hashBool u x = a} ≃
      {u : Seed d r // hashF2 u (bitsEquivF2 (Fin d) x) =
        bitsEquivF2 (Fin r) a} :=
  Equiv.subtypeEquiv (bitsEquivF2 (Fin (d + r - 1)))
    (fun u => hashBool_eq_iff u x a)

theorem hashBool_fiber_card (x : Fin d → Bool) (hx : x ≠ fun _ => false)
    (a : Fin r → Bool) :
    Fintype.card {u : Fin (d + r - 1) → Bool // hashBool u x = a} = 2 ^ (d - 1) := by
  classical
  have hnonzero : bitsEquivF2 (Fin d) x ≠ 0 := by
    intro h
    apply hx
    funext i
    apply bitValue_injective
    simpa using congrFun h i
  exact (Fintype.card_congr (hashBoolFiberEquiv x a)).trans
    (hashF2_fiber_card (bitsEquivF2 (Fin d) x) hnonzero (bitsEquivF2 (Fin r) a))

/-- Transfer hash collisions between Boolean and field-vector presentations. -/
def hashBoolCollisionEquiv (x y : Fin d → Bool) :
    {u : Fin (d + r - 1) → Bool // hashBool u x = hashBool u y} ≃
      {u : Seed d r // hashF2 u (bitsEquivF2 (Fin d) x) =
        hashF2 u (bitsEquivF2 (Fin d) y)} :=
  Equiv.subtypeEquiv (bitsEquivF2 (Fin (d + r - 1)))
    (fun u => hashBool_collision_iff u x y)

theorem hashBool_collision_card (x y : Fin d → Bool) (hxy : x ≠ y) :
    Fintype.card {u : Fin (d + r - 1) → Bool // hashBool u x = hashBool u y} =
      2 ^ (d - 1) := by
  classical
  exact (Fintype.card_congr (hashBoolCollisionEquiv (r := r) x y)).trans
    (hashF2_collision_card (bitsEquivF2 (Fin d) x) (bitsEquivF2 (Fin d) y)
      (fun h => hxy ((bitsEquivF2 (Fin d)).injective h)))

/-- Boolean assignments on a selected coordinate set. -/
def boolCoordinateCube (T : Finset (Fin d)) (rho : {i : Fin d // i ∉ T} → Bool) :
    Set (Fin d → Bool) :=
  {x | ∀ i (hi : i ∉ T), x i = rho ⟨i, hi⟩}

theorem mem_boolCoordinateCube_iff (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) (x : Fin d → Bool) :
    x ∈ boolCoordinateCube T rho ↔
      bitsEquivF2 (Fin d) x ∈ coordinateCube T (fun i => bitValue (rho i)) := by
  constructor
  · intro hx i hi
    change bitValue (x i) = bitValue (rho ⟨i, hi⟩)
    exact congrArg bitValue (hx i hi)
  · intro hx i hi
    exact bitValue_injective (hx i hi)

theorem injOn_hashBool_iff (u : Fin (d + r - 1) → Bool)
    (T : Finset (Fin d)) (rho : {i : Fin d // i ∉ T} → Bool) :
    Set.InjOn (hashBool u) (boolCoordinateCube T rho) ↔
      Set.InjOn (hashF2 (bitsEquivF2 (Fin (d + r - 1)) u))
        (coordinateCube T (fun i => bitValue (rho i))) := by
  constructor
  · intro hinj x hx y hy hxy
    obtain ⟨a, rfl⟩ := (bitsEquivF2 (Fin d)).surjective x
    obtain ⟨b, rfl⟩ := (bitsEquivF2 (Fin d)).surjective y
    have hab := hinj ((mem_boolCoordinateCube_iff T rho a).mpr hx)
      ((mem_boolCoordinateCube_iff T rho b).mpr hy)
      ((hashBool_collision_iff u a b).mpr hxy)
    exact congrArg (bitsEquivF2 (Fin d)) hab
  · intro hinj x hx y hy hxy
    apply (bitsEquivF2 (Fin d)).injective
    exact hinj ((mem_boolCoordinateCube_iff T rho x).mp hx)
      ((mem_boolCoordinateCube_iff T rho y).mp hy)
      ((hashBool_collision_iff u x y).mp hxy)

/-- Transfer bad-seed sets from Boolean to field-vector notation. -/
def hashBoolBadSeedEquiv (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    {u : Fin (d + r - 1) → Bool // ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} ≃
      {u : Seed d r // ¬ Set.InjOn (hashF2 u)
        (coordinateCube T (fun i => bitValue (rho i)))} :=
  Equiv.subtypeEquiv (bitsEquivF2 (Fin (d + r - 1)))
    (fun u => not_congr (injOn_hashBool_iff u T rho))

open scoped Classical in
theorem hashBool_badSeed_card_le (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    Fintype.card
      {u : Fin (d + r - 1) → Bool // ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} ≤
        (2 ^ T.card - 1) * 2 ^ (d - 1) := by
  classical
  calc
    Fintype.card
        {u : Fin (d + r - 1) → Bool // ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} =
      Fintype.card {u : Seed d r // ¬ Set.InjOn (hashF2 u)
        (coordinateCube T (fun i => bitValue (rho i)))} :=
          Fintype.card_congr (hashBoolBadSeedEquiv (r := r) T rho)
    _ = (badSeeds (r := r) T (fun i => bitValue (rho i))).card := by
      simp only [badSeeds, Fintype.card_subtype]
    _ ≤ (2 ^ T.card - 1) * 2 ^ (d - 1) := badSeeds_card_le T _

end DepthThreeLowerBound.BinaryHash

end Complexity

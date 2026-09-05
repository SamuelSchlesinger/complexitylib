/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ZigZagBaseExists

/-!
# The zig-zag tower, numbered

`ZigZagTower` builds its members out of nested product types and names the
base's vertices by an arbitrary bijection. That is enough for the mathematics,
but an algorithm has to be handed numbers. This module rebuilds the tower with
every vertex and dart numbered, and with each naming chosen explicitly: pairs
are packed by `finProdFinEquiv`, so a level-`k` vertex is a mixed-radix numeral
with `k + 1` digits in base `deg ^ 4`.

The recursion carries its own involutivity proof, which is what lets the next
level's types be `Fin` on the nose rather than up to a transport.

## Main definitions

- `Complexity.FinBase` — a numbered zig-zag base
- `Complexity.FinBase.data` — the rotation map at each level, with its proof
- `Complexity.FinBase.graphAt` — the level's graph
- `Complexity.FinBase.rotVal` — the same rotation map on raw numbers

## Main results

- `Complexity.FinBase.graphAt_succ` — one level is a zig-zag of the previous
- `Complexity.FinBase.spectral_graphAt` — every level has bound `2 / 5`
- `Complexity.FinBase.rotVal_eq` — the numeric recursion computes it
- `Complexity.nonempty_finBase` — a numbered base exists
-/

@[expose] public section

namespace Complexity

/-! ### The recursion, in the open -/

namespace RegGraph

/-- The rotation map of the square: walk two darts, and hand back the two
return labels in the opposite order. -/
theorem rot_power_two (G : RegGraph) (v : G.V) (s : Fin 2 → G.D) :
    (G.power 2).rot (v, s) =
      ((G.rot ((G.rot (v, s 0)).1, s 1)).1,
        ![(G.rot ((G.rot (v, s 0)).1, s 1)).2, (G.rot (v, s 0)).2]) := by
  have hw1 : G.walkAt 2 v s 1 = (G.rot (v, s 0)).1 := by
    rw [G.walkAt_succ_of_lt v s (by norm_num : (0 : ℕ) < 2)]
    rfl
  have hw2 : G.walkAt 2 v s 2 = (G.rot ((G.rot (v, s 0)).1, s 1)).1 := by
    rw [G.walkAt_succ_of_lt v s (by norm_num : (1 : ℕ) < 2), hw1]
    rfl
  refine Prod.ext ?_ ?_
  · show G.walkEnd 2 v s = _
    rw [← G.walkAt_self_eq_walkEnd]
    exact hw2
  · show G.revWalk v s = _
    funext j
    fin_cases j
    · show G.backLabel v s (Fin.rev 0) = _
      show (G.rot (G.walkAt 2 v s (Fin.rev (0 : Fin 2)).val, s (Fin.rev 0))).2 = _
      norm_num [hw1]
      rfl
    · show G.backLabel v s (Fin.rev 1) = _
      show (G.rot (G.walkAt 2 v s (Fin.rev (1 : Fin 2)).val, s (Fin.rev 1))).2 = _
      rfl

end RegGraph

/-- A zig-zag base with its vertices and darts numbered: `deg ^ 4` vertices,
`deg` darts, and a spectral bound of a fifth. -/
structure FinBase where
  /-- The degree. -/
  deg : ℕ
  /-- The degree is positive. -/
  deg_pos : 0 < deg
  /-- The rotation map. -/
  rot : Fin (deg ^ 4) × Fin deg → Fin (deg ^ 4) × Fin deg
  /-- It is an involution. -/
  rot_involutive : Function.Involutive rot
  /-- The spectral bound. -/
  lam : ℝ
  /-- It is nonnegative. -/
  lam_nonneg : 0 ≤ lam
  /-- And at most a fifth. -/
  lam_le : lam ≤ 1 / 5
  /-- The bound holds. -/
  spectral : (RegGraph.ofRot deg deg_pos (deg ^ 4) rot rot_involutive).SpectralBound lam

namespace FinBase

variable (F : FinBase)

/-- The base graph. -/
def graph : RegGraph := RegGraph.ofRot F.deg F.deg_pos (F.deg ^ 4) F.rot F.rot_involutive

@[simp] theorem V_graph : F.graph.V = Fin (F.deg ^ 4) := rfl

@[simp] theorem D_graph : F.graph.D = Fin F.deg := rfl

@[simp] theorem deg_graph : F.graph.deg = F.deg := Fintype.card_fin _

theorem sq_pos : 0 < F.deg ^ 2 := pow_pos F.deg_pos 2

/-- The number of vertices at level `k`. -/
def size (k : ℕ) : ℕ := (F.deg ^ 4) ^ (k + 1)

theorem size_succ (k : ℕ) : F.size (k + 1) = F.size k * F.deg ^ 4 := by
  rw [size, size, pow_succ]

/-- **The numbered base is a zig-zag base.** -/
def toBase : ZigZagBase where
  base := F.graph
  card_eq := by
    show Fintype.card (Fin (F.deg ^ 4)) = F.graph.deg ^ 4
    rw [Fintype.card_fin, deg_graph]
  lam := F.lam
  lam_nonneg := F.lam_nonneg
  lam_le := F.lam_le
  spectral := F.spectral

/-! ### The chosen namings -/

/-- Two darts of the base, as one dart of the level. -/
def dartName : Fin F.deg × Fin F.deg ≃ Fin (F.deg ^ 2) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-- The base's vertices name the pairs of darts of a level. -/
def baseName : Fin (F.deg ^ 4) ≃ (Fin 2 → Fin (F.deg ^ 2)) :=
  (finCongr (show F.deg ^ 4 = F.deg ^ 2 * F.deg ^ 2 by ring)).trans
    (finProdFinEquiv.symm.trans (finTwoArrowEquiv _).symm)

/-- A level-`k` vertex together with a base vertex, as a level-`(k+1)` vertex. -/
def vertName (k : ℕ) :
    Fin (F.size k) × (Fin 2 → Fin (F.deg ^ 2)) ≃ Fin (F.size (k + 1)) :=
  ((Equiv.refl _).prodCongr F.baseName.symm).trans
    (finProdFinEquiv.trans (finCongr (by simp only [size]; ring)))

/-- The two darts of the squared base, as one. -/
def zeroDartName : (Fin 2 → Fin F.deg) ≃ Fin (F.deg ^ 2) :=
  (finTwoArrowEquiv _).trans F.dartName

/-- The squared base's vertices, numbered as level zero's. -/
def zeroVertName : Fin (F.deg ^ 4) ≃ Fin (F.size 0) :=
  finCongr (by simp [size])

/-! ### The namings, in numbers -/

@[simp] theorem val_dartName (a b : Fin F.deg) :
    (F.dartName (a, b)).val = b.val + F.deg * a.val := rfl

@[simp] theorem val_dartName_symm_fst (i : Fin (F.deg ^ 2)) :
    (F.dartName.symm i).1.val = i.val / F.deg := rfl

@[simp] theorem val_dartName_symm_snd (i : Fin (F.deg ^ 2)) :
    (F.dartName.symm i).2.val = i.val % F.deg := rfl

@[simp] theorem val_baseName_zero (x : Fin (F.deg ^ 4)) :
    (F.baseName x 0).val = x.val / F.deg ^ 2 := rfl

@[simp] theorem val_baseName_one (x : Fin (F.deg ^ 4)) :
    (F.baseName x 1).val = x.val % F.deg ^ 2 := rfl

@[simp] theorem val_baseName_symm (s : Fin 2 → Fin (F.deg ^ 2)) :
    (F.baseName.symm s).val = (s 1).val + F.deg ^ 2 * (s 0).val := rfl

@[simp] theorem val_vertName (k : ℕ) (u : Fin (F.size k)) (s : Fin 2 → Fin (F.deg ^ 2)) :
    (F.vertName k (u, s)).val = (F.baseName.symm s).val + F.deg ^ 4 * u.val := rfl

@[simp] theorem val_vertName_symm_fst (k : ℕ) (v : Fin (F.size (k + 1))) :
    ((F.vertName k).symm v).1.val = v.val / F.deg ^ 4 := rfl

@[simp] theorem val_vertName_symm_snd_zero (k : ℕ) (v : Fin (F.size (k + 1))) :
    (((F.vertName k).symm v).2 0).val = v.val % F.deg ^ 4 / F.deg ^ 2 := rfl

@[simp] theorem val_vertName_symm_snd_one (k : ℕ) (v : Fin (F.size (k + 1))) :
    (((F.vertName k).symm v).2 1).val = v.val % F.deg ^ 4 % F.deg ^ 2 := rfl

theorem val_baseName_symm_vertName_symm (k : ℕ) (v : Fin (F.size (k + 1))) :
    (F.baseName.symm ((F.vertName k).symm v).2).val = v.val % F.deg ^ 4 := by
  have hlt : v.val % F.deg ^ 4 < F.deg ^ 4 := Nat.mod_lt _ (pow_pos F.deg_pos 4)
  have hy : ((F.vertName k).symm v).2 = F.baseName ⟨v.val % F.deg ^ 4, hlt⟩ := rfl
  rw [hy, Equiv.symm_apply_apply]

@[simp] theorem val_zeroVertName (x : Fin (F.deg ^ 4)) : (F.zeroVertName x).val = x.val := rfl

@[simp] theorem val_zeroVertName_symm (v : Fin (F.size 0)) :
    (F.zeroVertName.symm v).val = v.val := rfl

@[simp] theorem val_zeroDartName (s : Fin 2 → Fin F.deg) :
    (F.zeroDartName s).val = (s 1).val + F.deg * (s 0).val := rfl

@[simp] theorem val_zeroDartName_symm_zero (i : Fin (F.deg ^ 2)) :
    (F.zeroDartName.symm i 0).val = i.val / F.deg := rfl

@[simp] theorem val_zeroDartName_symm_one (i : Fin (F.deg ^ 2)) :
    (F.zeroDartName.symm i 1).val = i.val % F.deg := rfl

/-! ### The tower -/

/-- **The rotation map at each level**, carrying its involutivity so that the
next level's types are numbered on the nose. -/
noncomputable def data (F : FinBase) : (k : ℕ) →
    { f : Fin (F.size k) × Fin (F.deg ^ 2) → Fin (F.size k) × Fin (F.deg ^ 2) //
      Function.Involutive f }
  | 0 =>
      let W := ((F.graph.power 2).relabelV F.zeroVertName).relabel F.zeroDartName
      ⟨W.rot, W.rot_involutive⟩
  | k + 1 =>
      let G := RegGraph.ofRot (F.deg ^ 2) F.sq_pos (F.size k) (data F k).1 (data F k).2
      let W := ((RegGraph.zigzag (G.power 2) F.graph F.baseName).relabelV
        (F.vertName k)).relabel F.dartName
      ⟨W.rot, W.rot_involutive⟩

/-- The level-`k` graph. -/
noncomputable def graphAt (k : ℕ) : RegGraph :=
  RegGraph.ofRot (F.deg ^ 2) F.sq_pos (F.size k) (F.data k).1 (F.data k).2

@[simp] theorem order_graphAt (k : ℕ) : (F.graphAt k).order = F.size k := Fintype.card_fin _

@[simp] theorem deg_graphAt (k : ℕ) : (F.graphAt k).deg = F.deg ^ 2 := Fintype.card_fin _

theorem graphAt_zero :
    F.graphAt 0 = ((F.graph.power 2).relabelV F.zeroVertName).relabel F.zeroDartName := by
  simp only [graphAt, data]
  rfl

/-- **One level is the zig-zag of the previous with the base**, renumbered. -/
theorem graphAt_succ (k : ℕ) :
    F.graphAt (k + 1) =
      ((RegGraph.zigzag ((F.graphAt k).power 2) F.graph F.baseName).relabelV
        (F.vertName k)).relabel F.dartName := by
  simp only [graphAt, data]
  rfl

/-- **Every level has spectral bound `2 / 5`.** -/
theorem spectral_graphAt (F : FinBase) : ∀ k : ℕ, (F.graphAt k).SpectralBound (2 / 5)
  | 0 => by
      rw [graphAt_zero]
      exact RegGraph.spectralBound_relabel _ _
        (RegGraph.spectralBound_relabelV _ _ F.toBase.towerZero.spec)
  | k + 1 => by
      rw [graphAt_succ]
      exact RegGraph.spectralBound_relabel _ _
        (RegGraph.spectralBound_relabelV _ _
          (F.toBase.towerSuccOf ⟨F.graphAt k, by simp [toBase], spectral_graphAt F k⟩
            F.baseName).spec)

/-- **One level of the recursion, in coordinates.** A level-`(k+1)` vertex is a
level-`k` vertex together with a base vertex, and a level-`(k+1)` dart is a pair
of base darts; in those coordinates a step is: turn in the base, walk two darts
of the level below, turn in the base again. -/
theorem data_succ_apply (k : ℕ) (v : Fin (F.size (k + 1))) (i : Fin (F.deg ^ 2))
    {us : Fin (F.size k) × (Fin 2 → Fin (F.deg ^ 2))} (hus : us = (F.vertName k).symm v)
    {ab : Fin F.deg × Fin F.deg} (hab : ab = F.dartName.symm i)
    {p : Fin (F.deg ^ 4) × Fin F.deg} (hp : p = F.rot (F.baseName.symm us.2, ab.1))
    {q : Fin (F.size k) × (Fin 2 → Fin (F.deg ^ 2))}
    (hq : q = ((F.graphAt k).power 2).rot (us.1, F.baseName p.1))
    {r : Fin (F.deg ^ 4) × Fin F.deg} (hr : r = F.rot (F.baseName.symm q.2, ab.2)) :
    (F.data (k + 1)).1 (v, i)
      = (F.vertName k (q.1, F.baseName r.1), F.dartName (r.2, p.2)) := by
  subst hus hab hp hq hr
  simp only [data, RegGraph.relabel, RegGraph.relabelV, RegGraph.zigzag, RegGraph.zigzagRot,
    graphAt, graph, RegGraph.ofRot]
  rfl

@[simp] theorem rot_graphAt (k : ℕ) : (F.graphAt k).rot = (F.data k).1 := rfl

/-- **The bottom of the recursion, in coordinates.** Level zero is the base
squared: walk two base darts, and return the labels in the opposite order. -/
theorem data_zero_apply (v : Fin (F.size 0)) (i : Fin (F.deg ^ 2))
    {s : Fin 2 → Fin F.deg} (hs : s = F.zeroDartName.symm i)
    {p₀ : Fin (F.deg ^ 4) × Fin F.deg} (h0 : p₀ = F.rot (F.zeroVertName.symm v, s 0))
    {p₁ : Fin (F.deg ^ 4) × Fin F.deg} (h1 : p₁ = F.rot (p₀.1, s 1)) :
    (F.data 0).1 (v, i) = (F.zeroVertName p₁.1, F.zeroDartName ![p₁.2, p₀.2]) := by
  subst hs h0 h1
  simp only [data, RegGraph.relabel, RegGraph.relabelV, graph, RegGraph.ofRot]
  rfl

/-- **The step in full**, with the two walks of the level below spelled out. -/
theorem data_succ_apply' (k : ℕ) (v : Fin (F.size (k + 1))) (i : Fin (F.deg ^ 2))
    {us : Fin (F.size k) × (Fin 2 → Fin (F.deg ^ 2))} (hus : us = (F.vertName k).symm v)
    {ab : Fin F.deg × Fin F.deg} (hab : ab = F.dartName.symm i)
    {p : Fin (F.deg ^ 4) × Fin F.deg} (hp : p = F.rot (F.baseName.symm us.2, ab.1))
    {q₀ : Fin (F.size k) × Fin (F.deg ^ 2)}
    (hq₀ : q₀ = (F.data k).1 (us.1, F.baseName p.1 0))
    {q₁ : Fin (F.size k) × Fin (F.deg ^ 2)}
    (hq₁ : q₁ = (F.data k).1 (q₀.1, F.baseName p.1 1))
    {r : Fin (F.deg ^ 4) × Fin F.deg}
    (hr : r = F.rot (F.baseName.symm ![q₁.2, q₀.2], ab.2)) :
    (F.data (k + 1)).1 (v, i)
      = (F.vertName k (q₁.1, F.baseName r.1), F.dartName (r.2, p.2)) := by
  refine F.data_succ_apply k v i hus hab hp (q := (q₁.1, ![q₁.2, q₀.2])) ?_ hr
  erw [RegGraph.rot_power_two, rot_graphAt, hq₁, hq₀]
  rfl

/-! ### The recursion, in numbers -/

/-- The base's rotation map, on raw numbers. -/
noncomputable def baseVal (x a : ℕ) : ℕ × ℕ :=
  if h : x < F.deg ^ 4 ∧ a < F.deg then
    ((F.rot (⟨x, h.1⟩, ⟨a, h.2⟩)).1.val, (F.rot (⟨x, h.1⟩, ⟨a, h.2⟩)).2.val)
  else (0, 0)

@[simp] theorem baseVal_apply (x : Fin (F.deg ^ 4)) (a : Fin F.deg) :
    F.baseVal x.val a.val = ((F.rot (x, a)).1.val, (F.rot (x, a)).2.val) := by
  rw [baseVal, dite_eq_left ⟨x.isLt, a.isLt⟩]

/-- **The tower's rotation map, on raw numbers.** A level-`(k+1)` vertex `v`
splits as `v / deg^4` (the level below) and `v % deg^4` (the base); a dart `i`
splits as `i / deg` and `i % deg`. The step turns in the base, walks two darts
of the level below, and turns in the base again. -/
noncomputable def rotVal (F : FinBase) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, (v, i) =>
      let p₀ := F.baseVal v (i / F.deg)
      let p₁ := F.baseVal p₀.1 (i % F.deg)
      (p₁.1, p₀.2 + F.deg * p₁.2)
  | k + 1, (v, i) =>
      let p := F.baseVal (v % F.deg ^ 4) (i / F.deg)
      let q₀ := rotVal F k (v / F.deg ^ 4, p.1 / F.deg ^ 2)
      let q₁ := rotVal F k (q₀.1, p.1 % F.deg ^ 2)
      let r := F.baseVal (q₀.2 + F.deg ^ 2 * q₁.2) (i % F.deg)
      (r.1 + F.deg ^ 4 * q₁.1, p.2 + F.deg * r.2)

/-- **The numbers compute the tower.** -/
theorem rotVal_eq (k : ℕ) (v : Fin (F.size k)) (i : Fin (F.deg ^ 2)) :
    F.rotVal k (v.val, i.val)
      = (((F.data k).1 (v, i)).1.val, ((F.data k).1 (v, i)).2.val) := by
  induction k generalizing i with
  | zero =>
      have e0 : F.baseVal v.val (i.val / F.deg)
          = ((F.rot (F.zeroVertName.symm v, F.zeroDartName.symm i 0)).1.val,
             (F.rot (F.zeroVertName.symm v, F.zeroDartName.symm i 0)).2.val) :=
        F.baseVal_apply (F.zeroVertName.symm v) (F.zeroDartName.symm i 0)
      have e1 : F.baseVal (F.rot (F.zeroVertName.symm v, F.zeroDartName.symm i 0)).1.val
            (i.val % F.deg)
          = ((F.rot ((F.rot (F.zeroVertName.symm v, F.zeroDartName.symm i 0)).1,
                F.zeroDartName.symm i 1)).1.val,
             (F.rot ((F.rot (F.zeroVertName.symm v, F.zeroDartName.symm i 0)).1,
                F.zeroDartName.symm i 1)).2.val) :=
        F.baseVal_apply (F.rot (F.zeroVertName.symm v, F.zeroDartName.symm i 0)).1
          (F.zeroDartName.symm i 1)
      rw [F.data_zero_apply v i rfl rfl rfl]
      simp only [rotVal]
      rw [e0, e1]
      simp
  | succ k ih =>
      have hp := F.baseVal_apply (F.baseName.symm ((F.vertName k).symm v).2)
        (F.dartName.symm i).1
      rw [F.val_baseName_symm_vertName_symm k v, val_dartName_symm_fst] at hp
      have hq0 := ih ((F.vertName k).symm v).1
        (F.baseName (F.rot (F.baseName.symm ((F.vertName k).symm v).2,
          (F.dartName.symm i).1)).1 0)
      have hq1 := ih ((F.data k).1 (((F.vertName k).symm v).1,
          F.baseName (F.rot (F.baseName.symm ((F.vertName k).symm v).2,
            (F.dartName.symm i).1)).1 0)).1
        (F.baseName (F.rot (F.baseName.symm ((F.vertName k).symm v).2,
          (F.dartName.symm i).1)).1 1)
      have hr := F.baseVal_apply (F.baseName.symm
        ![((F.data k).1 (((F.data k).1 (((F.vertName k).symm v).1,
              F.baseName (F.rot (F.baseName.symm ((F.vertName k).symm v).2,
                (F.dartName.symm i).1)).1 0)).1,
            F.baseName (F.rot (F.baseName.symm ((F.vertName k).symm v).2,
              (F.dartName.symm i).1)).1 1)).2,
          ((F.data k).1 (((F.vertName k).symm v).1,
            F.baseName (F.rot (F.baseName.symm ((F.vertName k).symm v).2,
              (F.dartName.symm i).1)).1 0)).2]) (F.dartName.symm i).2
      rw [val_baseName_symm, val_dartName_symm_snd] at hr
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hr
      rw [val_vertName_symm_fst, val_baseName_zero] at hq0
      rw [val_baseName_one] at hq1
      rw [F.data_succ_apply' k v i rfl rfl rfl rfl rfl rfl]
      simp only [rotVal]
      rw [hp]
      dsimp only
      rw [hq0]
      dsimp only
      rw [hq1]
      dsimp only
      rw [hr]
      simp

theorem baseVal_lt {x a : ℕ} (hx : x < F.deg ^ 4) (ha : a < F.deg) :
    (F.baseVal x a).1 < F.deg ^ 4 ∧ (F.baseVal x a).2 < F.deg := by
  rw [baseVal, dite_eq_left ⟨hx, ha⟩]
  exact ⟨Fin.isLt _, Fin.isLt _⟩

theorem rotVal_lt (k : ℕ) {v i : ℕ} (hv : v < F.size k) (hi : i < F.deg ^ 2) :
    (F.rotVal k (v, i)).1 < F.size k ∧ (F.rotVal k (v, i)).2 < F.deg ^ 2 := by
  rw [show v = (⟨v, hv⟩ : Fin (F.size k)).val from rfl,
    show i = (⟨i, hi⟩ : Fin (F.deg ^ 2)).val from rfl, F.rotVal_eq k]
  exact ⟨Fin.isLt _, Fin.isLt _⟩

/-! ### Choosing a level -/

theorem one_lt_pow_four (hd : 1 < F.deg) : 1 < F.deg ^ 4 := Nat.one_lt_pow (by norm_num) hd

theorem exists_size_ge (hd : 1 < F.deg) (n : ℕ) : ∃ k, n ≤ F.size k := by
  refine ⟨n, ?_⟩
  calc n ≤ (F.deg ^ 4) ^ n := (Nat.lt_pow_self (F.one_lt_pow_four hd)).le
    _ ≤ (F.deg ^ 4) ^ (n + 1) :=
        Nat.pow_le_pow_right (Nat.zero_lt_of_lt (F.one_lt_pow_four hd)) (by omega)

theorem le_size_self (hd : 1 < F.deg) (n : ℕ) : n ≤ F.size n := by
  calc n ≤ (F.deg ^ 4) ^ n := (Nat.lt_pow_self (F.one_lt_pow_four hd)).le
    _ ≤ (F.deg ^ 4) ^ (n + 1) :=
        Nat.pow_le_pow_right (Nat.zero_lt_of_lt (F.one_lt_pow_four hd)) (by omega)

/-- The first level large enough for a requested size. -/
noncomputable def level (F : FinBase) (hd : 1 < F.deg) (n : ℕ) : ℕ :=
  Nat.find (F.exists_size_ge hd n)

theorem le_size_level (hd : 1 < F.deg) (n : ℕ) : n ≤ F.size (F.level hd n) :=
  Nat.find_spec (F.exists_size_ge hd n)

/-- **The level a size needs is at most that size.** -/
theorem level_le (hd : 1 < F.deg) (n : ℕ) : F.level hd n ≤ n :=
  Nat.find_le (F.le_size_self hd n)

theorem size_level_le (hd : 1 < F.deg) (n : ℕ) (hn : 1 ≤ n) :
    F.size (F.level hd n) ≤ F.deg ^ 4 * n := by
  classical
  rcases Nat.eq_zero_or_pos (F.level hd n) with h0 | hpos
  · rw [level] at h0 ⊢
    rw [h0, size]
    calc (F.deg ^ 4) ^ (0 + 1) = F.deg ^ 4 := by ring
      _ ≤ F.deg ^ 4 * n := Nat.le_mul_of_pos_right _ hn
  · obtain ⟨m, hm⟩ : ∃ m, F.level hd n = m + 1 := ⟨F.level hd n - 1, by omega⟩
    have hfind : Nat.find (F.exists_size_ge hd n) = m + 1 := hm
    have hlt : ¬ n ≤ F.size m :=
      Nat.find_min (F.exists_size_ge hd n) (m := m) (by rw [hfind]; omega)
    have hprev : F.size m < n := by omega
    rw [hm, size]
    rw [size] at hprev
    calc (F.deg ^ 4) ^ (m + 1 + 1) = F.deg ^ 4 * (F.deg ^ 4) ^ (m + 1) := by ring
      _ ≤ F.deg ^ 4 * n := Nat.mul_le_mul_left _ hprev.le

end FinBase

/-! ### Numbering a base -/

namespace ZigZagBase

variable (B : ZigZagBase)

theorem card_base_darts : Fintype.card B.base.D = B.base.deg := rfl

/-- **A zig-zag base, numbered.** -/
noncomputable def toFin : FinBase where
  deg := B.base.deg
  deg_pos := B.base.deg_pos
  rot := (B.base.toFinFormOf (B.base.deg ^ 4) B.base.deg B.card_eq B.card_base_darts).rot
  rot_involutive :=
    (B.base.toFinFormOf (B.base.deg ^ 4) B.base.deg B.card_eq B.card_base_darts).rot_involutive
  lam := B.lam
  lam_nonneg := B.lam_nonneg
  lam_le := B.lam_le
  spectral :=
    RegGraph.spectralBound_toFinFormOf B.base (B.base.deg ^ 4) B.base.deg B.card_eq
      B.card_base_darts B.spectral

end ZigZagBase

/-- **A numbered base exists.** -/
theorem nonempty_finBase : Nonempty FinBase :=
  ⟨randExpander.toZigZagBase.toFin⟩

/-- **And one whose degree is above one**, which is what folding a tower onto a
requested size needs. -/
theorem exists_finBase : ∃ F : FinBase, 1 < F.deg :=
  ⟨randExpander.toZigZagBase.toFin,
    randExpander.one_lt_deg_toZigZagBase (by
      show 1 < 120
      norm_num)⟩

end Complexity

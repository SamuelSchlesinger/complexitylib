/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.TowerTable
public import Complexitylib.Classes.PCP.Internal.FamilyFin

/-!
# The expander's table, for a requested size

The expander family answers a request for `n` vertices with the first tower
member of at least `2 n` of them, and `TowerTable` writes the rotation table of a
level. This module finds the level a request calls for — the first `L` with
`2 n ≤ d ^ (L + 1)`, a ceiling logarithm — and writes that level's table. The
table is polynomially long, because the level found always names a size within a
constant factor of the request.

## Main definitions

- `Complexity.levelFn`, `Complexity.sizeFn` — the level for a requested count,
  and its size
- `Complexity.FinBase.famTableFn` — the table for a requested size

## Main results

- `Complexity.levelFn_length` — the search finds the first level that is large
  enough
- `Complexity.pow_levelFn_le` — whatever level it reports, that level's size is
  polynomially bounded
- `Complexity.FinBase.famTableFn_mem_FP` — writing it is polynomial time
- `Complexity.FinBase.famRotFn_mem_FP` — and the family's rotation map is
  polynomial time
- `Complexity.FinBase.levelFn_fitLevel` — the search reports the level the
  family uses
-/

@[expose] public section

namespace Complexity

/-! ### Finding the tower level -/

/-- **The tower level for a requested count**, in unary: the first level `L`
with `2 |z| ≤ d ^ (L + 1)`, which is `Nat.clog d (2 |z|) - 1`, capped at
`p.eval |z|`. -/
def levelFn (d : ℕ) (p : Polynomial ℕ) (z : List Bool) : List Bool :=
  List.replicate (min (Nat.clog d (2 * z.length) - 1) (p.eval z.length)) true

theorem levelFn_mem_FP (d : ℕ) (p : Polynomial ℕ) : levelFn d p ∈ FP :=
  (((UnaryFn.const d).clog ((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP))).sub
    (UnaryFn.const 1)).min (UnaryFn.polyEval p (UnaryFn.length id_mem_FP))

/-- **The search finds the first level that is large enough.** -/
theorem levelFn_length (d : ℕ) (p : Polynomial ℕ) (z : List Bool) (L : ℕ)
    (hL : 2 * z.length ≤ d ^ (L + 1)) (hmin : ∀ i < L, ¬ (2 * z.length ≤ d ^ (i + 1)))
    (hp : L ≤ p.eval z.length) :
    (levelFn d p z).length = L := by
  rw [levelFn, List.length_replicate]
  suffices h : Nat.clog d (2 * z.length) - 1 = L by rw [h]; exact min_eq_left hp
  rcases Nat.lt_or_ge 1 d with hd | hd
  · have h1 : Nat.clog d (2 * z.length) ≤ L + 1 := (Nat.clog_le_iff_le_pow hd).mpr hL
    rcases Nat.eq_zero_or_pos L with rfl | hL0
    · omega
    · have h2 : L < Nat.clog d (2 * z.length) := (Nat.lt_clog_iff_pow_lt hd).mpr
        (lt_of_not_ge fun h => hmin (L - 1) (by omega) (by rwa [Nat.sub_add_cancel hL0]))
      omega
  · rw [Nat.clog_of_left_le_one hd]
    rcases Nat.eq_zero_or_pos L with rfl | hL0
    · rfl
    · have hz : 2 * z.length ≤ 1 :=
        hL.trans ((Nat.pow_le_pow_left hd _).trans (le_of_eq (one_pow _)))
      exact absurd (by omega) (hmin 0 hL0)

/-- **Whatever level the search reports, its size is bounded** — which is what
lets the table at that level be written down. -/
theorem pow_levelFn_le (d : ℕ) (p : Polynomial ℕ) (z : List Bool) :
    d ^ ((levelFn d p z).length + 1) ≤ d + 2 * z.length * d := by
  rw [levelFn, List.length_replicate, pow_succ]
  suffices h : d ^ min (Nat.clog d (2 * z.length) - 1) (p.eval z.length) ≤ 1 + 2 * z.length by
    calc _ ≤ (1 + 2 * z.length) * d := Nat.mul_le_mul_right d h
      _ = d + 2 * z.length * d := by ring
  have hk := min_le_left (Nat.clog d (2 * z.length) - 1) (p.eval z.length)
  generalize min (Nat.clog d (2 * z.length) - 1) (p.eval z.length) = k at hk ⊢
  rcases Nat.lt_or_ge 1 d with hd | hd
  · by_cases hlt : k < Nat.clog d (2 * z.length)
    · have := (Nat.lt_clog_iff_pow_lt hd).mp hlt
      omega
    · rw [show k = 0 by omega, pow_zero]
      omega
  · calc d ^ k ≤ 1 ^ k := Nat.pow_le_pow_left hd k
      _ = 1 := one_pow k
      _ ≤ 1 + 2 * z.length := by omega

/-- The size at the level the search reports. -/
def sizeFn (d : ℕ) (p : Polynomial ℕ) (z : List Bool) : List Bool :=
  List.replicate (d ^ ((levelFn d p z).length + 1)) true

theorem sizeFn_mem_FP (d : ℕ) (p : Polynomial ℕ) : sizeFn d p ∈ FP :=
  UnaryFn.pow_of_le (UnaryFn.const d)
    ((UnaryFn.length (levelFn_mem_FP d p)).add (UnaryFn.const 1))
    ((UnaryFn.const d).add
      (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).mul (UnaryFn.const d)))
    (pow_levelFn_le d p)

/-- **The size the search reports is the power its level names.** -/
theorem sizeFn_length (d : ℕ) (p : Polynomial ℕ) (z : List Bool) :
    (sizeFn d p z).length = d ^ ((levelFn d p z).length + 1) :=
  List.length_replicate ..

namespace FinBase

variable (F : FinBase) (p : Polynomial ℕ)

/-- The level the search reports for a request. -/
noncomputable def searchLevel (z : List Bool) : ℕ := (levelFn (F.deg ^ 4) p z).length

/-- **The size at the reported level is within a constant factor of the
request.** -/
theorem size_searchLevel_le (z : List Bool) :
    F.size (F.searchLevel p z) ≤ F.deg ^ 4 + 2 * z.length * F.deg ^ 4 :=
  pow_levelFn_le (F.deg ^ 4) p z

theorem size_le_of_le {l : ℕ} (z : List Bool) (hl : l ≤ F.searchLevel p z) :
    F.size l ≤ F.deg ^ 4 + 2 * z.length * F.deg ^ 4 := by
  refine le_trans ?_ (F.size_searchLevel_le p z)
  rw [size, size]
  have hbase : 1 ≤ F.deg ^ 4 := pow_pos F.deg_pos 4
  exact Nat.pow_le_pow_right hbase (by omega)

/-- The table of the level a request calls for. -/
noncomputable def famTableFn (z : List Bool) : List Bool := F.table (F.searchLevel p z)

/-- The polynomial that bounds that table. -/
noncomputable def tableWidth : Polynomial ℕ :=
  Polynomial.C 2
    + (Polynomial.C (F.deg ^ 4) + Polynomial.C (2 * F.deg ^ 4) * Polynomial.X)
      * Polynomial.C (F.deg ^ 2)
      * (Polynomial.C 4 * (Polynomial.C (F.deg ^ 4)
            + Polynomial.C (2 * F.deg ^ 4) * Polynomial.X)
        + Polynomial.C (4 * F.deg ^ 2 + 6))

theorem eval_tableWidth (n : ℕ) :
    F.tableWidth.eval n
      = 2 + (F.deg ^ 4 + 2 * F.deg ^ 4 * n) * F.deg ^ 2
        * (4 * (F.deg ^ 4 + 2 * F.deg ^ 4 * n) + (4 * F.deg ^ 2 + 6)) := by
  simp only [tableWidth, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

/-- **Writing the table for a requested size is polynomial time.** -/
theorem famTableFn_mem_FP : F.famTableFn p ∈ FP := by
  refine F.table_mem_FP (levelFn_mem_FP (F.deg ^ 4) p)
    (polyRulerFn_mem_FP F.tableWidth id_mem_FP) ?_
  intro z l hl
  rw [polyRuler_length, eval_tableWidth]
  refine le_trans (F.length_table_le l) ?_
  have hsize : F.size l ≤ F.deg ^ 4 + 2 * z.length * F.deg ^ 4 :=
    F.size_le_of_le p z hl
  have hM : F.deg ^ 4 + 2 * z.length * F.deg ^ 4 = F.deg ^ 4 + 2 * F.deg ^ 4 * z.length := by
    ring
  rw [hM] at hsize
  have h1 : F.size l * F.deg ^ 2 ≤ (F.deg ^ 4 + 2 * F.deg ^ 4 * z.length) * F.deg ^ 2 :=
    Nat.mul_le_mul_right _ hsize
  have h2 : 4 * F.size l + 4 * F.deg ^ 2 + 6
      ≤ 4 * (F.deg ^ 4 + 2 * F.deg ^ 4 * z.length) + (4 * F.deg ^ 2 + 6) := by omega
  exact Nat.add_le_add_left (Nat.mul_le_mul h1 h2) 2

/-! ### The level the family asks for -/

/-- **The search reports the level the family uses.** -/
theorem levelFn_fitLevel (hd : 1 < F.deg) (n : ℕ)
    (hp : F.fitLevel hd n ≤ p.eval n) :
    (levelFn (F.deg ^ 4) p (List.replicate n true)).length = F.fitLevel hd n := by
  have hlen : (List.replicate n true).length = n := List.length_replicate
  refine levelFn_length _ p _ _ ?_ ?_ (by rw [hlen]; exact hp)
  · rw [hlen]
    have := F.le_size_level hd (2 * n)
    rw [size] at this
    exact this
  · intro i hi
    rw [hlen]
    have hmin := Nat.find_min (F.exists_size_ge hd (2 * n)) (m := i) hi
    rw [size] at hmin
    exact hmin

/-- **The search reports the size the family uses.** -/
theorem sizeFn_fitN (hd : 1 < F.deg) (n : ℕ) (hp : F.fitLevel hd n ≤ p.eval n) :
    (sizeFn (F.deg ^ 4) p (List.replicate n true)).length = F.fitN hd n := by
  rw [sizeFn_length, F.levelFn_fitLevel p hd n hp, fitN, size]

/-- **And writes that level's table.** -/
theorem famTableFn_eq (hd : 1 < F.deg) (n : ℕ) (hp : F.fitLevel hd n ≤ p.eval n) :
    F.famTableFn p (List.replicate n true) = F.table (F.fitLevel hd n) := by
  rw [famTableFn, searchLevel, F.levelFn_fitLevel p hd n hp]

/-! ### The family's rotation map -/

/-- The family's rotation map, on `pair (unary n) (pair (unary v) (unary i))`:
split the dart into a slot and a step, lift the vertex into the tower member,
look the step up in that member's table, and fold the answer back onto `n`
vertices. Darts past the fold's degree are self-loops. -/
noncomputable def famRotFn (z : List Bool) : List Bool :=
  let n := pairFst z
  let v := pairFst (pairSnd z)
  let i := pairSnd (pairSnd z)
  let N := sizeFn (F.deg ^ 4) p n
  let T := F.famTableFn p n
  let m := divFn2 (pair n N) ++ [true]
  let s := divC F.fitD i
  let c := modC F.fitD i
  let lift := v ++ mulLen s n
  let y1 := tableFst T (mulLen lift (List.replicate F.fitD true) ++ c).length
  let y2 := tableSnd T (mulLen lift (List.replicate F.fitD true) ++ c).length
  ifLtLen i (mulLen m (List.replicate F.fitD true))
    (ifLtLen lift N
      (pair (marks (modFn2 (pair n y1)))
        (marks (y2 ++ mulC F.fitD (divFn2 (pair n y1)))))
      (pair (marks v) (marks i)))
    (pair (marks v) (marks i))

theorem famRotFn_mem_FP : F.famRotFn p ∈ FP := by
  have hn : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hv : (fun z : List Bool => pairFst (pairSnd z)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP) fun _ => rfl
  have hi : (fun z : List Bool => pairSnd (pairSnd z)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp Cobham.sndBlock_mem_FP Cobham.sndBlock_mem_FP) fun _ => rfl
  have hN : (fun z : List Bool => sizeFn (F.deg ^ 4) p (pairFst z)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hn (sizeFn_mem_FP _ p)) fun _ => rfl
  have hT : (fun z : List Bool => F.famTableFn p (pairFst z)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hn (F.famTableFn_mem_FP p)) fun _ => rfl
  have hm := Cobham.appendFn_mem_FP
    (mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hn hN) divFn2_mem_FP) fun _ => rfl)
    (constFn_mem_FP [true])
  have hs := divC_mem_FP hi F.fitD
  have hc := modC_mem_FP hi F.fitD
  have hlift := Cobham.appendFn_mem_FP hv (mulLen_mem_FP hs hn)
  have hidx := Cobham.appendFn_mem_FP
    (mulLen_mem_FP hlift (constFn_mem_FP (List.replicate F.fitD true))) hc
  have hy1 := tableFst_mem_FP hidx hT
  have hy2 := tableSnd_mem_FP hidx hT
  have hmod := mem_FP_of_eq
    (mem_FP_comp (Cobham.pairFn_mem_FP hn hy1) modFn2_mem_FP) fun _ => rfl
  have hdiv := mem_FP_of_eq
    (mem_FP_comp (Cobham.pairFn_mem_FP hn hy1) divFn2_mem_FP) fun _ => rfl
  have hstep := Cobham.pairFn_mem_FP (marks_mem_FP hmod)
    (marks_mem_FP (Cobham.appendFn_mem_FP hy2 (mulC_mem_FP hdiv F.fitD)))
  have hstay := Cobham.pairFn_mem_FP (marks_mem_FP hv) (marks_mem_FP hi)
  have hinner := ifLtLen_mem_FP hlift hN hstep hstay
  have houter := ifLtLen_mem_FP hi
    (mulLen_mem_FP hm (constFn_mem_FP (List.replicate F.fitD true))) hinner hstay
  exact mem_FP_of_eq houter fun _ => rfl

/-- **The rotation function runs the family's rotation map.** -/
theorem famRotFn_eq (hd : 1 < F.deg) (n v i : ℕ)
    (hp : F.fitLevel hd n ≤ p.eval n) :
    F.famRotFn p (pair (List.replicate n true)
        (pair (List.replicate v true) (List.replicate i true)))
      = pair (List.replicate (F.famRotVal hd n (v, i)).1 true)
        (List.replicate (F.famRotVal hd n (v, i)).2 true) := by
  have hrep : (List.replicate n true).length = n := List.length_replicate
  have hdpos : 0 < F.fitD := F.fitD_pos
  have hN : (sizeFn (F.deg ^ 4) p (List.replicate n true)).length = F.fitN hd n :=
    F.sizeFn_fitN p hd n hp
  have hT : F.famTableFn p (List.replicate n true) = F.table (F.fitLevel hd n) :=
    F.famTableFn_eq p hd n hp
  have hm : (divFn2 (pair (List.replicate n true)
      (sizeFn (F.deg ^ 4) p (List.replicate n true))) ++ [true]).length = F.wid hd n := by
    rw [divFn2_eq, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil, hrep, hN, wid, RegGraph.mergeWidth]
  have hs : (divC F.fitD (List.replicate i true)) = List.replicate (i / F.fitD) true := by
    rw [divC_eq, List.length_replicate]
  have hc : (modC F.fitD (List.replicate i true)) = List.replicate (i % F.fitD) true := by
    rw [modC_eq, List.length_replicate]
  have hlift : (List.replicate v true
      ++ mulLen (divC F.fitD (List.replicate i true)) (List.replicate n true)).length
      = v + i / F.fitD * n := by
    rw [List.length_append, List.length_replicate, length_mulLen, hs, hrep,
      List.length_replicate]
  rw [famRotFn, famRotVal]
  simp only [pairFst_pair, pairSnd_pair]
  by_cases h1 : i < F.wid hd n * F.fitD
  · rw [ite_eq_left h1, ifLtLen_pos (by
      rw [List.length_replicate, length_mulLen, hm, List.length_replicate]
      exact h1)]
    by_cases h2 : v + i / F.fitD * n < F.fitN hd n
    · rw [ite_eq_left h2, ifLtLen_pos (by rw [hlift, hN]; exact h2)]
      have hidx : (mulLen (List.replicate v true
            ++ mulLen (divC F.fitD (List.replicate i true)) (List.replicate n true))
          (List.replicate F.fitD true) ++ modC F.fitD (List.replicate i true)).length
          = (v + i / F.fitD * n) * F.fitD + i % F.fitD := by
        rw [List.length_append, length_mulLen, hlift, List.length_replicate, hc,
          List.length_replicate]
      have hclt : i % F.fitD < F.deg ^ 2 := Nat.mod_lt _ hdpos
      have hbound : (v + i / F.fitD * n) * F.fitD + i % F.fitD
          < F.size (F.fitLevel hd n) * F.deg ^ 2 := by
        have hfitN : F.fitN hd n = F.size (F.fitLevel hd n) := rfl
        rw [hfitN] at h2
        have hsucc : (v + i / F.fitD * n) + 1 ≤ F.size (F.fitLevel hd n) := h2
        have hclt' : i % F.fitD < F.fitD := Nat.mod_lt _ hdpos
        show (v + i / F.fitD * n) * F.fitD + i % F.fitD < F.size (F.fitLevel hd n) * F.fitD
        calc (v + i / F.fitD * n) * F.fitD + i % F.fitD
            < (v + i / F.fitD * n) * F.fitD + F.fitD := by omega
          _ = ((v + i / F.fitD * n) + 1) * F.fitD := by ring
          _ ≤ F.size (F.fitLevel hd n) * F.fitD := Nat.mul_le_mul_right _ hsucc
      rw [hT, hidx, F.tableFst_table hbound, F.tableSnd_table hbound,
        show F.deg ^ 2 = F.fitD from rfl,
        mul_add_div_of_lt hdpos (Nat.mod_lt _ hdpos), Nat.mul_add_mod_of_lt (Nat.mod_lt _ hdpos)]
      refine congrArg₂ pair ?_ ?_
      · rw [marks_eq, modFn2_eq,
          List.length_replicate, hrep, List.length_replicate]
      · rw [marks_eq, List.length_append, List.length_replicate,
          length_mulC, divFn2_eq, List.length_replicate, hrep,
          List.length_replicate]
        exact congrArg (List.replicate · true) (by ring)
    · rw [ite_eq_right h2, ifLtLen_neg (by rw [hlift, hN]; exact h2)]
      refine congrArg₂ pair ?_ ?_
      · rw [marks_eq, List.length_replicate]
      · rw [marks_eq, List.length_replicate]
  · rw [ite_eq_right h1, ifLtLen_neg (by
      rw [List.length_replicate, length_mulLen, hm, List.length_replicate]
      exact h1)]
    refine congrArg₂ pair ?_ ?_
    · rw [marks_eq, List.length_replicate]
    · rw [marks_eq, List.length_replicate]

end FinBase

end Complexity

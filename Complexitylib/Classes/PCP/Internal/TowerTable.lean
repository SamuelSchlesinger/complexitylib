/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.TowerFin
public import Complexitylib.Classes.PCP.Internal.Materialize
public import Complexitylib.Classes.P.FinsetDomain
public import Complexitylib.Classes.PCP.Internal.FiniteKey

/-!
# The tower's rotation table

`TowerFin` gives the tower's rotation map as arithmetic on numbers; this module
runs that arithmetic. A level is held as a table — one record for each vertex
and dart, holding the vertex reached and the label to come back by, both in
unary — and one level is computed from the one below by writing a new table
whose every record needs two lookups in the old one.

The base graph's own rotation map is a table on a bounded key, so it is
polynomial time however it was chosen (`FiniteKey`).

## Main definitions

- `Complexity.FinBase.tableList`, `Complexity.FinBase.table` — a level's table
- `Complexity.FinBase.baseRec` — the base's rotation map, as a record
- `Complexity.FinBase.stepRec` — one record of the next level

## Main results

- `Complexity.FinBase.baseRec_mem_FP`, `Complexity.FinBase.stepRec_mem_FP`
- `Complexity.FinBase.stepRec_eq` — the rule computes the level above
- `Complexity.FinBase.tableStep_eq`, `Complexity.FinBase.tableStep_mem_FP` — and
  writing out every record climbs one level
- `Complexity.FinBase.table_mem_FP` — so the table of any level is polynomial
  time, given room for it
-/

@[expose] public section

namespace Complexity

theorem mul_add_div_of_lt {a b c : ℕ} (hc : 0 < c) (h : b < c) : (a * c + b) / c = a := by
  rw [show a * c + b = b + c * a by ring, Nat.add_mul_div_left _ _ hc,
    Nat.div_eq_of_lt h, Nat.zero_add]

theorem mul_add_mod_of_lt {a b c : ℕ} (h : b < c) : (a * c + b) % c = b := by
  rw [show a * c + b = b + c * a by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

namespace FinBase

variable (F : FinBase)

/-! ### The table -/

/-- The records of the level-`k` table: for each vertex and dart, the vertex
reached and the label pointing back, both in unary. -/
noncomputable def tableList (k : ℕ) : List (List Bool × List Bool) :=
  (List.range (F.size k * F.deg ^ 2)).map fun j =>
    (List.replicate (F.rotVal k (j / F.deg ^ 2, j % F.deg ^ 2)).1 true,
      List.replicate (F.rotVal k (j / F.deg ^ 2, j % F.deg ^ 2)).2 true)

@[simp] theorem length_tableList (k : ℕ) :
    (F.tableList k).length = F.size k * F.deg ^ 2 := by
  rw [tableList, List.length_map, List.length_range]

/-- The level-`k` table. -/
noncomputable def table (k : ℕ) : List Bool := DataEncode.bitstringEncode (F.tableList k)

theorem tableFst_table {k j : ℕ} (hj : j < F.size k * F.deg ^ 2) :
    tableFst (F.table k) j
      = List.replicate (F.rotVal k (j / F.deg ^ 2, j % F.deg ^ 2)).1 true := by
  rw [table]
  refine tableFst_eq (l := F.tableList k)
    (c := (F.rotVal k (j / F.deg ^ 2, j % F.deg ^ 2)).2)
    (by rw [length_tableList]; exact hj) ?_
  simp only [tableList, List.getElem_map, List.getElem_range]

theorem tableSnd_table {k j : ℕ} (hj : j < F.size k * F.deg ^ 2) :
    tableSnd (F.table k) j
      = List.replicate (F.rotVal k (j / F.deg ^ 2, j % F.deg ^ 2)).2 true := by
  rw [table]
  refine tableSnd_eq (l := F.tableList k)
    (w := (F.rotVal k (j / F.deg ^ 2, j % F.deg ^ 2)).1)
    (by rw [length_tableList]; exact hj) ?_
  simp only [tableList, List.getElem_map, List.getElem_range]

/-! ### The base graph's own table -/

/-- The record the base's rotation map gives, before the key is bounded. -/
noncomputable def baseRaw (z : List Bool) : List Bool :=
  encPair
    (List.replicate
      (F.baseVal (pairFst z).length (pairSnd z).length).1 true)
    (List.replicate
      (F.baseVal (pairFst z).length (pairSnd z).length).2 true)

/-- How long an argument to the base's table can be. -/
def baseKeyBound : ℕ := 2 * F.deg ^ 4 + 2 + F.deg

/-- **The base's rotation map, as a record.** -/
noncomputable def baseRec (z : List Bool) : List Bool :=
  if z ∈ keySet F.baseKeyBound (fun _ => True) then F.baseRaw z else []

theorem baseRec_mem_FP : F.baseRec ∈ FP :=
  ite_mem_finset_mem_FP F.baseRaw (keySet F.baseKeyBound (fun _ => True))

theorem baseRec_eq {x a : ℕ} (hx : x < F.deg ^ 4) (ha : a < F.deg) :
    F.baseRec (pair (List.replicate x true) (List.replicate a true))
      = encPair (List.replicate (F.baseVal x a).1 true)
          (List.replicate (F.baseVal x a).2 true) := by
  have hlen : (pair (List.replicate x true) (List.replicate a true)).length
      ≤ F.baseKeyBound := by
    rw [pair_length, List.length_replicate, List.length_replicate, baseKeyBound]
    omega
  rw [baseRec, ite_eq_left (mem_keySet.mpr ⟨hlen, trivial⟩), baseRaw,
    pairFst_pair, pairSnd_pair, List.length_replicate,
    List.length_replicate]

/-! ### One record of the next level -/

/-- One record of the level above, from the table below. The argument is
`pair table (unary index)`: the index splits into a vertex and a dart, the
vertex into a vertex of the level below and a base vertex, and the dart into two
base darts. -/
noncomputable def stepRec (z : List Bool) : List Bool :=
  let T := pairFst z
  let J := pairSnd z
  let V := divC (F.deg ^ 2) J
  let I := modC (F.deg ^ 2) J
  let U := divC (F.deg ^ 4) V
  let X := modC (F.deg ^ 4) V
  let A := divC F.deg I
  let B := modC F.deg I
  let P := F.baseRec (pair X A)
  let P1 := unaryOf (fstEnc P)
  let P2 := unaryOf (sndEnc P)
  let Q0 := posAt T (mulC (F.deg ^ 2) U ++ divC (F.deg ^ 2) P1).length
  let W0 := unaryOf (fstEnc Q0)
  let C0 := unaryOf (sndEnc Q0)
  let Q1 := posAt T (mulC (F.deg ^ 2) W0 ++ modC (F.deg ^ 2) P1).length
  let W1 := unaryOf (fstEnc Q1)
  let C1 := unaryOf (sndEnc Q1)
  let R := F.baseRec (pair (marks (C0 ++ mulC (F.deg ^ 2) C1)) B)
  let R1 := unaryOf (fstEnc R)
  let R2 := unaryOf (sndEnc R)
  encPair (marks (R1 ++ mulC (F.deg ^ 4) W1)) (marks (P2 ++ mulC F.deg R2))

theorem stepRec_mem_FP : F.stepRec ∈ FP := by
  have hT := Cobham.fstBlock_mem_FP
  have hJ := Cobham.sndBlock_mem_FP
  have hV := divC_mem_FP hJ (F.deg ^ 2)
  have hI := modC_mem_FP hJ (F.deg ^ 2)
  have hU := divC_mem_FP hV (F.deg ^ 4)
  have hX := modC_mem_FP hV (F.deg ^ 4)
  have hA := divC_mem_FP hI F.deg
  have hB := modC_mem_FP hI F.deg
  have hP := mem_FP_comp (Cobham.pairFn_mem_FP hX hA) F.baseRec_mem_FP
  have hP1 := unaryOf_mem_FP (fstEnc_mem_FP hP)
  have hP2 := unaryOf_mem_FP (sndEnc_mem_FP hP)
  have hIdx0 := Cobham.appendFn_mem_FP (mulC_mem_FP hU (F.deg ^ 2))
    (divC_mem_FP hP1 (F.deg ^ 2))
  have hQ0 := posAt_mem_FP hIdx0 hT
  have hW0 := unaryOf_mem_FP (fstEnc_mem_FP hQ0)
  have hC0 := unaryOf_mem_FP (sndEnc_mem_FP hQ0)
  have hIdx1 := Cobham.appendFn_mem_FP (mulC_mem_FP hW0 (F.deg ^ 2))
    (modC_mem_FP hP1 (F.deg ^ 2))
  have hQ1 := posAt_mem_FP hIdx1 hT
  have hW1 := unaryOf_mem_FP (fstEnc_mem_FP hQ1)
  have hC1 := unaryOf_mem_FP (sndEnc_mem_FP hQ1)
  have hRarg := Cobham.pairFn_mem_FP
    (marks_mem_FP (Cobham.appendFn_mem_FP hC0 (mulC_mem_FP hC1 (F.deg ^ 2)))) hB
  have hR := mem_FP_comp hRarg F.baseRec_mem_FP
  have hR1 := unaryOf_mem_FP (fstEnc_mem_FP hR)
  have hR2 := unaryOf_mem_FP (sndEnc_mem_FP hR)
  have hOut := encPair_mem_FP
    (marks_mem_FP (Cobham.appendFn_mem_FP hR1 (mulC_mem_FP hW1 (F.deg ^ 4))))
    (marks_mem_FP (Cobham.appendFn_mem_FP hP2 (mulC_mem_FP hR2 F.deg)))
  exact mem_FP_of_eq hOut fun _ => rfl

/-- **The record rule computes the level above.** -/
theorem stepRec_eq {k j : ℕ} (hj : j < F.size (k + 1) * F.deg ^ 2) :
    F.stepRec (pair (F.table k) (List.replicate j true))
      = encPair
          (List.replicate (F.rotVal (k + 1) (j / F.deg ^ 2, j % F.deg ^ 2)).1 true)
          (List.replicate (F.rotVal (k + 1) (j / F.deg ^ 2, j % F.deg ^ 2)).2 true) := by
  have hd1 : 0 < F.deg := F.deg_pos
  have hd2 : 0 < F.deg ^ 2 := F.sq_pos
  have hd4 : 0 < F.deg ^ 4 := pow_pos F.deg_pos 4
  have hsq : F.deg ^ 4 = F.deg ^ 2 * F.deg ^ 2 := by ring
  -- the vertex and the dart
  have hvlt : j / F.deg ^ 2 < F.size (k + 1) := (Nat.div_lt_iff_lt_mul hd2).mpr hj
  have hxlt : j / F.deg ^ 2 % F.deg ^ 4 < F.deg ^ 4 := Nat.mod_lt _ hd4
  have halt : j % F.deg ^ 2 / F.deg < F.deg := by
    refine (Nat.div_lt_iff_lt_mul hd1).mpr ?_
    have := Nat.mod_lt j hd2
    nlinarith [this]
  have hult : j / F.deg ^ 2 / F.deg ^ 4 < F.size k := by
    refine (Nat.div_lt_iff_lt_mul hd4).mpr ?_
    rw [← F.size_succ k]
    exact hvlt
  -- the base turn
  obtain ⟨p1, p2, hp⟩ : ∃ p1 p2,
      F.baseVal (j / F.deg ^ 2 % F.deg ^ 4) (j % F.deg ^ 2 / F.deg) = (p1, p2) := ⟨_, _, rfl⟩
  have hp1 : p1 < F.deg ^ 4 := by
    have := (F.baseVal_lt hxlt halt).1
    rwa [hp] at this
  rw [stepRec]
  simp only [pairFst_pair, pairSnd_pair, divC_eq hd2, modC_eq hd2,
    divC_eq hd4, modC_eq hd4, divC_eq hd1, modC_eq hd1, List.length_replicate,
    F.baseRec_eq hxlt halt, hp, unaryOf_fstEnc_encPair, unaryOf_sndEnc_encPair,
    length_mulC_append, ← tableFst_def, ← tableSnd_def]
  -- the first lookup
  have hs0 : p1 / F.deg ^ 2 < F.deg ^ 2 :=
    (Nat.div_lt_iff_lt_mul hd2).mpr (by rw [← hsq]; exact hp1)
  have hs1 : p1 % F.deg ^ 2 < F.deg ^ 2 := Nat.mod_lt _ hd2
  have hidx0 : j / F.deg ^ 2 / F.deg ^ 4 * F.deg ^ 2 + p1 / F.deg ^ 2 < F.size k * F.deg ^ 2 := by
    have h2 : j / F.deg ^ 2 / F.deg ^ 4 + 1 ≤ F.size k := hult
    nlinarith
  obtain ⟨w0, c0, hq0⟩ : ∃ w0 c0,
      F.rotVal k (j / F.deg ^ 2 / F.deg ^ 4, p1 / F.deg ^ 2) = (w0, c0) := ⟨_, _, rfl⟩
  have hw0 : w0 < F.size k := by
    have := (F.rotVal_lt k hult hs0).1
    rwa [hq0] at this
  have hc0 : c0 < F.deg ^ 2 := by
    have := (F.rotVal_lt k hult hs0).2
    rwa [hq0] at this
  rw [F.tableFst_table hidx0, F.tableSnd_table hidx0,
    mul_add_div_of_lt hd2 hs0, mul_add_mod_of_lt hs0, hq0]
  simp only [length_mulC_append]
  -- the second lookup
  have hidx1 : w0 * F.deg ^ 2 + p1 % F.deg ^ 2 < F.size k * F.deg ^ 2 := by
    have h2 : w0 + 1 ≤ F.size k := hw0
    nlinarith
  obtain ⟨w1, c1, hq1⟩ : ∃ w1 c1,
      F.rotVal k (w0, p1 % F.deg ^ 2) = (w1, c1) := ⟨_, _, rfl⟩
  have hc1 : c1 < F.deg ^ 2 := by
    have := (F.rotVal_lt k hw0 hs1).2
    rwa [hq1] at this
  rw [F.tableFst_table hidx1, F.tableSnd_table hidx1,
    mul_add_div_of_lt hd2 hs1, mul_add_mod_of_lt hs1, hq1]
  simp only [marks_append_mulC]
  -- the base turn back
  have hblt : j % F.deg ^ 2 % F.deg < F.deg := Nat.mod_lt _ hd1
  have hrlt : c0 + F.deg ^ 2 * c1 < F.deg ^ 4 := by
    rw [hsq]
    nlinarith
  rw [show c0 + c1 * F.deg ^ 2 = c0 + F.deg ^ 2 * c1 from by ring]
  obtain ⟨r1, r2, hr⟩ : ∃ r1 r2,
      F.baseVal (c0 + F.deg ^ 2 * c1) (j % F.deg ^ 2 % F.deg) = (r1, r2) := ⟨_, _, rfl⟩
  rw [F.baseRec_eq hrlt hblt, hr]
  simp only [unaryOf_fstEnc_encPair, unaryOf_sndEnc_encPair, marks_append_mulC]
  simp only [rotVal, hp, hq0, hq1, hr]
  rw [show r1 + w1 * F.deg ^ 4 = r1 + F.deg ^ 4 * w1 from by ring,
    show p2 + r2 * F.deg = p2 + F.deg * r2 from by ring]

/-! ### One level of the table -/

/-- **One level of the table**: write out every record of the level above. -/
noncomputable def tableStep (T : List Bool) : List Bool :=
  listEncFn F.stepRec (pair (marks (mulC (F.deg ^ 4) (posCount T))) T)

theorem tableStep_mem_FP : F.tableStep ∈ FP := by
  have hcount := marks_mem_FP (mulC_mem_FP (posCount_mem_FP id_mem_FP) (F.deg ^ 4))
  have harg := Cobham.pairFn_mem_FP hcount id_mem_FP
  exact mem_FP_of_eq (mem_FP_comp harg (materialize_mem_FP F.stepRec_mem_FP)) fun _ => rfl

theorem tableStep_eq (k : ℕ) : F.tableStep (F.table k) = F.table (k + 1) := by
  have hcount : marks (mulC (F.deg ^ 4) (posCount (F.table k)))
      = List.replicate (F.tableList (k + 1)).length true := by
    rw [table, posCount_eq, marks_eq, length_mulC, List.length_replicate, length_tableList,
      length_tableList, F.size_succ k]
    ring_nf
  rw [tableStep, hcount, table]
  refine materialize_eq (F.tableList (k + 1)) (F.table k) fun i hi => ?_
  rw [length_tableList] at hi
  rw [F.stepRec_eq hi]
  simp only [tableList, List.getElem_map, List.getElem_range]
  rw [encPair_eq]

/-- How long a level's table is: one record a vertex and dart, and a record
holds two numbers below the level's size. -/
theorem length_table_le (l : ℕ) :
    (F.table l).length
      ≤ 2 + F.size l * F.deg ^ 2 * (4 * F.size l + 4 * F.deg ^ 2 + 6) := by
  rw [table, length_bitstringEncode_list]
  have hbound : ∀ x ∈ (F.tableList l).map
      (fun a => (DataEncode.bitstringEncode a).length),
      x ≤ 4 * F.size l + 4 * F.deg ^ 2 + 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [tableList, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hv : j / F.deg ^ 2 < F.size l := (Nat.div_lt_iff_lt_mul F.sq_pos).mpr hj
    have hi : j % F.deg ^ 2 < F.deg ^ 2 := Nat.mod_lt _ F.sq_pos
    have hlt := F.rotVal_lt l hv hi
    rw [← encPair_eq, length_encPair]
    omega
  have hsum := List.sum_le_length_nsmul _ _ hbound
  rw [List.length_map, length_tableList] at hsum
  simp only [smul_eq_mul] at hsum
  omega

/-! ### Climbing to a level -/

theorem tableStep_iterate : ∀ l : ℕ, F.tableStep^[l] (F.table 0) = F.table l
  | 0 => rfl
  | l + 1 => by
      rw [Function.iterate_succ_apply', tableStep_iterate l, tableStep_eq]

/-- **The table of a requested level is polynomial time**, as soon as there is
room to write it down. -/
theorem table_mem_FP {ruler width : List Bool → List Bool} (hr : ruler ∈ FP) (hw : width ∈ FP)
    (hbound : ∀ z, ∀ l ≤ (ruler z).length, (F.table l).length ≤ (width z).length) :
    (fun z => F.table (ruler z).length) ∈ FP := by
  have hiter := Cobham.iterate_mem_FP F.tableStep_mem_FP (constFn_mem_FP (F.table 0)) hr hw
    (fun z l hl => by rw [F.tableStep_iterate l]; exact hbound z l hl)
  exact mem_FP_of_eq hiter fun z => by rw [F.tableStep_iterate]

end FinBase

end Complexity

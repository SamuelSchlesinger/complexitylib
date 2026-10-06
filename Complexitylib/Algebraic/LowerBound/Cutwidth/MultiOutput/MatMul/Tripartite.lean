/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite.Internal

/-!
# The terminal graph of matrix multiplication

The terminals of `n × n` matrix multiplication `C = A B` are the edges of the complete
tripartite graph on three copies `I`, `J`, `K` of `Fin n` (`Tripartite.Defs`): `A i j` joins
`i` and `j`, `B j k` joins `j` and `k`, `C i k` joins `i` and `k`. A split of the wires of a
circuit places `d v` of the `2 n` terminals at each vertex `v`, and the *minority*
`g (d) = min (d, 2 n - d)` is the smaller of the two counts. The sums of `g` over `I`, `J` and
`K` are the charges `R_I`, `R_J`, `R_K`; for matrix multiplication they bound the ranks of the
linear maps obtained by fixing `B` (`R_I`), by fixing `A` (`R_K`), and the cross block of the
Hessian of a combination of the outputs (`R_J`), so each is at most the number of signals
crossing the split. This file proves the combinatorics, independently of circuits.

**Charging** (`lightHeavy_le_charge`). Call a vertex *heavy* when `d v ≥ n`. A terminal with a
light endpoint `u` and a heavy endpoint `v` is charged to `u` if it is placed, and to `v`
otherwise: at a light vertex `g` counts the placed terminals, at a heavy one the unplaced ones.
So the number `P` of light–heavy terminals is at most `R_I + R_J + R_K`.

**Counting** (`card_mixedPairs`, `three_mul_sq_le_two_mul_lightHeavy`). With `x`, `y`, `z` heavy
vertices in `I`, `J`, `K` and `h = x + y + z`, `P = 2 n h - 2 (x y + y z + z x)`, which is at least
`2 n h - 2 h² / 3`. If `3 n ≤ 2 h ≤ 3 n + 3`, this gives `3 n² ≤ 2 P + 3`, so
`3 n² ≤ 2 (R_I + R_J + R_K) + 3` (`three_mul_sq_le_two_mul_charge`): one of the three charges is
at least `(n² - 1)/2`.

**The threshold prefix** (`exists_threshold`). The degrees sum to twice the number of placed
terminals, so placing one more terminal adds at most two heavy vertices
(`heavyCount_le_add_two`). Along an injective ranking of the wires of a circuit whose `3 n²`
terminals lie on distinct wires, the heavy count of the prefixes thus climbs from `0` to `3 n`
in steps of at most two, and the first prefix with at least `⌈3 n/2⌉` heavy vertices ends at a
terminal and satisfies `3 n ≤ 2 h ≤ 3 n + 3`.

**Exploratory probes** (`probeIJ`, `twoSubsetProbeIJ`). These are bookkeeping definitions for a
possible combined `I`/`J` charge, recorded with the identities that relate them to the existing
charges; they are not used by any lower bound. At `i ∈ I` the minority splits as
`minority n (r + s) = min r (n - s) + min (n - r) s` (`minority_add_eq`), with `r` and `s` the
placed `A`- and `C`-terminals at `i`; at `j ∈ J` it splits likewise, with the `A`- and
`B`-terminals at `j`. `twoSubsetProbeIJ a b c I₀ I₁` counts the first `I`-summand over `I₀`, the
second over `I₁`, and the two `J`-summands with their `A`-terminals restricted to the rows of
`I₀ᶜ` and `I₁ᶜ`; `probeIJ a b c I₀` is the case `I₀ = I₁` (`twoSubsetProbeIJ_self`), and equals
`chargeJ` for `I₀ = ∅` and `chargeI` for `I₀ = univ` (`probeIJ_empty`, `probeIJ_univ`). Each
summand `min x (n - y)` or `min x y` falls short of `x` by `x + y - n` or `x - y`, and the `x`
add up to the `n²` entries of `A`, giving `twoSubsetProbeIJ + (shortfalls) = n²`
(`twoSubsetProbeIJ_add_eq`). For `I₀ = (heavyI a c)ᶜ`, `I₁ = heavyI a c` the `I`-shortfalls
vanish (`twoSubsetProbeIJ_compl_heavyI_add_eq`), and the probe is at least the number of
light–heavy `A`-terminals (`card_mixedPairs_le_twoSubsetProbeIJ`).

No theorem in the library bounds the number of signals crossing a split below by `probeIJ` or
`twoSubsetProbeIJ`: their `I`- and `J`-summands come from ranks of different linear maps (a
Jacobian and a Hessian block), which are not known to add. In particular these probes do not
improve the matrix-multiplication bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Tripartite

variable {n : Nat}

/-! ## The minority function -/

/-- At a light vertex the minority is the number of placed terminals. -/
theorem minority_of_lt {d : Nat} (h : d < n) : minority n d = d :=
  Internal.minority_of_lt h

/-- At a heavy vertex the minority is the number of unplaced terminals. -/
theorem minority_of_le {d : Nat} (h : n ≤ d) : minority n d = 2 * n - d :=
  Internal.minority_of_le h

/-- At a vertex whose `2 n` terminals form two groups of `n`, with `x` and `y` of them placed,
the minority is `min x (n - y) + min (n - x) y`. -/
theorem minority_add_eq {x y : Nat} (hx : x ≤ n) (hy : y ≤ n) :
    minority n (x + y) = min x (n - y) + min (n - x) y :=
  Internal.minority_add_eq hx hy

/-- The minority, the excess `d - n` and the deficit `n - d` of `d ≤ 2 n` add up to `n`. -/
theorem minority_add_excess_add_deficit {d : Nat} (hd : d ≤ 2 * n) :
    minority n d + (d - n) + (n - d) = n :=
  Internal.minority_add_excess_add_deficit hd

/-! ## Charging -/

/-- The rows of a set of index pairs partition it. -/
theorem sum_card_row (a : Finset (Fin n × Fin n)) : ∑ i, (rowSet a i).card = a.card :=
  Internal.sum_card_row a

/-- The columns of a set of index pairs partition it. -/
theorem sum_card_col (a : Finset (Fin n × Fin n)) : ∑ j, (colSet a j).card = a.card :=
  Internal.sum_card_col a

/-- **Charging.** The terminals with exactly one heavy endpoint number at most
`R_I + R_J + R_K`. -/
theorem lightHeavy_le_charge (a b c : Finset (Fin n × Fin n)) :
    lightHeavy a b c ≤ chargeI a c + chargeJ a b + chargeK b c :=
  Internal.lightHeavy_le_charge a b c

/-- The mixed pairs of `X` and `Y` number `|X| (n - |Y|) + (n - |X|) |Y|`. -/
theorem card_mixedPairs (X Y : Finset (Fin n)) :
    (mixedPairs X Y).card = X.card * (n - Y.card) + (n - X.card) * Y.card :=
  Internal.card_mixedPairs X Y

/-- **The light–heavy terminals near the threshold.** If the heavy vertices number `h` with
`3 n ≤ 2 h ≤ 3 n + 3`, the light–heavy terminals number `P` with `3 n² ≤ 2 P + 3`. -/
theorem three_mul_sq_le_two_mul_lightHeavy (a b c : Finset (Fin n × Fin n))
    (hlo : 3 * n ≤ 2 * heavyCount a b c) (hhi : 2 * heavyCount a b c ≤ 3 * n + 3) :
    3 * n ^ 2 ≤ 2 * lightHeavy a b c + 3 :=
  Internal.three_mul_sq_le_two_mul_lightHeavy a b c hlo hhi

/-- **The charging inequality.** If the heavy vertices number `h` with `3 n ≤ 2 h ≤ 3 n + 3`,
then `3 n² ≤ 2 (R_I + R_J + R_K) + 3`. -/
theorem three_mul_sq_le_two_mul_charge (a b c : Finset (Fin n × Fin n))
    (hlo : 3 * n ≤ 2 * heavyCount a b c) (hhi : 2 * heavyCount a b c ≤ 3 * n + 3) :
    3 * n ^ 2 ≤ 2 * (chargeI a c + chargeJ a b + chargeK b c) + 3 :=
  Internal.three_mul_sq_le_two_mul_charge a b c hlo hhi

/-! ## The threshold prefix -/

/-- **One more terminal adds at most two heavy vertices.** -/
theorem heavyCount_le_add_two {a b c a' b' c' : Finset (Fin n × Fin n)} (ha : a ⊆ a')
    (hb : b ⊆ b') (hc : c ⊆ c')
    (hcard : a'.card + b'.card + c'.card ≤ a.card + b.card + c.card + 1) :
    heavyCount a' b' c' ≤ heavyCount a b c + 2 :=
  Internal.heavyCount_le_add_two ha hb hc hcard

/-- **The threshold prefix.** Let the terminals `tA`, `tB`, `tC` of `n × n` matrix multiplication,
`n ≥ 1`, lie on distinct wires, and rank the wires injectively below `T`. Some prefix of the
ranking ends at a terminal, ranked `t`, and the wires ranked below `t + 1` have `h` heavy
vertices with `3 n ≤ 2 h ≤ 3 n + 3`. -/
theorem exists_threshold {N s : Nat} (hn : 0 < n) (tA tB tC : Fin n × Fin n → Wire N s)
    (hinj : Function.Injective (Sum.elim tA (Sum.elim tB tC))) (rank : Wire N s → Nat)
    (hrank : Function.Injective rank) (T : Nat) (hT : ∀ w, rank w < T) :
    ∃ t, (∃ x, rank (Sum.elim tA (Sum.elim tB tC) x) = t) ∧
      3 * n ≤ 2 * heavyCount (place tA (prefixBelow rank (t + 1)))
        (place tB (prefixBelow rank (t + 1))) (place tC (prefixBelow rank (t + 1))) ∧
      2 * heavyCount (place tA (prefixBelow rank (t + 1)))
        (place tB (prefixBelow rank (t + 1))) (place tC (prefixBelow rank (t + 1))) ≤
        3 * n + 3 :=
  Internal.exists_threshold hn tA tB tC hinj rank hrank T hT

/-! ## Exploratory probes mixing the `I` and `J` charges -/

/-- The rows `i ∈ R` split at `j` into those with `A i j` placed and those with it unplaced. -/
theorem card_colSetIn_add_card_complColSetIn (a : Finset (Fin n × Fin n)) (R : Finset (Fin n))
    (j : Fin n) :
    (colSetIn a R j).card + (complColSetIn a R j).card = R.card :=
  Internal.card_colSetIn_add_card_complColSetIn a R j

/-- Column `j` of `a` splits into its rows in `R` and in `Rᶜ`. -/
theorem card_colSetIn_add_compl (a : Finset (Fin n × Fin n)) (R : Finset (Fin n)) (j : Fin n) :
    (colSetIn a R j).card + (colSetIn a Rᶜ j).card = (colSet a j).card :=
  Internal.card_colSetIn_add_compl a R j

/-- The complement of column `j` of `a` splits into its rows in `R` and in `Rᶜ`. -/
theorem card_complColSetIn_add_compl (a : Finset (Fin n × Fin n)) (R : Finset (Fin n))
    (j : Fin n) :
    (complColSetIn a R j).card + (complColSetIn a Rᶜ j).card = n - (colSet a j).card :=
  Internal.card_complColSetIn_add_compl a R j

/-- Double counting the pairs of `a` with first coordinate in `R`. -/
theorem sum_card_colSetIn (a : Finset (Fin n × Fin n)) (R : Finset (Fin n)) :
    ∑ j, (colSetIn a R j).card = ∑ i ∈ R, (rowSet a i).card :=
  Internal.sum_card_colSetIn a R

/-- Double counting the pairs outside `a` with first coordinate in `R`. -/
theorem sum_card_complColSetIn (a : Finset (Fin n × Fin n)) (R : Finset (Fin n)) :
    ∑ j, (complColSetIn a R j).card = ∑ i ∈ R, (n - (rowSet a i).card) :=
  Internal.sum_card_complColSetIn a R

/-- With no rows charged on the `I` side, `probeIJ` is `chargeJ`. -/
theorem probeIJ_empty (a b c : Finset (Fin n × Fin n)) :
    probeIJ a b c ∅ = chargeJ a b :=
  Internal.probeIJ_empty a b c

/-- With every row charged on the `I` side, `probeIJ` is `chargeI`. -/
theorem probeIJ_univ (a b c : Finset (Fin n × Fin n)) :
    probeIJ a b c Finset.univ = chargeI a c :=
  Internal.probeIJ_univ a b c

/-- `probeIJ` is the diagonal case of `twoSubsetProbeIJ`. -/
theorem twoSubsetProbeIJ_self (a b c : Finset (Fin n × Fin n)) (I₀ : Finset (Fin n)) :
    twoSubsetProbeIJ a b c I₀ I₀ = probeIJ a b c I₀ :=
  Internal.twoSubsetProbeIJ_self a b c I₀

/-- At `j ∈ J`, with `x = (colSetIn a I₀ᶜ j).card`, `x' = (complColSetIn a I₁ᶜ j).card` and
`y = (rowSet b j).card`, the summands `min x (n - y)` and `min x' y` of `twoSubsetProbeIJ` fall
short of `x` and `x'` by `x + y - n` and `x' - y`. -/
theorem min_colSetIn_add_min_complColSetIn_add_eq (a b : Finset (Fin n × Fin n))
    (I₀ I₁ : Finset (Fin n)) (j : Fin n) :
    min (colSetIn a I₀ᶜ j).card (n - (rowSet b j).card) +
      min (complColSetIn a I₁ᶜ j).card (rowSet b j).card +
      ((colSetIn a I₀ᶜ j).card + (rowSet b j).card - n) +
      ((complColSetIn a I₁ᶜ j).card - (rowSet b j).card) =
      (colSetIn a I₀ᶜ j).card + (complColSetIn a I₁ᶜ j).card :=
  Internal.min_colSetIn_add_min_complColSetIn_add_eq a b I₀ I₁ j

/-- The single-subset case of `min_colSetIn_add_min_complColSetIn_add_eq`: the two `J`-summands
at `j` restricted to the rows of `R`, plus their shortfalls, add up to `R.card`. -/
theorem min_colSetIn_add_min_complColSetIn_single_add_eq (a b : Finset (Fin n × Fin n))
    (R : Finset (Fin n)) (j : Fin n) :
    min (colSetIn a R j).card (n - (rowSet b j).card) +
      min (complColSetIn a R j).card (rowSet b j).card +
      (((colSetIn a R j).card + (rowSet b j).card - n) +
        ((complColSetIn a R j).card - (rowSet b j).card)) = R.card :=
  Internal.min_colSetIn_add_min_complColSetIn_single_add_eq a b R j

/-- Restricting the `A`-terminals at `j ∈ J` to the rows of `R` lowers the two summands of
`minority n (degJ a b j)` by at most `n - R.card` in total. -/
theorem minority_degJ_le_min_add_min_add_sub (a b : Finset (Fin n × Fin n))
    (R : Finset (Fin n)) (j : Fin n) :
    minority n (degJ a b j) ≤
      min (colSetIn a R j).card (n - (rowSet b j).card) +
        min (complColSetIn a R j).card (rowSet b j).card + (n - R.card) :=
  Internal.minority_degJ_le_min_add_min_add_sub a b R j

/-- **Bookkeeping identity for `twoSubsetProbeIJ`.** The probe plus the shortfalls of its
summands (the excesses over `I₀`, the deficits over `I₁`, and the `J`-shortfalls of
`min_colSetIn_add_min_complColSetIn_add_eq`) is `n²`. -/
theorem twoSubsetProbeIJ_add_eq (a b c : Finset (Fin n × Fin n)) (I₀ I₁ : Finset (Fin n)) :
    twoSubsetProbeIJ a b c I₀ I₁ +
      ∑ i ∈ I₀, excessI a c i + ∑ i ∈ I₁, deficitI a c i +
      ∑ j, (((colSetIn a I₀ᶜ j).card + (rowSet b j).card - n) +
        ((complColSetIn a I₁ᶜ j).card - (rowSet b j).card)) = n * n :=
  Internal.twoSubsetProbeIJ_add_eq a b c I₀ I₁

/-- The case `I₀ = I₁` of `twoSubsetProbeIJ_add_eq`, for `probeIJ`. -/
theorem probeIJ_add_eq (a b c : Finset (Fin n × Fin n)) (I₀ : Finset (Fin n)) :
    probeIJ a b c I₀ +
      ∑ i ∈ I₀, (excessI a c i + deficitI a c i) +
      ∑ j, (((colSetIn a I₀ᶜ j).card + (rowSet b j).card - n) +
        ((complColSetIn a I₀ᶜ j).card - (rowSet b j).card)) = n * n :=
  Internal.probeIJ_add_eq a b c I₀

/-- The case `I₀ = (heavyI a c)ᶜ`, `I₁ = heavyI a c` of `twoSubsetProbeIJ_add_eq`, where the
excesses over the light rows and the deficits over the heavy rows vanish. -/
theorem twoSubsetProbeIJ_compl_heavyI_add_eq (a b c : Finset (Fin n × Fin n)) :
    twoSubsetProbeIJ a b c (heavyI a c)ᶜ (heavyI a c) +
      ∑ j, (((colSetIn a (heavyI a c) j).card + (rowSet b j).card - n) +
        ((complColSetIn a (heavyI a c)ᶜ j).card - (rowSet b j).card)) = n * n :=
  Internal.twoSubsetProbeIJ_compl_heavyI_add_eq a b c

/-- The `A`-terminals with exactly one heavy endpoint number at most
`twoSubsetProbeIJ a b c (heavyI a c)ᶜ (heavyI a c)`: the charging of `lightHeavy_le_charge`,
restricted to the `A`-terminals, pays for each of them from one of the probe's summands. -/
theorem card_mixedPairs_le_twoSubsetProbeIJ (a b c : Finset (Fin n × Fin n)) :
    (mixedPairs (heavyI a c) (heavyJ a b)).card ≤
      twoSubsetProbeIJ a b c (heavyI a c)ᶜ (heavyI a c) :=
  Internal.card_mixedPairs_le_twoSubsetProbeIJ a b c

/-- `probeIJ a b c (heavyI a c)ᶜ` is at least the placed terminals at the light rows of `I`, plus,
at each `j ∈ J`, the `A`-terminals `A i j` with heavy `i` that are placed (for light `j`) or
unplaced (for heavy `j`). -/
theorem sum_light_heavy_le_probeIJ (a b c : Finset (Fin n × Fin n)) :
    (∑ i, if i ∈ heavyI a c then 0 else (rowSet a i).card + (rowSet c i).card) +
      (∑ j, if j ∈ heavyJ a b then ((colSet a j)ᶜ ∩ heavyI a c).card
        else (colSet a j ∩ heavyI a c).card) ≤
      probeIJ a b c (heavyI a c)ᶜ :=
  Internal.sum_light_heavy_le_probeIJ a b c

end Algebraic.Cutwidth.MultiOutput.Tripartite

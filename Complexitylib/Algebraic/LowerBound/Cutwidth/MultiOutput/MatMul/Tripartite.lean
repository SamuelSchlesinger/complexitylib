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
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.Tripartite

variable {n : Nat}

/-! ## The minority function -/

theorem minority_of_lt {d : Nat} (h : d < n) : minority n d = d :=
  Internal.minority_of_lt h

theorem minority_of_le {d : Nat} (h : n ≤ d) : minority n d = 2 * n - d :=
  Internal.minority_of_le h

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

end Algebraic.Cutwidth.MultiOutput.Tripartite

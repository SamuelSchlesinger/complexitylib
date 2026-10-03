/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting.Internal

/-!
# A finite entropy budget for splitting the paired condenser

Let `H` be the actual condenser half-width and `b` its field seed width.
The coordinate count proves `k ≤ 2*H`. Together with the output-rate bound,
the sufficient budget `u*(b+2*(s+E)) ≤ (u-1)*k` gives both `s ≤ H` and
`H+s+E ≤ k`. The condenser error exponent `e` and splitting error exponent
`E` remain independent.

These are arithmetic deductions for our sparse parameter choice. The two
target inequalities are the entropy requirements of the splitting step in
Chattopadhyay--Goodman--Liao, Corollary 5.4 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
This layer establishes one finite level's budget; choosing a recursive
sequence and bounding its total seed length remain separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual two-half output has capacity for all `k` input entropy bits. -/
theorem explicitCondenserHalfWidth_capacity (n k e : Nat) {u : Nat} (rate : 0 < u) :
    k ≤ explicitCondenserHalfWidth n k e u + explicitCondenserHalfWidth n k e u :=
  Internal.explicitCondenserHalfWidth_capacity n k e rate

/-- A field-width budget supplies both entropy inequalities needed for splitting. -/
theorem explicitCondenserPair_split_budget (n k e u s E : Nat) (rate : 1 < u)
    (budget : u * (sparseFieldBits u (explicitCondenserBudget n k e) +
        2 * (s + E)) ≤ (u - 1) * k) :
    s ≤ explicitCondenserHalfWidth n k e u ∧
      explicitCondenserHalfWidth n k e u + s + E ≤ k :=
  Internal.explicitCondenserPair_split_budget n k e u s E rate budget

/-- The explicit upper bound on field width gives a sufficient budget without sparse rounding. -/
theorem explicitCondenserPair_split_budget_of_bound (n k e u s E : Nat) (rate : 1 < u)
    (budget : u * (6 * (u + 1) * explicitCondenserBudget n k e +
        2 * (s + E)) ≤ (u - 1) * k) :
    s ≤ explicitCondenserHalfWidth n k e u ∧
      explicitCondenserHalfWidth n k e u + s + E ≤ k :=
  Internal.explicitCondenserPair_split_budget_of_bound n k e u s E rate budget

/-- The maximal next entropy `k-H-E` fits in one half and exactly exhausts the split budget.
The sufficient field-width budget ensures that natural subtraction does not truncate. -/
theorem explicitCondenserPair_next_entropy (n k e u E : Nat) (rate : 1 < u)
    (budget : u * (sparseFieldBits u (explicitCondenserBudget n k e) + 2 * E) ≤
      (u - 1) * k) :
    k - explicitCondenserHalfWidth n k e u - E ≤ explicitCondenserHalfWidth n k e u ∧
      explicitCondenserHalfWidth n k e u +
          (k - explicitCondenserHalfWidth n k e u - E) + E = k :=
  Internal.explicitCondenserPair_next_entropy n k e u E rate budget

end Algebraic.Cutwidth.Extractor

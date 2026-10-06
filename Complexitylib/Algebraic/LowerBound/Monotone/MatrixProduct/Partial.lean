/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan
import Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.Internal

/-!
# Monotone circuits for partial Boolean matrix products

Fix a set `T` of triples `(i, k, j)` with `i < I`, `k < K` and `j < J`. The
*partial Boolean matrix product* over `T` of an `I × K` matrix `x` and a `K × J`
matrix `y` has entries `z i j = ⋁ {x i k ∧ y k j | (i, k, j) ∈ T}`; the full
product is the case `T = univ`, and restricting the product to the supports
`E_X` of `x` and `E_Y` of `y` is the case
`T = {(i, k, j) | (i, k) ∈ E_X ∧ (k, j) ∈ E_Y}`. Every monotone circuit computing
it has at least `|T|` AND gates. This generalizes the monotone bound of
`Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct` (Pratt 1975;
Paterson 1975; Mehlhorn--Galil 1976; Wegener, *The Complexity of Boolean
Functions*, Theorem 6.8.1) along the same staged argument, whose counting never
uses the shape of `T`.

The circuit model is the imported library's De Morgan signature
(`DeMorgan.signature`: the constants, identity, NOT, and fan-in-two AND and OR,
with unbounded fan-out). A circuit is *monotone* when it has no NOT gate,
`circuit.cost DeMorgan.notCost = 0`; constants are allowed, so the model is
closed under substituting constants for inputs. AND gates are counted by
`DeMorgan.andCost`, which charges one per AND gate and nothing for every other
gate; every gate of the program is counted, used or not.

## Main results

* `card_le_andCost`: a monotone circuit computing the partial product over `T`,
  for any injective placement of the matrix entries among its inputs and any
  placement of the outputs, has at least `T.card` AND gates.

The proof is in `Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.Internal`.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace MatrixProduct

/-- **Monotone partial Boolean matrix product.** Place entry `(i, k)` of an
`I × K` matrix at input `x i k` and entry `(k, j)` of a `K × J` matrix at input
`y k j`, all at distinct inputs, and let `T` be a set of triples `(i, k, j)`. A
De Morgan circuit without NOT gates whose output `z i j` computes
`⋁ {x i k ∧ y k j | (i, k, j) ∈ T}` for every `i` and `j` has at least `|T|` AND
gates. -/
theorem card_le_andCost {N M I J K : Nat}
    (x : Fin I → Fin K → Fin N) (y : Fin K → Fin J → Fin N)
    (distinct : Function.Injective (Sum.elim (Function.uncurry x) (Function.uncurry y)))
    (T : Finset (Fin I × Fin K × Fin J))
    (z : Fin I → Fin J → Fin M) (circuit : Circuit DeMorgan.signature N M)
    (monotone : circuit.cost DeMorgan.notCost = 0)
    (computes : ∀ (a : Fin N → Bool) i j,
      circuit.eval DeMorgan.interpretation a (z i j) =
        decide (∃ k, (i, k, j) ∈ T ∧ a (x i k) = true ∧ a (y k j) = true)) :
    T.card ≤ circuit.cost DeMorgan.andCost :=
  Internal.card_le_andCost (.ofInjective x y distinct) T z circuit monotone computes

end MatrixProduct
end Monotone
end Algebraic

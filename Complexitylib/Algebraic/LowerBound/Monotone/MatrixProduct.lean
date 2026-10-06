/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AndOr
public import Mathlib.Logic.Equiv.Fin.Basic
import Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.Internal

/-!
# Monotone circuits for Boolean matrix product

The Boolean product of an `I × K` matrix `x` and a `K × J` matrix `y` has
entries `z i j = ⋁ k, x i k ∧ y k j`. Every circuit over the binary AND/OR basis
(`AndOr.signature`, which has neither negations nor constants) computing it has
at least `I * J * K` AND gates (Pratt 1975; Paterson 1975; Mehlhorn--Galil 1976;
see Wegener, *The Complexity of Boolean Functions*, Theorem 6.8.1). AND gates
are counted by `AndOr.andCost`, which charges one per AND gate and nothing per
OR gate; every gate of the program is counted, used or not. The schoolbook
circuit attains the bound.

## Main results

* `mul_mul_le_andCost`: the bound for any injective placement of the entries of
  `x` and `y` among the circuit inputs and any placement of the outputs.
* `cube_le_andCost`: for two `n × n` matrices in a fixed row-major layout,
  at least `n ^ 3` AND gates.

The proof is in `Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.Internal`.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace MatrixProduct

/-- **Monotone Boolean matrix product.** Place entry `(i, k)` of an `I × K`
matrix at input `x i k` and entry `(k, j)` of a `K × J` matrix at input `y k j`,
all at distinct inputs. An AND/OR circuit whose output `z i j` computes
`⋁ k, x i k ∧ y k j` for every `i` and `j` has at least `I * J * K` AND gates. -/
theorem mul_mul_le_andCost {N M I J K : Nat}
    (x : Fin I → Fin K → Fin N) (y : Fin K → Fin J → Fin N)
    (distinct : Function.Injective (Sum.elim (Function.uncurry x) (Function.uncurry y)))
    (z : Fin I → Fin J → Fin M) (circuit : Circuit AndOr.signature N M)
    (computes : ∀ (a : Fin N → Bool) i j,
      circuit.eval AndOr.boolInterpretation a (z i j) =
        decide (∃ k, a (x i k) = true ∧ a (y k j) = true)) :
    I * J * K ≤ circuit.cost AndOr.andCost :=
  Internal.mul_mul_le_andCost (.ofInjective x y distinct) z circuit computes

/-- The input carrying entry `(i, k)` of the left `n × n` matrix: the first
`n * n` inputs, in row-major order. -/
def leftEntry (n : Nat) (i k : Fin n) : Fin (n * n + n * n) :=
  Fin.castAdd (n * n) (finProdFinEquiv (i, k))

/-- The input carrying entry `(k, j)` of the right `n × n` matrix: the last
`n * n` inputs, in row-major order. -/
def rightEntry (n : Nat) (k j : Fin n) : Fin (n * n + n * n) :=
  Fin.natAdd (n * n) (finProdFinEquiv (k, j))

/-- The output carrying entry `(i, j)` of the product, in row-major order. -/
def productEntry (n : Nat) (i j : Fin n) : Fin (n * n) :=
  finProdFinEquiv (i, j)

/-- The row-major layout puts the entries of both matrices at distinct inputs. -/
theorem entry_injective (n : Nat) :
    Function.Injective (Sum.elim (Function.uncurry (leftEntry n))
      (Function.uncurry (rightEntry n))) := by
  rintro (⟨i, k⟩ | ⟨k, j⟩) (⟨i', k'⟩ | ⟨k', j'⟩) h <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Function.uncurry_apply_pair, leftEntry,
      rightEntry, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h
  · have := finProdFinEquiv.injective (Fin.ext h)
    simp_all
  · have := (finProdFinEquiv (i, k)).isLt
    omega
  · have := (finProdFinEquiv (i', k')).isLt
    omega
  · have := finProdFinEquiv.injective (Fin.ext (Nat.add_left_cancel h))
    simp_all

/-- **Monotone Boolean matrix product, square case.** An AND/OR circuit computing
the Boolean product of two `n × n` matrices has at least `n ^ 3` AND gates. -/
theorem cube_le_andCost (n : Nat) (circuit : Circuit AndOr.signature (n * n + n * n) (n * n))
    (computes : ∀ (a : Fin (n * n + n * n) → Bool) i j,
      circuit.eval AndOr.boolInterpretation a (productEntry n i j) =
        decide (∃ k, a (leftEntry n i k) = true ∧ a (rightEntry n k j) = true)) :
    n ^ 3 ≤ circuit.cost AndOr.andCost := by
  simpa [pow_succ, Nat.mul_assoc] using
    mul_mul_le_andCost (leftEntry n) (rightEntry n) (entry_injective n) (productEntry n)
      circuit computes

end MatrixProduct
end Monotone
end Algebraic

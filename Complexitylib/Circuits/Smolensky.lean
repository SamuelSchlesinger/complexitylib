/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Defs
public import Complexitylib.Circuits.Smolensky.Internal.Bound

/-!
# The Razborov–Smolensky lower bound

Parity is not computed by constant-depth, polynomial-size circuits of
unbounded-fan-in AND, OR, and `MOD_3` gates (`xorBool_not_mem_AC0Mod_three`).
The finite form is an explicit size–depth tradeoff
(`Smolensky.parity_size_lower_bound`): a circuit of depth at most `d` computing
`n`-bit parity has size at least `(2/5) · 2^ℓ` whenever `(40ℓ)^{2d} ≤ n`. Taking
`ℓ = ⌊n^{1/(2d)} / 40⌋`, the size is `2^{Ω(n^{1/(2d)})}`.

The circuits are the library's typed circuits over `Basis.unboundedAndOrMod 3`:
a `MOD_3` gate outputs `true` exactly when the number of its true inputs is not
divisible by `3`, negations are free per-input flags, the size `G + 1` counts the
internal gates and the output gate, and the depth counts the output gate.

The proof is Smolensky's approximation method over `ZMod 3`, with functions
`{0,1}^n → ZMod 3` in place of formal polynomials (`Smolensky.lowDegree`):

1. `Smolensky.exists_lowDegree_approx`: with a fixed choice of `ℓ` subsets of
   the inputs of each OR or AND gate, a depth-`d` circuit agrees with a function
   of degree at most `(2ℓ)^d` on all but `size · 2^n / 2^ℓ` inputs. The random
   choices of the usual proof are replaced by exact double counting over all
   tuples of subsets.
2. `Smolensky.card_agree_xorBool_le`: a function of degree at most `D` agrees
   with parity on at most as many inputs as there are subsets of at most
   `n / 2 + D` coordinates.
3. `Smolensky.ten_mul_card_le`: when `100 (t + 1)² ≤ n + 1`, at most `6/10` of all
   subsets have at most `n / 2 + t` coordinates.
-/


public section

namespace Complexity

namespace Smolensky

/-- **Smolensky's approximation theorem.** A single-output circuit of
unbounded-fan-in AND, OR, and `MOD_3` gates of depth at most `d` agrees with a
function `{0,1}^n → ZMod 3` of degree at most `(2ℓ)^d` on all but at most
`size · 2^n / 2^ℓ` inputs, for every `ℓ ≥ 1`. -/
theorem exists_lowDegree_approx {n G d ℓ : ℕ} [NeZero n]
    (C : Circuit (Basis.unboundedAndOrMod 3) n 1 G) (hdepth : C.depth ≤ d)
    (hℓ : 1 ≤ ℓ) :
    ∃ P ∈ lowDegree n ((2 * ℓ) ^ d),
      (Finset.univ.filter fun x => P x ≠ bitVal (C.eval x 0)).card * 2 ^ ℓ ≤
        C.size * 2 ^ n :=
  exists_lowDegree_approx_internal C hdepth hℓ

/-- **Parity is hard to approximate over `ZMod 3`.** A function of degree at
most `D` agrees with `n`-bit parity on at most as many inputs as there are
subsets of `Fin n` with at most `n / 2 + D` elements. -/
theorem card_agree_xorBool_le {n D : ℕ} {P : BitString n → ZMod 3}
    (hP : P ∈ lowDegree n D) :
    (Finset.univ.filter fun x => P x = bitVal (Schnorr.xorBool n x)).card ≤
      (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + D).card :=
  card_agree_xorBool_le_internal hP

/-- **Binomial estimate.** When `100 (t + 1)² ≤ n + 1`, at most `6/10` of the
subsets of `Fin n` have at most `n / 2 + t` elements. -/
theorem ten_mul_card_le (n t : ℕ) (h : 100 * (t + 1) ^ 2 ≤ n + 1) :
    10 * (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + t).card ≤
      6 * 2 ^ n :=
  ten_mul_card_le_internal n t h

/-- **Razborov–Smolensky, counting form.** If an AND/OR/`MOD_3` circuit of depth
at most `d` computes `n`-bit parity, then for every `ℓ ≥ 1`,
`2^ℓ · 2^n ≤ 2^ℓ · #{S ⊆ Fin n : |S| ≤ n / 2 + (2ℓ)^d} + size · 2^n`. -/
theorem parity_counting_bound {n G d ℓ : ℕ} [NeZero n]
    (C : Circuit (Basis.unboundedAndOrMod 3) n 1 G)
    (hcomputes : C.Computes (Schnorr.xorBool n)) (hdepth : C.depth ≤ d) (hℓ : 1 ≤ ℓ) :
    2 ^ ℓ * 2 ^ n ≤
      2 ^ ℓ * (Finset.univ.filter fun S : Finset (Fin n) =>
          S.card ≤ n / 2 + (2 * ℓ) ^ d).card +
        C.size * 2 ^ n :=
  parity_counting_bound_internal C hcomputes hdepth hℓ

/-- **Razborov–Smolensky size–depth tradeoff.** If an AND/OR/`MOD_3` circuit of
depth at most `d` computes `n`-bit parity and `(40ℓ)^{2d} ≤ n`, then its size is
at least `(2/5) · 2^ℓ`. With `ℓ = ⌊n^{1/(2d)} / 40⌋` this is
`size ≥ 2^{Ω(n^{1/(2d)})}`. -/
theorem parity_size_lower_bound {n G d ℓ : ℕ} [NeZero n]
    (C : Circuit (Basis.unboundedAndOrMod 3) n 1 G)
    (hcomputes : C.Computes (Schnorr.xorBool n)) (hdepth : C.depth ≤ d)
    (hn : (40 * ℓ) ^ (2 * d) ≤ n) :
    2 * 2 ^ ℓ ≤ 5 * C.size :=
  two_mul_two_pow_le_size_internal C hcomputes hdepth hn

end Smolensky

/-- **Parity is not in `AC0[3]`** (Razborov–Smolensky): no polynomial-size,
constant-depth family of unbounded-fan-in AND/OR/`MOD_3` circuits computes the
parity family. -/
theorem xorBool_not_mem_AC0Mod_three : Schnorr.xorBool ∉ AC0Mod 3 :=
  Smolensky.xorBool_not_mem_AC0Mod_three_internal

end Complexity

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Defs
public import Complexitylib.Circuits.Smolensky.Internal.Circuit
public import Complexitylib.Circuits.Smolensky.Internal.Parity
public import Complexitylib.Circuits.Smolensky.Internal.Binomial

/-!
# Smolensky's polynomial approximation

Smolensky's lower bound approximates circuits with `MOD_3` gates by low-degree
functions over `ZMod 3` (`Smolensky.lowDegree`, functions `{0,1}^n → ZMod 3` in
place of formal polynomials) and shows that parity has no such approximation:

1. `Smolensky.exists_lowDegree_approx`: with a fixed choice of `ℓ` subsets per
   OR or AND gate, a depth-`d` circuit agrees with a function of degree at most
   `(2ℓ)^d` on all but `size · 2^n / 2^ℓ` inputs. The random choices of the
   usual proof are replaced by exact double counting over all tuples of subsets.
2. `Smolensky.card_agree_xorBool_le`: a function of degree at most `D` agrees
   with parity on at most as many inputs as there are subsets of at most
   `n / 2 + D` coordinates.
3. `Smolensky.ten_mul_card_le`: when `100 (t + 1)² ≤ n + 1`, at most `6/10` of all
   subsets have at most `n / 2 + t` coordinates.

The circuits are the library's typed circuits over `Basis.unboundedAndOrMod 3`:
a `MOD_3` gate outputs `true` exactly when the number of its true inputs is not
divisible by `3`, negations are free per-input flags, the size `G + 1` counts the
internal gates and the output gate, and the depth counts the output gate.
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

end Smolensky

end Complexity

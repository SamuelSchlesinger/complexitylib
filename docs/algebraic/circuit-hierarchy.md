# Circuit size hierarchy

The library proves the nonuniform circuit size hierarchy over its native
shared De Morgan circuits. For any real exponents `1 <= a < b`,

```text
SIZE(n^a) is a strict subset of SIZE(n^b).
```

The classes allow multiplicative constants and finitely many exceptional
input widths. The separating function family is chosen nonuniformly; the
result supplies no uniform circuit-generation algorithm.

## Exact finite statement

Let `C(f)` be the minimum internal gate count for a scalar Boolean function
on `n` inputs. Truth tables form the cube `{0,1}^{2^n}`. Distance counts
the input assignments where two functions disagree, without normalization.

```text
abs(C(f) - C(g)) <= 2*n * hammingDist(f,g).
```

To set one truth-table entry to 1, append a minterm recognizing the selected
input and OR its output with the original output. To set it to 0, append the
dual clause and AND its output with the original output. For positive `n`,
the test uses at most `n` NOT gates and `n-1` binary gates. One final binary
gate completes the correction, and the original shared circuit appears once.

The generic Boolean-cube theorem walks between two functions by coordinate
updates. The first crossing of a threshold overshoots by at most the update
bound; the complexity need not increase monotonically along the path.
Consequently, whenever `1 <= s < C(h)` for some endpoint `h`,

```text
there exists f with s < C(f) <= s + 2*n.
```

The exact sharp Shannon census supplies a sufficient finite condition for
such an endpoint. The asymptotic Shannon theorem implies the stronger
simultaneous statement:

```text
for all sufficiently large n,
  for every s with 1 <= s <= floor(2^n/n),
    there exists f with s < C(f) <= s + 2*n.
```

## Cost convention and proof boundary

The measure counts every internal gate in the De Morgan signature, including
constant and identity gates, matching the existing Shannon counting API.
Designated output wires are free, so an input projection has complexity zero.
With zero inputs, every Boolean function has complexity exactly one. The
point-update bound covers this case too, with zero additional gates.

`DeMorgan.complexity_eq_gateComplexity` identifies the natural-valued measure
with the generic extended-natural minimum. Its finiteness follows from a
proved circuit construction. Class membership is also proved equivalent to
the existence of actual `Circuit.Family` witnesses; it is not a predicate on
an abstract surrogate for circuits.

The generic hierarchy criterion requires an upper budget below the Shannon
scale and, for every constant `K`, the eventual gap

```text
K * lower(n) + 2*n + 1 <= upper(n).
```

Distinct real powers with `1 <= a < b` satisfy this condition. Flooring the
real powers preserves the usual asymptotic size-class definition.

## API

Use `import Complexitylib.Algebraic.LowerBound.Hierarchy` for the complete development.
The three headline endpoints are also exported by `Algebraic.Applications`.

| Module | Principal result |
| --- | --- |
| `Algebraic.BooleanCube` | `BooleanCube.exists_between`, `BooleanCube.dist_le_mul_hammingDist` |
| `Algebraic.Basis.DeMorgan.PointUpdate` | `DeMorgan.exists_update_circuit` |
| `Algebraic.Basis.DeMorgan.Complexity` | `DeMorgan.complexity_dist_le`, `DeMorgan.exists_complexity_between` |
| `Algebraic.LowerBound.Hierarchy.Finite` | `DeMorgan.exists_complexity_between_of_sharpBudget`, `DeMorgan.eventually_exists_complexity_between` |
| `Algebraic.LowerBound.Hierarchy.Family` | `DeMorgan.mem_sizeClass_iff`, `DeMorgan.sizeClass_ssubset_of_gap` |
| `Algebraic.LowerBound.Hierarchy.Polynomial` | `DeMorgan.polynomialSize_ssubset`, `DeMorgan.sizeClass_pow_ssubset` |

This is a formalization of the classical circuit size hierarchy; see, for
example, [Theorem 6.1 of ECCC TR25-045](https://eccc.weizmann.ac.il/report/2025/045/download).

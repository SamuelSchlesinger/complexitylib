# Conditional circuit complexity

## One general notion, two input conventions

The underlying definition is **relative complexity**. For any common domain
`X`, carrier `U`, target family `F : X → Uᵐ`, and source family `S : X → Uᵏ`,

\[
R(F\mid S)=\min\{\operatorname{cost}(h):h(S(x))=F(x)\text{ for every }x\in X\}.
\]

Only the supplied values are circuit inputs. The domain need not have
coordinates, be finite, or equal the carrier. This is
`Circuit.relativeCostComplexity` in `Algebraic.Complexity.Relative`.
The definition uses extended natural numbers, with infinity for impossible
computations and an attained minimum whenever the value is finite.

Your conditional quantity is its specialization

\[
C(f\mid G)=R(f\mid (\mathrm{id},G)).
\]

This is a definition in the implementation, so both conventions share the
same foundation. In particular, the conditional triangle inequality is
derived from the relative triangle inequality by retaining the original
coordinates as free outputs.

### Adapting Boyack

Boyack is a source of mathematical results; the organization follows the
general circuit library and the questions about supplied information. The
adaptation makes these choices explicit:

- Allow arbitrary carriers, domains, finite gate arities, and natural costs.
- Distinguish supplied values from original input coordinates.
- Count constants according to actual gates or supplied wires. Boyack's
  disconnected-wire zero convention is not built into this circuit syntax.
- Express a partially specified computation using **total extensions**
  agreeing on the source image. Ordinary complexity always has a total
  function as its argument.
- Separate general semantic results from results requiring algebraic laws,
  Boolean completeness, specific bases, or algorithmic running-time claims.

The initial goal is a reusable theory of relative computation. A chapter-by-
chapter transcription would obscure these distinctions and is not the
organization used here.

## Conditional complexity

Fix a gate basis and interpretation. For `f : Uⁿ → Uᵐ` and a finite family
`G : Uⁿ → Uᵏ`, define

\[
C(f\mid G)=\min\{\operatorname{size}(h):
  h(x,G(x))=f(x)\text{ for every }x\}.
\]

The minimum ranges over circuits on `n+k` inputs. The original coordinates
and all `G(x)` values are free. Only the gates of `h` are charged. The same
definition works for natural-number operation weights. An impossible
computation has value `∞`; finite values are attained.

The values of `h(x,y)` for `y ≠ G(x)` are unrestricted. Thus this is also
the minimum ordinary complexity of an extension of the partial function
`(x,G(x)) ↦ f(x)`. It is not required to compute any of the supplied functions.

```lean
import Complexitylib.Algebraic.ConditionalComplexity

open Algebraic

-- f : ScalarFunction U n
-- g : Fin k → ScalarFunction U n
-- interpretation : Interpretation σ U
#check Circuit.conditionalGateComplexity
-- Circuit.conditionalGateComplexity interpretation
--   (fun x (_ : Fin 1) => f x) (fun x i => g i x)
```

## Relation to Synthesis

The pinned CSLib version defines Boolean `Synthesis sources targets budget`.
For **every program** making the source functions available, it promises
another program with at most `budget` more gates, preserving all available
functions and making the targets available too. That includes intermediate
functions of the starting program, beyond its designated source outputs.
The definition does not require a literal syntactic extension of that program.

Conditional complexity instead minimizes a circuit whose formal inputs are
exactly the original coordinates and supplied values. The checked theorem
`Cslib.Circuits.Boolean.synthesis_of_conditionalGateComplexity_le` converts a
conditional bound into `Synthesis`: instantiate the conditional circuit after
the starting program. We do not assert a converse or an equivalence between
the definitions.

## Basic laws checked in Lean

Write `C` for either gate complexity or a fixed nonnegative weighted cost.
The following hold for arbitrary interpretations, with extended-natural
values where necessary:

| Property | Statement | Reason |
| --- | --- | --- |
| Empty conditioning | `C(f ∣ ∅) = C(f)` | Only the original coordinates are supplied. |
| Supplied outputs | `C(G ∣ G) = 0` | Select the supplied wires. |
| Ignore supplied values | `C(f ∣ G) ≤ C(f)` | Use only the original coordinates. |
| Enlarge the family | `C(f ∣ G,H) ≤ C(f ∣ G)` | Ignore the extra coordinates. Reordering and duplication are also free. |
| Directed triangle | `C(f ∣ G) ≤ C(f ∣ H) + C(H ∣ G)` | Compute `H`, then `f`. |
| Bounded saving | `C(f) ≤ C(f ∣ G) + C(G)` | First compute the supplied values. |
| Joint upper bound | `C(f,G) ≤ C(f ∣ G) + C(G)` | Keep the supplied outputs when computing `f`. |
| Free conditioning | If `C(G)=0`, then `C(f ∣ G)=C(f)` | Combine ignoring the values with the bounded-saving inequality. |

For **unit gate cost**, there is an exact characterization of zero:
every output of `f` must be one fixed original coordinate or one fixed
supplied function. Selecting a different wire depending on the input can
require gates. This characterization does not apply to arbitrary weights
that assign zero cost to operations.

The triangle inequality also explains approximate invariance under changing
the supplied representation. If `C(H ∣ G) ≤ a` and `C(G ∣ H) ≤ b`, then

\[
C(f\mid G)\le C(f\mid H)+a,\qquad
C(f\mid H)\le C(f\mid G)+b.
\]

These are directed computational comparisons; symmetry is not expected.

### General properties of supplied information

The relative framework also proves:

- **Restriction of the common domain:** restricting both source and target
  to fewer points cannot increase complexity. A surjective reindexing
  preserves it exactly, including duplication or permutation of table columns.
- **Source and output reindexing:** permutations preserve complexity;
  selecting target outputs cannot increase it.
- **Equivalent free representations:** if each source family can be obtained
  from the other at zero cost, every target has the same complexity relative
  to either family. This accommodates duplicate source functions.
- **Information loss:** if `S(x)=S(y)` but `F(x)≠F(y)`, then `R(F ∣ S)=∞`.
  With a functionally complete interpretation and a nonempty output space,
  constancy of `F` on each such fiber is also sufficient for finite complexity.
- **Sections and inverses:** if `S` is surjective and `F` is constant on its
  fibers, then `R(F ∣ S)=C(F∘s)` for any right inverse `s` of `S`. In
  particular, an invertible source family gives `C(F∘S⁻¹)`.
- **Carrier embeddings:** an injective map preserving gate operations
  preserves relative complexity of the mapped families. Without injectivity,
  only the nonincrease direction is asserted.
- **Pointwise computation:** a circuit acting on whole functions `X → U`
  with pointwise operations has exactly the same cost as a circuit required
  to produce their values at every `x`. This is the general mechanism behind
  Boyack's correspondence between set complexity and relative complexity.
- **Basis translation:** compiling gates transports relative complexity with
  the exact cost of implementing each source operation in the target basis.

The information-loss obstruction applies to `R(F ∣ S)`. The source map
`x ↦ (x,G(x))` for conditional complexity is injective, so supplying `G`
cannot erase original information. Representability can still fail for an
incomplete gate basis.

### Proof of the triangle inequality

Take a circuit `a` computing `H(x)` from `(x,G(x))` and a circuit `b`
computing `f(x)` from `(x,H(x))`. Preserve the original coordinates while
running `a`, then connect `(x,a(x,G(x)))` to `b`. The resulting circuit
computes `f(x)` and has cost `cost(a)+cost(b)`: keeping the coordinates and
connecting wires adds no gates. Taking the infimum over both circuits proves

\[
C(f\mid G)\le C(f\mid H)+C(H\mid G).
\]

`Circuit.conditionalCostComplexity_triangle` formalizes this construction for
arbitrary natural-number gate weights. Its infimum proof also handles `∞`,
so it needs no representability or functional-completeness assumption.
`Circuit.conditionalGateComplexity_triangle` specializes to unit gate cost.

## An exact chain rule fails

Use AND, OR, NOT, and the two Boolean constants, charging one per gate and
zero for designated output wires. Set

\[
f(x,y)=x\land y,\qquad G(x,y)=\neg(x\land y).
\]

The checked equalities are

\[
C(f,G)=2,\qquad C(G)=2,\qquad C(f\mid G)=1.
\]

A joint circuit computes AND and then NOT. Its first gate already supplies
`f`, so exposing that intermediate wire as another output costs nothing.
Given only `G(x,y)`, one NOT gate recovers `f`. Zero gates cannot suffice:
`f` is none of the three supplied functions `x`, `y`, and `G`.

Consequently,

\[
2=C(f,G)<C(f\mid G)+C(G)=3.
\]

This identifies the obstruction: optimizing two stages separately can lose
sharing through intermediate functions. The gate basis matters; this specific
example would not work in a basis containing NAND as a primitive gate.

The proof in `Algebraic.ConditionalComplexity.Counterexample` includes the
lower bounds. Its finite one-gate check uses kernel-checked `decide`, not an
external search result or `native_decide`.

## Counting and random targets

Fix **any** supplied family `G : Uⁿ → Uᵏ`. It may itself be very expensive to
compute. A circuit description on `n+k` inputs determines at most one function
of `x` after substituting `G(x)`. Thus

\[
\#\{f:C(f\mid G)\le s\}\le B_\sigma(n+k,m,s),
\]

where the exact ordered-description budget used by the Lean theorem is

\[
B_\sigma(N,m,s)=
\sum_{t=0}^{s}(N+t)^m
\prod_{j=0}^{t-1}\left(\sum_{o\in\sigma}(N+j)^{\operatorname{arity}(o)}\right).
\]

This overcounts semantic functions, which is sufficient for a lower bound.
The relative version works on any domain and carrier: only the operation
signature must be finite. Counting all targets or invoking the library's
factorial-improved normalization bound imposes additional finiteness assumptions.

For finite carriers, `card_relativeFunctionsAtMost_le_sharpBudget` and its
conditional specialization also give the factorial-improved bound

\[
\#\{F:R(F\mid S)\le s\}\le
\sum_{t=0}^{s}\left\lfloor
\frac{L_\sigma(k+t)^t(k+t)^m}{t!}\right\rfloor,
\quad L_\sigma(w)=\sum_{o\in\sigma}w^{\operatorname{arity}(o)},
\]

when `S` has `k` outputs. This reuses the library's normalization and counting
of distinct gate labelings; restricting a total circuit function to the source
image can only reduce the number of resulting targets.
Neither displayed count is necessarily smaller at every finite budget; their
minimum is also a checked upper bound (`card_relativeFunctionsAtMost_le_min`).

For a uniformly random scalar Boolean function on `n` variables,

\[
\Pr[C(f\mid G)\le s]
\le \frac{B_\sigma(n+k,1,s)}{2^{2^n}}.
\]

The denominator counts functions on **the original `n` variables**. Supplied
values add input wires to the circuit description but do not enlarge the
random target space. The Lean result `conditional_easy_fraction_le` proves
the corresponding exact rational cardinality bound for any finite target
family; its probability interpretation requires that family to be nonempty.

For the five-operation Boolean basis above, the line count is
`2 + w + 2w²` at `w` available wires. For example, with `n=10`, `k=10`, and
`s=50`, direct integer evaluation of the displayed sum gives
`B(20,1,50) < 2^597`. Hence the probability is less than `2^-427`.
This numerical evaluation was checked with Python integer arithmetic; it is
not a separate Lean theorem.

The usual counting argument then shows that, for a fixed finite bounded-arity
basis and polynomially many supplied functions, random targets still require
`Ω(2ⁿ/n)` gates with high probability. This asymptotic consequence is derived
from the displayed bound; the new Lean module proves the finite counting and
fraction bounds, not a separate asymptotic theorem.

### Choosing from a menu

If `G` can be chosen from a fixed finite menu `M`, union-bound the easy sets:

\[
\#\{f:\exists G\in M,\ C(f\mid G)\le s\}
\le |M|B_\sigma(n+k,m,s).
\]

The checked theorem `exists_conditional_hard_for_all_given` gives a target
hard for every menu choice whenever this bound is smaller than the target
family. The menu can be fixed first and the choice made after seeing `f`.
Allowing unrestricted target-dependent conditioning would defeat the
conclusion: choosing `G=f` makes conditional complexity zero.

## Six lower-bound results checked in Lean

### 1. Necessary source values

For `S : X -> U^N` and `F : X -> U^m`, define `r(F;S)` as the smallest
number of source coordinates whose values determine `F`. If no subset does,
the value is infinity. Determination means that two samples agreeing on the
selected coordinates must have the same target value.

```text
fanin(op) <= b, b >= 2  ==>  r(F;S) <= m + (b-1)*R(F | S)
arity(op) <= 1+w(op)    ==>  r(F;S) <= m + R_w(F | S)
```

This is `sourceSupportSize`, bounded by
`Circuit.sourceSupportSize_le_relativeGateComplexity` and
`Circuit.sourceSupportSize_le_relativeCostComplexity`. The proof counts
the input frontier of a shared circuit. It uses neither Boolean semantics
nor finiteness of the common domain or carrier.

### 2. Exact complexity with linear Boolean helpers

Over `F_2`, let the nonzero target be `f(x)=a.x`, and let the helpers be the
rows of `Bx`. Suppose all operations have arity at most two, every gate costs
one, and XOR has a one-gate implementation. Then:

```text
C(a.x | Bx) = min_lambda [wt(lambda) + wt(a + sum_j lambda_j*B_j) - 1]
```

The formalization uses `ZMod 2`. Other operations in the basis may be
nonlinear. The theorem is `Linear.conditionalGateComplexity_eq_min_weight`.
Its more general relative version minimizes the weight of representations
using any supplied linear dictionary, returning infinity if none exists.

For the lower bound, determination by linear forms implies membership in
their linear span. A binary circuit with `s` gates touches at most `s+1`
sources. For the upper bound, sum a minimum representation with an XOR tree.
The nonzero-target assumption matters: the zero function need not be a free
wire in this model.

The regression suite checks three-bit parity in a basis containing addition,
multiplication, and constants: its complexity is two with no helpers, one
with `x_0+x_1` supplied, and zero with the entire parity supplied.

### 3. Relative Hessian rank

Let `f` and the `g_j` be **formal polynomials** over any field. Circuits use
addition, multiplication, and named field constants. Charge one per
multiplication and zero per addition or constant gate. At each point `a`:

```text
min_lambda rank(H_f(a) - sum_j lambda_j*H_gj(a)) <= 2*M(f | G)
```

`Hessian.residualRank_le_twice_with_helpers` proves this minimum-complexity
statement. `Hessian.exists_helper_hessian_residual` gives the circuit-level
version: for each circuit and each evaluation point, suitable coefficients
exist with residual rank at most twice its multiplication cost. These
coefficients may depend on the point.

The proof takes the quotient by the span of the supplied Hessians, applies
the library's interaction-span argument, and lifts back to matrices. One
multiplication contributes a symmetrized outer product of rank at most two.
Repeated uses of a gate are charged only once.

These are formal polynomial statements in every characteristic. Over a finite
field, equality of polynomial functions at field elements alone is a weaker
correctness requirement and is not the hypothesis of these theorems.

### 4. Pairing resists arbitrary one-sided preprocessing

For any field, any `n >= 0`, and any finite family of polynomials in the
`x` variables alone:

```text
M(sum_i x_i*y_i | g_0(x), ..., g_(k-1)(x)) = n
```

This is `Pairing.preprocessedMultiplicationComplexity_eq`. There is no
bound on the number, degrees, or computation costs of the helpers. Every
source-adjusted Hessian has block form `[[A,I],[I,0]]`, which is invertible
over every field. The lower bound is `n`; the usual sum of `n` products
attains it. Tests include characteristic two and a degree-seven helper.

### 5. Restrictions and parameterizations

For arbitrary interpretations, natural operation weights, and an arbitrary
map `rho` from new input tuples to old ones:

```text
C_w(f o rho) <= C_w(f | G) + C_w(y -> (rho(y), G(rho(y))))
```

Consequently, a restricted lower bound `L` and a joint source construction
of cost at most `a` give `L-a <= C_w(f | G)`, with subtraction truncated at
zero. These are `Circuit.costComplexity_precomp_le_conditional_add` and
`Circuit.conditionalCostComplexity_lowerBound_of_precomp`. The source tuple
is charged jointly, allowing shared work in its construction.

The general source-to-source inequality is
`Circuit.relativeCostComplexity_precomp_triangle`, available from
`Algebraic.Complexity.Relative`. The conditional statements specialize it.

### 6. Approximation relative to initialized sources

On a finite sample space, assume each supplied function has an exact
approximate representative. Suppose each approximate operation introduces
at most `e(op)` new disagreements, uniformly over its approximate arguments.
If every approximate value disagrees with the target on at least `L`
samples, then:

```text
L <= R_e(f | S)
```

`Approximation.Scheme.relativeCostComplexity_lowerBound_of_localErrors`
states this directly. A second endpoint accepts the library's more general
one-sided approximation relation. Both reuse its union-of-exceptions proof
for shared circuits, counting each gate once. The regression suite obtains
the one-gate lower bound for AND by approximating gates with projections.

These results adapt standard support, linear-algebra, Hessian, restriction,
and approximation arguments to supplied information. No novelty or priority
claim is made for them. Large asymptotic gaps between the joint and
two-stage costs remain a separate question.

## Sources and proof scope

Stephen Wayne Boyack's [1985 MIT thesis](https://hdl.handle.net/1721.1/15322),
Definition 2.1 and Proposition 2.2 (pp. 29–30),
defines circuit complexity relative to supplied functions and gives the
triangle inequality. His source family need not contain the original input
coordinates; the convention here includes them automatically, corresponding
to supplying `(id,G)`. His Boolean specialization uses all binary Boolean
operations; our counterexample uses the explicitly stated AND/OR/NOT basis.
This is a relevant prior source, not a claim of earliest priority.

The complete MIT repository scan has 212 pages. The copy previously hosted
under Rivest's student theses has 182 PDF pages and omits several printed
pages, including 32–47. Source references here use the complete scan's
printed page numbers.

| Source result | Adapted status |
| --- | --- |
| Definition 2.1; Proposition 2.2 | General relative definition and weighted triangle inequality, formalized. |
| Proposition 2.2.1; Corollaries 2.2.1.1–3 | Total-extension infimum, surjective-section equality, and invertible-source equality, formalized with domains explicit. |
| Lemma 2.2.2 | General ordered and factorial-improved counting bounds, formalized using the library's circuit syntax. The thesis's displayed constant is not asserted. |
| Proposition 7.1.4 | General pointwise semantic correspondence, formalized. Boolean rows can be viewed as characteristic functions. |
| Proposition 7.1.4.2 | Underlying source/output/domain reindexing invariances, formalized; no separate matrix-multiplication interface is introduced. |
| Theorem 7.1.5, complete-basis case | Semantic fiber criterion, formalized. The polynomial-time decision bound and the other listed bases are not formalized here. |
| Transposition, derivative, and gradient results | Require additional algebraic or Boolean structure. They remain separate developments; this work does not establish those results or the gradient conjecture. |

The finite counting argument specializes the library's existing exact circuit
syntax counts. No novelty claim is made for the elementary laws or counting
method. The new definitions, laws, counterexample, synthesis implication, and
finite counting theorems are Lean proofs. The numerical illustration and
asymptotic discussion have the separate status stated above.

| Import | Contents |
| --- | --- |
| `Algebraic.Complexity.Relative` | General relative definition, minima, zero case, composition, source information, extensions, domain restrictions, and reindexing |
| `Algebraic.Complexity.RelativeCounting` | Counting on arbitrary domains, sharp finite-carrier bounds, finite menus and fractions |
| `Algebraic.Complexity.RelativeTransport` | Homomorphisms, pointwise operations, and basis translation |
| `Algebraic.Complexity.RelativeSupport` | Necessary source counts and weighted or bounded-fan-in lower bounds |
| `Algebraic.Complexity.RelativeApproximation` | Relative lower bounds from local approximation errors |
| `Algebraic.ConditionalComplexity` | Definition, extension characterization, minima, zero case, monotonicity, triangle and chain bounds |
| `Algebraic.ConditionalComplexity.Boolean` | Conversion to CSLib Boolean `Synthesis` |
| `Algebraic.ConditionalComplexity.Counterexample` | Exact AND/NAND counterexample |
| `Algebraic.ConditionalComplexity.Counting` | Finite counting, rational fraction bound, and simultaneous hardness against a menu |
| `Algebraic.ConditionalComplexity.Restriction` | Lower bounds by restricting or parameterizing the original inputs |
| `Algebraic.ConditionalComplexity.Linear` | Exact minimum-weight formula for nonzero linear targets over `ZMod 2` |
| `Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Relative` | Source-adjusted Hessians and relative multiplication lower bounds |
| `Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.PairingRelative` | Exact pairing complexity with arbitrary one-sided polynomial preprocessing |

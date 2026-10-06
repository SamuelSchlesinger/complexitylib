# Communication and distribution-sensitive frontier capacity

Mirrored from the frontier-method research notes at `d81d97a`; Lean names are in the
namespace `Complexity.Frontier` (see the [frontier-method note](index.md)).
This investigation starts from the paper at commit `dea9d2ed9450`. It proves a
distribution-sensitive charging bound and conditional potential interface. It does
**not** prove a better universal circuit coefficient or an exact counting speedup.
The new mathematical statements are deductions from the existing pruning lemma;
the disjoint weighted peeling argument underlying that lemma is credited to Sam McGuire.

## The checked result

Let `P_0, P_1` be coherent, nested sweeps of the two output classes of a predictor
`g`, and let the target have rectangle bias at most `2b` at threshold `K`. Write
`N = 2^n`, `lambda = (K-1)^2/N`, and use **unconditional** transition masses

```
p[a,t,e] = Pr[g(X) = a and transition_a(t,X) = e].
```

Then

```
agreement(f,g) <= 1/2 + b + (1/2) sum_{a,t,e} min(lambda, p[a,t,e]).
```

Keep a transition when its mass is at least `lambda`. The existing pruning bound
charges `lambda` for each retained transition and bounds the lost mass by the sum
of the deleted transition masses. This gives the displayed minimum separately at
every transition. It is optimal for this *separable union-bound estimate*; it need
not optimize the actual union of discarded inputs across all layers.

Lean checks the stronger version for arbitrary signed weights, asymmetric rectangle
thresholds, and an atom bound:

- `Complexity.Frontier.Sweep.abs_sumOn_le_capped`
- `Complexity.Frontier.agreement_le_capped_sweeps`

The construction retains entire transitions of the original sweep, so it preserves
the required splicing structure. It does not merge states solely because they have
similar distributions or small mutual information.

## A usable moment criterion

For equal-length sweeps let `Z_t = (g(X), transition_{g(X)}(t,X))`. Its distribution
is normalized across both output classes. Since

```
min(lambda, p) <= sqrt(lambda) sqrt(p),
H_(1/2)(Z) = 2 log_2 sum_z sqrt(Pr[Z=z]),
```

the new inequality implies

```
agreement(f,g) <= 1/2 + b
  + (K-1)/2 * sum_t 2^(-(n - H_(1/2)(Z_t))/2).
```

Thus polynomially many transitions, `log K = o(n)`, and
`H_(1/2)(Z_t) <= (1-gamma)n` at every layer give an exponentially small remainder.
The underlying square-root moment and unnormalized agreement bounds are checked as
`Sweep.cappedCapacity_le_root` and `agreement_le_root_sweeps`. The displayed entropy
notation is the logarithmic restatement, not a separate Lean entropy API.

More generally, a paper proof works for every fixed `0 < theta < 1`:

```
min(lambda, p) <= lambda^(1-theta) p^theta,
error <= (1/2) lambda^(1-theta) sum_t 2^((1-theta) H_theta(Z_t)).
```

The unnormalized fractional-moment inequality is now checked as
`Sweep.cappedCapacity_le_moment` and `agreement_le_moment_sweeps`; the entropy
formula above is its logarithmic restatement. Taking theta close to one can give
better coefficients for biased independent sources and for restriction-tree
accounting, at the expense of the exponential remainder's rate. The
[restriction continuation](restrictions.md) derives that accounting and tests
concrete structural reductions, without claiming a universal improvement.
The [additive continuation](additive.md) supplies a different exact-demand interface:
sumset hardness permits overlapping vector labels. A coded affine prefix can then be
checked by one syndrome, with a layout-dependent rank cost. Its remaining target is a
common ordering that makes the suffix boundary and syndrome cheap simultaneously.
The [joint-code refinement](joint.md) also removes overlap between visible interface
signals and the syndrome itself; it gives a smaller target for that common ordering.

## Where amortization enters

Encode one whole transition sequentially. At each prefix `v`, let `p(v)` be its
actual mass. A nonnegative potential `V` with leaf values at least one and

```
sum_{u child of v} sqrt(p(u)) V(u) <= sqrt(p(v)) V(v)
```

certifies that the square-root moment is at most `V(root)`. Sum the inequalities
level by level: every child has exactly one parent, so all intermediate terms
telescope. This is checked as `Communication.rootPotential_le`.

For a positive-mass prefix with conditional next-bit probability `q_v`, set

```
c(v) = sqrt(q_v) + sqrt(1-q_v),
V(v) = c(v) max_supported_child V(child),
V(leaf) = 1.
```

The certificate holds, and `V(root)` is the maximum product of the local factors
along a supported encoding path. This is genuinely conditional: no independence
between boundary signals is assumed. Different histories can earn savings at
different positions, provided the total path budget is controlled.

A deterministic bit has factor 1, a fair bit has factor sqrt(2), and a bit with
conditional probability 1/4 or 3/4 has factor `(1+sqrt(3))/2`. If every path has at
most `h` unrestricted bits and at most `d` such biased bits, with all remaining bits
deterministic, its entropy budget is at most

```
h + 2d log_2((1+sqrt(3))/2) = h + 0.8999686... d.
```

The output-class bit can be appended last at a cost of at most one entropy bit:
`sqrt(p_0)+sqrt(p_1) <= sqrt(2(p_0+p_1))`. Thus the conditional signal analysis can
use the original uniform input distribution rather than wrongly assuming that
independence persists after conditioning on the circuit output.

This amortizes the encoding of **one transition**. It does not yet charge circuit
gates across successive graph cuts. A certificate based on gate structure is the
missing supply result.

The finite checker independently verifies an equivalent identity: normalize each
conditional square-root vector to obtain an escort distribution `Q` on codewords.
Then `sum_z sqrt(p(z)) = E_Q[product of local factors along z]`. In particular this
expectation is at most the largest path product.

## An obstruction to the Shannon-entropy shortcut

Take independent fair bits `z,x_1,...,x_k` and the `k` gates `y_i = z AND x_i`.
Every output has marginal probability 1/4 of being one, yet

```
Pr[Y=0^k] = 1/2 + 2^(-k-1),
Pr[Y=y]   = 2^(-k-1) for y != 0^k.
```

Any codebook of `M` output patterns has mass at most `1/2 + M/2^(k+1)`.
Consequently, covering probability `1-delta` with `delta < 1/2` requires
`M >= (1-2delta)2^k`. Inverse-polynomial error gives essentially no reduction in
the logarithm of support size, even though Shannon entropy is `k/2+1-o(1)`.

Here `H_(1/2)(Y) = k-1+o(1)`, whereas adding marginal Renyi entropies would give
only `0.8999686... k`. That proposed subadditivity bound is false. The conditional
potential diagnoses the problem: once an output one has appeared, the shared
selector is known to be one and the remaining outputs are fair.

This is a realizable boundary distribution, not an impossibility theorem for all
layouts or semantic recompilations. For example, if the final readout is the XOR
of these outputs, the whole function simplifies to `z AND XOR_i x_i`. Branching
on the shared selector also removes all the masking gates. A promising global
argument would need to account for such simplifications when conditional
compression gives no saving; neither alternative is presently guaranteed for
arbitrary circuits.

## The exact theorem still needed

For every small fan-in-two circuit, find compatible sweeps with polynomially many
layers for which, when `m = n-o(n)` inputs are reachable,

```
max_t H_(1/2)(Z_t) <= B(s-m) + o(n), with B < 0.2807019373...
```

The moment bound would then prove average-case hardness below
`(1+1/B-epsilon)n`, with the same extractor error and an exponentially small
remainder. Circuits with many unused inputs are handled by the existing direct
rectangle argument. `B=1/4` would yield the illustrative threshold `5n`; it is
not established or supported as a universal conjecture by the finite experiment.

Current transition codes reconstruct the original whole transition. Semantic
messages that retain only continuation behavior require a new coherent compiler.
Similarly, an information-theoretic codebook need not be efficiently enumerable or
support exact counting. No #SAT improvement follows from the new bound alone.

## Reproducible finite experiments

Run [check_communication.py](data/check_communication.py):

- 512 exact tests of compiled circuit traces, capped pruning, and moment domination;
  354 improve the raw unpruned budget. Layouts are unoptimized, circuits may be
  redundant, and these counts provide no evidence for a universal coefficient.
- 1,280 exhaustive comparisons with every codebook in a four-label space, verifying
  the optimal separable keep/drop choice independently of the threshold formula.
- 80 dependent distributions verifying the escort identity and path-potential bound.
- A shared-selector example with `k=12`: Shannon entropy 6.9984 bits, Renyi order
  1/2 entropy 11.0440 bits, and 4,015 of 4,096 patterns needed for 99% mass.
  Independent AND outputs instead have Renyi order 1/2 entropy 10.7996 bits.

## Sources and status

- The paper's existing pruning and weighted frontier results supply the demand
  argument; the new cap optimization and conditional certificates are derived here.
- Renner and Wolf's smooth Renyi entropy [renner-wolf04][renner-wolf04] supplies the
  source-coding context. We use the explicit finite inequalities above, not an unquoted
  coding theorem or an independence assumption.
- Braverman and Rao [braverman-rao11][braverman-rao11] concern amortization across
  independent copies of communication problems. That theorem does not supply the circuit
  prefix-potential bound required here.

The capped and fractional-moment bounds and finite conditional telescoping are checked
in Lean. The entropy restatements, shared-selector calculation, and special
conditional-probability examples are paper proofs with finite checks. A stronger
unrestricted circuit lower bound remains open in this investigation.

[braverman-rao11]: ../sources.md#braverman-rao11
[renner-wolf04]: ../sources.md#renner-wolf04

# Why the proposed derandomization would give RL = L = BPL = coRL

The proof's task is to replace a long random computation by a short description
of an estimate of its acceptance probability. There are only polynomially many
such descriptions. If most estimates are accurate and **every** estimate can be
evaluated in deterministic logspace, a majority vote removes the randomness.

This is a reduced exposition of OpenAI's proposed proof, pinned to revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` [oai26][oai26]. The supporting notes
expose the estimator and its implementation; they are essential parts of the
argument. The proof status and limits of this reconstruction are stated below.

## The one construction the class equalities need

Fix a randomized machine with polynomial worst-case time, logarithmic work
space, and independent fair coin tosses. Input is read-only and endmarked;
physical input heads stay within the endmarkers. Every simultaneously live
writable cell counts toward space. Let `p_M(x)` be its acceptance probability.
Write `B = Θ(log(n+2))` for an input of length `n`, with a fixed minimum padding.

The construction must supply a nonempty set `E_x` of valid `O(B)`-bit
**environment encodings** and a deterministic evaluator `v(x,σ)` such that:

- Validity is decidable in `O(B)` space, and each encoding is counted once.
- For every valid `σ`, evaluation halts in `O(B)` total space and returns a
  constant-precision dyadic number.
- More than three quarters of the valid encodings satisfy
  `|v(x,σ) - p_M(x)| < 1/8`.

An environment describes the estimator's sampling and hashing choices. It is
not a short random tape on which the original machine is simply simulated.

The final algorithm enumerates every valid encoding, evaluates it, and keeps a
signed vote count. Its thresholds are:

| Machine | No-instance probability | Yes-instance probability | Vote yes when |
| --- | --- | --- | --- |
| BPL | at most `1/3` | at least `2/3` | `v > 1/2` |
| RL | `0` | at least `1/2` | `v > 1/4` |

Every accurate estimate votes correctly, so the strict majority is correct.
There are `2^O(B)` encodings; the counter and current encoding occupy `O(B)`
bits. Evaluation is total even on inaccurate environments. A halting
`O(B)`-space deterministic evaluation on a fixed input has `2^O(B)` complete
configurations, hence polynomial running time. Enumeration preserves that bound.

Thus the construction gives both `BPL ⊆ L` and `RL ⊆ L` directly. A halting
deterministic logspace decider runs in polynomial time and can ignore its coins,
so `L ⊆ RL` and `L ⊆ BPL`. Finally, `L` is closed under complement: interchange
its two halting verdicts. Since `coRL = {A : Aᶜ ∈ RL}`, `RL = L` also gives
`coRL = L`. This proves all four equalities from the one construction, without
an amplification machine or median search.

## 1. Make the exact answer shallow

Put the original machine's configurations into time layers. Its transition
matrix `C_0` is nonnegative, has row sums at most one, and moves strictly
forward in time. Let `h_0` be the vector of acceptance probabilities and `W_0`
the indicator of accepting configurations in the final layer. Then

```
h_0 = W_0 + C_0 h_0,     0 ≤ h_0 ≤ 1.
```

Keep this same form throughout the construction. A correction `E ≥ 0` changes
`C` to `D = C - E + EC` and changes `W` to `W + EW`. Substitution preserves
`h = W + C h`. A weighted copying of vertices then transports the invariant to
the next stage; the primary copy preserves its parent's `h` value.

The substantive matrix result is that one can perform this operation so that
entries shrink by a factor `16`, while the number of vertices incident to a
positive entry grows by at most `2`. After `l` stages, at the primary copy `z_l`
of the start,

```
0 ≤ p_M(x) - W_l(z_l) ≤ |V_0| · 8^(-l).
```

Since `|V_0| = 2^O(B)`, `L = O(B)` stages make this error at most `1/32`.
The matrices and vectors are mathematical targets; none is stored in full.
The [target note](target/index.md) explains the fixed-length correction,
overloaded-column detector, copy count, and the affine-line sampler that make
this reduction possible.

## 2. Estimate that target with a short environment

The estimator replaces dense rows by sparse random tables with the correct
conditional means. It estimates successive **differences** between child
budgets, compresses their sums, and uses short fingerprints to compare
endpoints without retaining full addresses. Adaptive candidates are handled by
a comparison calculation that ignores the current block's fingerprint salt.

The [accuracy note](estimator/index.md) explains the coupled induction. Its
output is the manuscript's eighth-moment bound for the actual reward estimator:

```
(1/N) E_σ Σ_v [X_f(v)/f] |Wbar_L(v) - W_L(v)|^8 ≤ C^8 · 2^(-8p).
```

Here `N = 2^O(B)` bounds the stage size, `f = 16^(-L)`, `X_f(v)` records
retention, and `p` is the statistical accuracy exponent. The constant `C ≥ 1`
is independent of the input. The environment has `O(B)` bits.

For our specified start `z`, retention has probability `π_f ≥ f`. Keeping its
one nonnegative summand and conditioning gives

```
Pr(|Wbar_L(z) - W_L(z)| > 1/32 | X_f(z)=1)
    ≤ N C^8 · 2^(-8p) · 32^8.
```

Choose `p ≥ 5 + log₂ C + (log₂ N + 3)/8`. The failure probability is at most
`1/8`. This still requires `p = O(B)`: constant final accuracy does not remove
the factor `N` lost when selecting a specified start from an averaged bound.
The budget needed to attain this precision is also `O(B)`.

## 3. Evaluate every environment within the space bound

The [implementation note](implementation/index.md) explains the harder resource
claim. The evaluator maintains one movable vertex address. Short inverse ports
restore earlier positions; program-tree traversals recover incoming accesses;
a shared, fully charged `B`-bit vector supports comparisons. Numerical
operations request individual redundant digits, retaining longer words only
when a sufficient decrease in the requested digit place pays for them.

A call carries a decreasing allowance `w` and a digit place `t`. Its concrete
record certificate bounds the bits retained over a child `(w',j)` by

```
ℓ ≤ A(w-w') + D(t-j) = Φ(w,t) - Φ(w',j),
Φ(w,t) = Aw + Dt.
```

The bound includes local copies used during inverse traversal. Summing over the
active stack telescopes. The bottom record has size at most its own potential,
so all stack records together occupy at most the top potential, `O(B)`.
Since `ℓ ≥ 0`, potentials do not increase down the stack; positivity of `D`
also bounds every descendant digit place. Environment, cursor, catalyst, and
scratch are counted once outside the stack.

This argument depends on the **concrete** certificates: a small record for an
isolated call would not suffice. Strictly decreasing allowances and finite
traversals give termination on every environment, independently of accuracy.
The evaluator computes the same fixed estimator as the moment theorem;
requesting another digit never changes its lists, ports, or structural tests.

## Assemble the three errors

Choose the hierarchy error and the statistical error threshold to be `1/32`
each. The evaluator's digits lie in `{-6,…,6}`. Truncating through fractional
place `8` leaves a tail of at most `6·2^(-8) < 1/32`; clipping to `[0,1]` cannot
increase distance from the exact reward. Hence at least seven eighths of the
valid environments give total error below `3/32 < 1/8`.

For enumeration, retain precisely the canonical field encodings satisfying
nonzero-slope conditions and the start-retention test, together with all raw
salt bit strings. This domain is nonempty. Different salt strings that induce
the same fingerprint remain separate encodings: their multiplicity is part of
the probability law. This supplies exactly the family used in the vote above.

## What was reduced, and what still carries the proof

The four class equalities need a constant-gap decision, so median search,
variable-precision output, accepting-path extraction, and the effective
compiler can be omitted. Specializing the sampler to `H=4, h₀=2` removes the
general frame notation. The vector invariant replaces cumulative matrix
products. One final space potential suffices once local overshoot and record
bounds are established. These reductions are justified in the linked notes.

The central work remains the uniform conditional sampler, the adaptive
estimation/compression argument, and the total evaluator with its physical
space bound. None is implied just by the correction identity or by a generic
recomputation trick. A [reduction ledger](reductions.md) records the scope of
each simplification and the dependencies that survive.

## Known Limitations

This is an exposition and mathematical reconstruction of a proposed proof,
not a Lean verification of `RL = L`. The finite-action spectral-gap theorem is
an external mathematical input. The detailed estimator inequalities and
concrete recipe certificates remain attributed to the manuscript, with their
mechanisms and dependencies exposed in the supporting notes. Review status and
any unresolved findings will be recorded here when the draft has converged.

## Supplementary Code

Run `python3 research/rl-derandomization/data/audit.py` from the repository root.
The [audit](data/audit.py) checks document reachability, citations, and source
manifest consistency, then runs the [finite sampler checks](target/data/validate_sampler.py).
Those checks exhaust the affine-line identities and representative wrap
variants over the two smallest prime fields. Optional `--source-dir` and
`--pdf` arguments verify downloaded source bytes against the
[pinned manifest](data/source-manifest.json). These are reproducibility checks;
they do not establish the uniform spectral gap or the class equality.

## Sources

The [bibliography](sources.md) identifies the pinned manuscript and the
external sources used in the supporting notes. No source theorem is credited
to this exposition.

[oai26]: sources.md#oai26

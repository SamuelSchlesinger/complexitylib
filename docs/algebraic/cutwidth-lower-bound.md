# The `(4 - ε) n` cutwidth lower bound

`Algebraic.LowerBound.Cutwidth` proves a circuit lower bound over the full
binary basis `B₂`: every gate computes any of the sixteen functions of two
bits, both slots may carry the same signal, fan-out is unrestricted, and the
size is the number of gates. The basis is `Algebraic.Binary` in
`Algebraic.Basis.Binary`.

The circuit proof follows Ryan Williams's private working note
*A (4 − ε)n lower bound for Boolean circuits* (September 2026), using the
circuit-to-read-once compiler from Samuel Schlesinger's counting note.
The graph and extractor sources, and the alternative connected-cluster
argument developed in this formalization, are identified below.

## Statement

The general theorem is `Algebraic.Cutwidth.eventually_lt_size_of_rectangleFree`
in `Algebraic.LowerBound.Cutwidth.FourN`:

```lean
theorem eventually_lt_size_of_rectangleFree
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat)
    (hK : (fun n => Real.logb 2 (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hacc : ∀ᶠ n in atTop, 2 ^ (n - 2) ≤ (accepting (f n)).card)
    (hrect : ∀ᶠ n in atTop, RectangleFree (f n) (K n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size
```

The family and threshold are fixed before `ε`. Only `log₂ K(n) = o(n)`
is required; polynomial thresholds are a special case. The older entry
points with explicit bisection, pathwidth, or ordering bounds remain available.
The library proves those graph bounds and adds no axioms.

## The remaining family hypothesis

A *one-rectangle* of `f` is a product `P × Q`, for a split of the coordinates
into `U` and its complement, on which `f` is identically `1`. The function is
`K`-rectangle-free when every one-rectangle under every split has a side with
fewer than `K` elements. The theorem assumes such a family with
`log₂ K(n) = o(n)` and at least `2 ^ (n - 2)` accepting inputs.
This is a checked theorem about every qualifying family; a particular
polynomial-time family has yet to be constructed in Lean.

`Cutwidth.Extractor` proves the bridge from flat-source sumset extraction.
`FlatSumsetExtractor` counts independent source pairs with multiplicity,
including pairs with equal sums. Error at most `1/4` gives both family
properties directly. `Extractor.Padding` allows any fixed error strictly
below `1/2`: `balancePad f` adds a fresh XOR bit, is exactly balanced, and
has rectangle threshold `2 K`. Its list evaluator preserves membership in
Complexitylib's `FP`.
`eventually_lt_size_balancePad_of_flatSumsetExtractor` and its
nondeterministic counterpart check the full asymptotic bridge: the padded
family needs more than `(4 - ε) (n + 1)` gates at its full input length,
assuming an eventually positive threshold with `log₂ K(n) = o(n)`.

The explicit construction remains substantial.
[Xin Li, Theorem 7.13 (2023)](https://arxiv.org/abs/2303.06802v2) gives a
polynomial support threshold. The weaker requirement here also admits the
polylogarithmic source entropy of
[Chattopadhyay and Liao (2021)](https://arxiv.org/abs/2110.12652).
For the latter route, the strong linear primitive described below now has
logarithmic seed length and arbitrary fixed polylogarithmic output. The
ordinary short-seed extractor `Γ` now also has its separate linear-output
parameters: for all sufficiently large `b`, it extracts `b` bits from `8b`
input bits with entropy at least `2b`, error at most `1/4`, and a seed of
at most `2^27*(clog 2 (b+1))^3` bits. The finite independence-merging
lemma is proved with the exact retained variables and an average leakage
budget, as described below. The affine correlation breaker,
including its internal extractor requirements, and the fixed source-reduction
map with its parity estimates still need construction and proof, together
with their uniform polynomial-time composition in Complexitylib's machine model.
The final analytic implication is proved in `Extractor.SourceReduction`.
For every qualifying pair of flat sources `P, Q`, suppose at least half
of the fixings in `Q` leave `m > 0` good output coordinates whose nonempty
parities of orders at most four have absolute sign expectation at most `δ`.
If `100 m² δ ≤ 1` and at most `sqrt m / 8` coordinates are bad, the
majority output is a sumset extractor with error `35/72 < 1/2`.
The good coordinates may depend on the source pair and fixing; the reduction
itself must be a single fixed function of the XOR input. Raw moment bounds,
normalization, the quartic tail certificate, majority robustness, and
averaging over fixings are all checked. The majority evaluator belongs to
`FP`. Supplying the hypothesized parity bounds remains the construction task.

`Extractor.Sampler` also proves the finite extractor-to-sampler conversion
used in that construction, for arbitrary source probability weights.
Extraction from supports of size at least `K` gives sampling for sources
with point masses at most `1/L`, provided `K ≤ δL`. This is the entropy
direction used in the proof of Chattopadhyay--Liao Lemma 3.18; their printed
Lemma 3.15 reverses it. The module proves the conversion without assuming
that a short-seed extractor has already been constructed.

`Sampler.Amplification` proves the next finite step: a neighbor map that
reaches a sufficiently large fraction of base seeds turns the sampler into
a somewhere sampler with the same source threshold and failure probability.
Seeded extraction itself supplies that neighbor-coverage guarantee.
`SourceReduction.BadSeeds` and `SourceReduction.Selection` count all low-order
parity tests, combine their excluded seeds, and select the good fixings and
coordinates. The individual parity estimates from the correlation breaker
are still explicit hypotheses; a failure bound of `1/2` is used directly
on good fixings, before any approximation by a different source distribution.

`Condenser.Polynomial` defines the modular-squaring map underlying the
Guruswami--Umans--Vadhan condenser, with the characteristic-power exponent
used by Cheraghchi to obtain linearity. Its coordinate formula, state-degree
bound, and linearity over `ZMod 2` are checked. `Condenser.Expansion` proves
the finite expansion bound for a supplied monic irreducible modulus of
degree at least two. Every source set `P` of distinct polynomials below that
degree, with `|P| ≤ h^m`, has at least
`(q - (deg E - 1)(h - 1)m)|P|` distinct neighbors, retaining the seed in
each neighbor. The proof uses exactly `|P|` interpolation monomials, removes
common modulus factors, and counts roots in the quotient field.
`Condenser.Lossless.Polynomial` converts that bound to a distributional
guarantee for every qualifying flat source: the seeded output is within
`(deg E - 1)(2^r - 1)m/q` of an ideal output that, conditional on each seed,
is uniform on exactly `|P|` values. The comparison uses every test on the
joint seed-output space, and the condenser map stays fixed as `P` varies.
`Lossless.Mixture` proves exact averaging over all `K`-subsets and preservation
of test discrepancy under normalized nonnegative mixtures.
`polynomialCondenser_flat_mixture` therefore covers every flat support of
size at least `K`, provided `K ≤ (2^r)^m`: its ideal output is an explicit
mixture of seedwise `K`-flat distributions. The source support itself may
exceed the output alphabet size. The later `Strong.FlatMixture` and
`Strong.Weighted.Condenser` layers supply the decomposition and transfer
for arbitrary capped probability weights.

`Modulus.Binomial` supplies the family `X^(3^s) - a`, monic and irreducible
whenever `a` is a noncube, by Mathlib's odd-prime-power Kummer theorem.
Rounding the degree to a power of three costs less than a factor of three.
Noncube existence is also proved when `3` divides `q - 1`.
`Binomial.Extension` proves that the quotient root has norm `a`, so it is
again a noncube and can supply the next binomial modulus's coefficient.
`Modulus.Binary` constructs the explicit irreducible family
`M_s = X^(2*3^s) + X^(3^s) + 1` over `ZMod 2`. Its quotient has cardinality
`2^(2*3^s)` and its named root is a noncube, so the next extension coefficient
requires no search. `Binary.Codec` gives an equivalence between that quotient
and coefficient lists of length exactly `2*3^s`, including high zero bits.
Both round trips and the decoding laws for addition, multiplication,
remainder, and modular squaring are checked. This is a semantic codec;
the runtime programs operate directly on bit lists. `Binary.Extension` uses
Mathlib's quotient-composition equivalence to identify the binomial tower
with the quotient by `M_(s+v)`, including the exact root and coefficient laws.
`Parameters.Sparse` checks that restricting field bit lengths to twice a
power of three can preserve rate `1 + 1/u`: choose the field size first,
then the powering exponent. The finite output-length and normalized-error
inequalities are proved, including the ceiling-division slack.

The encoded arithmetic layer supplies addition, carryless multiplication,
runtime-modulus remainder, bounded modular squaring, and blockwise Horner
evaluation. Each operation has an exact polynomial interpretation and a
uniform `FP` evaluator registered for `polytime`. The loops keep every state
at the modulus degree in bits. Missing coefficient bits are zero; widths and
iteration counts are unary word lengths. Zero moduli have explicit total
behavior: remainder returns the dividend, while squaring and Horner return
the empty list.

The trinomial generator rounds a requested unary half-degree up to a power
of three. `Binary.Encoding.encodedBinaryFrobenius` composes this generator
with bounded modular squaring; its exact semantics, output width, and
uniform `FP` membership are proved. The new `UnaryFn.pow_clog` closure rule
lets `polytime` handle rounding, including runtime bases and the zero cases.

`Condenser.Encoding` now supplies the complete uniform `FP` program. It
transposes source coefficient bits into the larger binary quotient, performs
bounded modular squaring, transposes back, evaluates by Horner, and concatenates
the requested coordinates. `Encoding.Correctness` identifies the decoded output
vector exactly with `polynomialCondenser` over the explicit field and binomial
extension. Source packing is injective for every fixed length within the
coefficient rectangle, including partial final blocks. The source and seed
may be padded; the runtime program is total even for malformed inputs.
The field interpretation requires the intended power-of-three dimensions.
`Encoding.Correctness.Linear` proves source additivity for every field seed,
including unequal padded source lengths. `Encoding.Lossless` transfers the
retained-seed lossless and mixture bounds to these actual output coordinates;
the concrete field's cardinality and irreducibility are proved internally.

`Parameters.Explicit` selects every numerical parameter from source length
`n`, entropy budget `k`, inverse-error exponent `e`, and positive rate parameter
`u`. Set `T=e+clog₂(9(n+1)(k+1))+1`, choose the sparse field width `b` and
stride `r=b-T`, then round the extension degree `d` up to a power of three
above both `3` and `ceil(n/b)`. With `m=ceil(k/r)`, the checked inequalities are
`n≤bd`, `d≤9(n+1)`, `k≤rm`, `b≤6(u+1)T`, `u·mb≤(u+1)k+ub`, and
`dk·2^e≤2^T`. These are explicit finite bounds, including the empty source
and zero entropy cases. The rounding choices adapt the sparse-grid argument
above; they are deductions in this formalization.

`Encoding.Explicit` supplies a single paired-input `FP` evaluator that computes
those parameters and runs the condenser. Its output has exactly `mb` bits;
the decoded output is linear in the source and is within `2^-e` of the
corresponding seedwise flat witness for supports of size at most `2^k`. For larger flat
supports it is within `2^-e` of an explicit mixture of seedwise `2^k`-flat
witnesses. All tests retain the seed, and the map is independent of the source
support. The runtime parameters use unary words; both rounded powers have
checked polynomial bounds, so no exponential-size field table is constructed.

`Extractor.Strong` defines extraction by tests on the retained seed and output.
For every nonempty flat support `P` with `K ≤ |P|`, each test differs from
independent uniform seed/output by at most the specified error. Product tests
give the existing weak `FlatSeededExtractor` contract in `Sampler`. No empty
support is treated as a probability distribution, even when `K=0`.

`Hashing` proves the finite leftover-hash lemma from collision universality:
if distinct inputs collide on at most a `1/M` fraction of seeds, every joint
test on a flat support of size `N>0` has squared discrepancy at most `M/(4N)`.
Thus `ε≥0` and `M ≤ 4 ε² K` give strong extraction at threshold `K>0`. Full pairwise
independence is unnecessary. `Hashing.Field` realizes universality by field
multiplication followed by a surjective additive projection; the collision
fraction is exactly `1/M`. These are the standard multiplication/truncation
and composition mechanisms in
[Guruswami--Umans--Vadhan, Lemma 5.1, Proposition 4.5, and Remark 5.15](https://people.seas.harvard.edu/~salil/research/PVcondenser-jacm.pdf).

`Hashing.Binary` instantiates the projection with the first `ell` coefficients
of the explicit binary field. Its runtime program multiplies, reduces modulo
the generated trinomial, and takes the requested prefix. It has a uniform
`FP` evaluator; within field capacity its output has exactly the requested
width and its decoded map is additive in the source. Fixed input length is
required for decoding to be injective. `Encoding.Serialization` identifies
coordinate vectors with bitstrings of their exact total width, including
zero padding, and proves that re-encoding the decoded condenser recovers its
actual runtime output.

`Strong.Composition` then applies the hash to the condenser's supplied flat
mixture. Each ideal support may depend on the condenser seed and mixture
component; the component weights are nonnegative and normalized. A fresh
independent hash seed adds the two test errors. Both seeds remain in every
final test, and the actual condenser is not assumed injective.

`Strong.OneShot` supplies this composed program with a fully selected schedule.
For source length `n`, requested output `ell`, and inverse-error exponent `e`,
set `k=ell+2e`; use condenser rate `u=1` and error exponent `e+1`. Let its
field width be `b` and output width be `N`, then choose a hashing field of
width `B` covering `max(N,ell)`. The checked finite bounds include

```text
N ≤ 2(ell+2e) + b,
B ≤ 6(N+ell+1),
b+B ≤ 7b + 12(ell+2e) + 6ell + 6.
```

The exact leftover-hash budget and addition of the two half-errors yield
`decodedOneShotExtractor_flat`: every flat support of `n`-bit words with
at least `2^(ell+2e)` elements gives an `ell`-bit output within `2^-e` of
uniform, against all tests retaining both independent field seeds. The
statistical map is the decoded actual bit program. Its output length is
exactly `ell`, its fixed-seed map preserves source XOR even outside the
fixed-length promise, and its total paired-input evaluator belongs to `FP`.
All parameters and actual field half-degrees have registered unary
polynomial-time certificates. This is a finite implementation of the
condense-then-hash step in
[Chattopadhyay--Goodman--Liao, Lemma 4.9](https://eccc.weizmann.ac.il/report/2021/075/download/),
using the explicit sparse field schedule developed here.

`Strong.FlatMixture` extends this result beyond flat sources. For `K>0`,
every finite nonnegative probability weighting `p` with `K*p(x)≤1` is an
exact convex mixture of uniform `K`-element supports. The proof completes
`p` to a doubly stochastic matrix and uses Mathlib's Birkhoff--von Neumann
theorem, formalized by Bhavik Mehta in `Mathlib.Analysis.Convex.Birkhoff`.
`Strong.Weighted` then proves that the flat and weighted strong-extractor
contracts are equivalent at positive thresholds, with no added error.
In particular, `decodedOneShotExtractor_ofFn_weighted` gives the same
actual program's guarantee for every distribution on `Fin n → Bool`
whose point masses are at most `2^(-(ell+2e))`.

`Strong.Weighted.Condenser` expresses the condenser witness as a normalized
distribution at each retained seed. Exact-size flat injection witnesses
extend to all capped weights. Thus `decodedExplicitCondenser_weighted_ofFn`
preserves the input cap `2^-k` in its ideal conditional output for every
positive rate parameter `u`, with joint statistical distance at most `2^-e`.
Strong extraction is the special case
where the ideal output is uniform on its whole type. The ideal weights are
existential statistical witnesses; the already checked runtime program is
unchanged.

`Strong.Weighted.Probability` supplies finite total variation, its test
characterization, and contraction under deterministic maps.
`Strong.Weighted.Coupling` constructs maximal couplings and replaces one
marginal of a correlated pair while preserving the other. The joint
distance equals the original marginal distance. Its lifted kernel also
records conditional independence of the replacement from the second
coordinate given the first, including rows of mass zero. This is the finite
coupling ingredient of
[CGL Lemma 4.19, which credits Li's 2015 Lemma 3.20](https://eccc.weizmann.ac.il/report/2021/075/download/).
`Strong.Weighted.Coupling.Conditional` extends this construction across an
external transcript. The target law of `(Z,A')` must have the original `Z`
marginal. The coupling preserves the whole original `(Z,A,B)` law and has
disagreement exactly equal to the joint marginal distance. Its kernel makes
`A'` independent of `B` given `(Z,A)`. Projecting to `(Z,A',B)` preserves
`(Z,B)` jointly, with full joint distance exactly the original marginal
distance. These are average identities, including null transcript rows;
individual rows need not have small error.

`Strong.Weighted.Conditional` defines normalized conditional rows, completing
null rows uniformly, and `uniformSecondWeight`, which replaces the output
by independent uniform randomness while preserving its actual side-information
marginal. Distance from this law is exactly the average conditional distance.
Observing or forgetting part of the side information cannot increase it.
`Strong.Weighted.Expectation` proves the sharp change-of-measure bound:
every statistic in `[0,1]` changes by at most total variation between
equal-mass laws. It also identifies strong extraction with a retained-seed
distance bound.

`WeightedStrongSeededExtractor.leakage_dist_le` gives the finite average
leakage estimate. For a normalized joint source `p(tag,x)` and nonnegative
envelopes `p(tag,x) ≤ μ(tag)`, a threshold-`K` extractor with error `ε ≥ 0` has
distance at most `ε + K*∑tag μ(tag)` from a uniform output, retaining both
the complete tag and the independent uniform seed. Individual normalized
rows may violate the extractor cap. Their total mass is controlled by the
joint envelopes, and null rows contribute zero. This is the finite
average conditional-entropy step used in
[Chattopadhyay–Liao, Lemma 3.26](https://arxiv.org/pdf/2110.12652),
which credits Chattopadhyay–Goodman–Liao and ideas from
Chattopadhyay–Li (2016).

`Strong.Weighted.Merging` proves the two-sided version. Given a transcript
`Z`, the complete left and right variables `A,B` have independent laws.
The source `X` and initial observation `U` depend on the left side; the
seed `Y` and observation `V` depend on the right. An extra leak `L` may
depend on `Z,V,A`. If `μ(z,u)` bounds each joint mass
`Pr[Z=z,U=u,X=x]`, and `(Z,V,Y)` is `δ`-close to its actual `(Z,V)` law
with a fresh uniform seed, then extraction retains `(Z,B,U,L)` with error
at most `ε + δ + K*card(L)*∑μ`. The comparison preserves the actual
retained marginal. Both seed laws average the same statistic in `[0,1]`,
so the seed discrepancy costs exactly one `δ`. This theorem uses a
joint-mass envelope and permits low-entropy conditional rows.

`Strong.Weighted.Merging.Independence` specializes this to the finite
form of CL Lemma 3.26. The left variable contains `X,X₁,…,Xₜ`; the right
contains `Y,Y₁,…,Yₜ`. For arbitrary sets `S,T`, the hypothesis bounds the
joint source masses after observing `Z,X_T` and bounds the seed distance
conditioned on `Z,Y_S`. Writing `Wᵢ=E(Xᵢ,Yᵢ)`, the actual conclusion retains
`Z,Y,Y₁,…,Yₜ,W_(S∪T)` alongside `E(X,Y)`. Its error is
`ε + δ + K*card(Out)^card(S)*∑μ`, or `2ε+δ` when the last term is at most
`ε`. The sets may overlap. For `m`-bit outputs the leakage factor is
`2^(m*card(S))`; the formal contract uses the explicit joint-mass budget
in place of logarithmic average conditional min-entropy notation.

`Strong.Weighted.Transcript` formalizes the deterministic-observation rule
of CL Lemma 3.25. After observing a left-side message `f(Z,A)`, the transcript
weight is `w(z)*Pr[f(z,A)=u | z]` and its left kernel is normalized on that
event, with a uniform completion on null events. The unchanged right kernel
and these new factors give exactly the original joint law with the message
retained. The symmetric rule and a left message followed by an adaptive
right message are also proved, preserving both original side variables.
`Transcript.Envelope` supplies the exact source-mass identities behind the
entropy bookkeeping. A message with alphabet `U` computed from the source
multiplies the total joint envelope by `card U`. A message from the independent
opposite side scales each envelope row by that message's probability and
preserves its total. A source message followed by an adaptive opposite-side
message therefore pays only `card U`, including null rows.

`Strong.Weighted.Conditional.Transport` proves that a bijection of the
output depending on its retained tag preserves distance from uniform
exactly. `Strong.Weighted.Affine` applies this to a source combined with a
right-side mask. If a fixed mask acts bijectively on each fixed-seed
extractor output, the actual extraction law retains the full right state
with error `ε + δ + K*∑z μ(z)`. Here `μ(z)` bounds each joint source mass
and `δ` is the seed's joint distance from uniform given `Z`; no separate
bound for every transcript row is assumed.

`Strong.Block.Recursion.Scheduled.Affine` supplies this guarantee for the
actual Boolean extractor program on a left source XOR a correlated right
mask. Its fixed-seed XOR identity discharges the output-bijection premise,
and the checked extractor theorem discharges the extraction premise.
Both the general finite schedule and the explicit error-`2^-e` schedule
retain every right-side value and use the exact Boolean seed width,
without caller-provided extractors or finite-field instances. This proves
the retained-law estimate used by the first affine extraction step in CL
Theorem 6.1. Matching its parameters and transcript budgets, the
correlation-breaker call, and the evolving alternating/doubling guarantees
remain open.

`Strong.Weighted.Alternating` proves the next local transition. Reveal a
right-side message `V`, then use a seed computed from the left state and
that message to extract from the right source. The original normalized
sides are independent given `Z`, and the next seed is `δ`-close to uniform
jointly with `(Z,V)`, retaining its actual marginal. The output retains the
entire left state and the message. Its error is `ε + δ + K*∑μ` for a joint
message-and-source envelope, or `ε + δ + K*card V*∑μ` for an original
source envelope. The proof updates the actual transcript and swaps the
factored sides, so the incoming seed discrepancy is charged once.
`affine_alternating_dist_le` obtains that seed from an actual first affine
extraction call: the revealed right message consists of its seed and its
extracted mask. The two-call law uses both original sources and retains
the complete left state. The resulting bound includes both extractor
errors and both explicit entropy budgets. This supplies a local transition;
the full tampering-set induction and parameter allocation remain open.

`Strong.Weighted.LookAhead` now derives both honest seed transitions in the
actual two-round, one-tampering computation. Write `s1=prefix(q)`,
`r1=W(x,s1)`, `s2=QExt(q,r1)`, and `r2=W(x,s2)`, with the same calls on
arbitrarily correlated tampered inputs. The final law retains the entire
right state and both first outputs. If the original seed has joint error
`δ`, the left/right extractor errors are `ε,η`, and their thresholds are
`K,J`, the bound is
`2ε+η+δ+K*(1+card(Mid×Mid))*∑μ+J*card(Seed×Seed)*∑ν`.
Only the original source envelopes and seed error are premises; the
second seed estimate follows from the actual calls. This is the two-round
argument of [Chattopadhyay–Goyal–Li, Lemma 6.5 and Claim 6.6](https://arxiv.org/pdf/1505.00107),
with explicit average entropy accounting that includes null transcripts.

`Strong.Weighted.Perturbation` separately handles a seed approximately
uniform jointly with the source and tag. It proves error
`ε + 2δ + K*∑μ` while retaining the actual tag-and-seed marginal.
Comparing with the independent-seed reference marginal costs only one
`δ`; returning to the actual marginal can cost the second. These are
finite stability bounds derived from leakage and deterministic contraction.

`Strong.Block` defines a block source by prefix-mass inequalities,
`K*p(prefix, next)≤p(prefix)`. Prefixes and normalized mixtures preserve
these inequalities. A source on `t` blocks has joint cap `K^t`; full
conditional entropy forces exact uniformity on all block tuples.
The zero-, one-, and two-block characterizations are
checked, including the bridge to `Strong.Block.Splitting`. For two blocks
with `2^m` possible values each, a source of min-entropy `k` has a repaired
two-block source of conditional min-entropy `t` and error at most `2^-e`
whenever `t≤m` and `m+t+e≤k`. The first marginal is preserved exactly.
The proof uniformizes only low-mass rows. This formalizes the finite
two-block repair in
[CGL Lemma 5.3, attributed there to Goldreich--Wigderson (1997)](https://eccc.weizmann.ac.il/report/2021/075/download/).
The explicit repair also preserves the original joint point cap, a useful
invariant when it is applied inside a longer block source.

`Strong.Block.Conditioning` decomposes a block source into its capped head
and normalized block-source tails. Zero-mass head rows are completed using
a positive row. Its converse also permits unnormalized nonnegative row
coefficients with the prescribed head totals. `Strong.Weighted.Mixture`
proves that retaining a mixture tag gives exactly the weighted sum of
component total variation distances. In particular, retained-seed distance
is the average of the conditional distances at each seed.

`Strong.Block.Condenser.Repair` replaces a deterministic head `f(a)` while
preserving the latent state's conditional block-source tail. The repaired
tuple has the prescribed capped head, remains a block source, and its joint
distance is exactly the distance between the old and new head marginals.
The construction first repairs the joint law of `(f(a),a)`, then attaches
the same normalized conditional tail to each latent value. This gives
the factorization needed to preserve all tail prefix caps.

`IsBlockSource.exists_split_pow_two` proves the finite power-of-two form of
[CGL Corollary 5.4](https://eccc.weizmann.ac.il/report/2021/075/download/).
For a threshold-`2^k` source on `t` pair blocks, each half with `2^m`
possible values, `s≤m` and `m+s+e≤k` give a threshold-`2^s` source on
`2t` successive halves within total variation `t*2^-e` of the actual split
law. `splitBlockEquiv` preserves the order first half, second half, then
the next pair. The hypothesis is a conditional block-source bound after
each earlier pair; the pairs need not be independent. The proof repairs a
head pair while retaining its original joint cap, uses correlated head
replacement to preserve the remaining input block caps, and applies
induction to its conditional tails. Splitting adds no random seed, and
the theorem includes zero blocks without a feasibility restriction on `k`.
`exists_split_pow_two_seedFamily` applies this repair separately at every
earlier seed and retains that seed once in the joint law. Exact averaging
gives the same `t*2^-e` bound, without adding randomness or assuming that
the source is independent of its earlier seed.

`WeightedStrongSeededCondenser.block` now proves
[CGL Lemma 5.5's shared-seed conclusion](https://eccc.weizmann.ac.il/report/2021/075/download/).
For a threshold-`Kin` source of `t` blocks and a strong condenser from `Kin`
to `Kout` with error `ε`, the joint law

```text
(Y, C(X₁,Y), ..., C(Xₜ,Y))
```

is within `t*ε` of a uniform-seed family of threshold-`Kout` block sources.
The blocks may be dependent, and only one seed is retained. The proof
corrects conditional tails by induction, then applies head replacement
separately at each seed and averages its exact distance. It does not require
an error bound at each individual seed.

`WeightedStrongSeededExtractor.block` specializes this to comparison with
uniform joint output. `decodedExplicitCondenser_block_ofFn` applies the actual scheduled
map to every Boolean-vector block with the same field seed, preserving
threshold `2^k` in the ideal block source with error at most `t*2^-e` for
every positive rate `u`. The generic encoded variant is also checked.
`explicitBlockCondenserBits` computes one shared-seed level on a concatenated
word of fixed-width blocks. Its uniform `FP` certificate accepts all sizes,
parameters, blocks, seed, and block count as runtime data; its tuple theorem
identifies the output with the concatenation of the individual program outputs.
The exact length is the block count times the component output length.
`explicitBlockCondenserBits_eq_condenseSplitMap` identifies this runtime
output with the flattened tuple of the statistical condense-and-split map,
using the canonical encoding of the field seed. It keeps each first half
immediately before its second half, including the zero-width and empty cases.
At the leaves, `decodedOneShotExtractor_block_ofFn` reuses one pair of
independent field seeds across all `t` blocks of threshold `2^(ell+2e)`.
It compares the full tuple of `t` outputs, each containing `ell` bits,
with uniform at error at most `t*2^-e`, retaining the seed pair only once.

`Strong.Weighted.SeedStep` describes adding one fresh independent uniform
seed to an earlier joint law and retaining both seed coordinates. Its
deterministic composition identity connects successive seeded operations
to an actual function of the input and the whole seed tuple. Distance
contracts through this operation, even when the earlier source and seed
are correlated. `WeightedStrongSeededCondenser.condenseSplit` therefore
carries a previous joint error `η` through a level at total cost
`η+t*(ε+2^-e)`. `WeightedStrongSeededExtractor.retained_block` gives the
corresponding final extraction cost `η+t*ε`, comparing all seeds and output
blocks jointly with uniform.

`recursiveBlockMap` is the finite recursive map for varying block alphabets
and seed types. If level `i` preserves threshold `2^(k i)`, its half-output
alphabet has `2^(m i)` values, and

```text
k(i+1) ≤ m(i),
m(i) + k(i+1) + e(i) ≤ k(i),
```

then `exists_recursiveBlockSource` produces a nearby threshold-`2^(k h)`
block-source family after `h` levels. Starting with `t` blocks, there are
`2^h*t` blocks, and the extra joint error is exactly budgeted by

```text
Σ i<h, (2^i*t) * (ε(i) + 2^(-e(i))).
```

`recursiveBlockExtractor` begins with an initial condenser, performs those
levels, and applies one final shared-seed extractor to all leaves. Its
strong-extraction theorem discharges the initial block-source witness
using the initial condenser's guarantee. For one initial block and common
component and splitting error `2^-E`, the full bound is
`(3*2^h-1)*2^-E`. The checked choice `E=e+h+2` makes this at most `2^-e`.
The retained seed alphabet has cardinality equal to the product of the
initial, level, and final seed cardinalities. In particular, seed widths
add when those cardinalities are powers of two. No seed is charged once
per block. These are the finite statistical recursion and accounting
behind [CGL Theorem 5.6](https://eccc.weizmann.ac.il/report/2021/075/download/),
for supplied components satisfying the displayed finite conditions.
The recursion also preserves fixed-seed additivity: splitting respects
pointwise addition, and the component additivity hypotheses propagate
through every executed level and the final leaf map. This statement uses
only addition structures; the intended binary-vector instances supply
their usual vector-space interpretation.

`explicitCondenserPair` supplies the required pair-shaped component from
the actual scheduled bit program. Write `H=explicitCondenserHalfWidth n k e u`
and let `b` be the selected field bit width. The output has exactly `2H`
bits: its first and second `H` bits are the two Boolean-vector outputs.
Because every field coordinate has even width, no padding is needed.
Injective output transport preserves the threshold `2^k` and error `2^-e`,
and the checked rate bound is `u*(H+H) ≤ (u+1)*k + u*b`.
The capacity bound `k ≤ 2H` follows from the actual coordinate count. For
`u>1`, the sufficient budget

```text
u*(b + 2*(s+E)) ≤ (u-1)*k
```

implies both `s≤H` and `H+s+E≤k`, where `E` is the splitting error exponent.
A second version substitutes the proved upper bound on `b`, removing the
field-width rounding from this sufficient condition. The maximal choice
`s=k-H-E` has a separate checked budget ensuring that natural subtraction
does not truncate and that `H+s+E=k` holds exactly.

`scheduledBlockExtractor` now specifies every component in that recursion.
For natural parameters `n,h,L,e` with `clog 2 (n+1)≤L` and `h≤L`, set

```text
E = e+h+2,
Q = 4096*(L+E+1),
k(i) = 4^(h-i)*Q.
```

First condense at rate parameter one into a single block of actual width
`N=scheduledBlockInitialWidth n h Q E`. At level `i<h`, apply the rate-three
paired condenser at entropy `k(i)` and the current actual block width.
Use the one-shot extractor with output length `L` at every leaf.
The checked reserve pays every rounded splitting inequality. The initial
width satisfies `k(0)≤N≤64*k(0)`; all intermediate payloads occupy at most
`2*N` bits, and the block count is at most `k(0)`.
`scheduledBlockExtractor_dyadic` proves strong extraction of `2^h*L` bits
from sources of min-entropy at least `4^h*Q`, with error at most `2^-e`.
For every fixed complete seed, `scheduledBlockExtractor_xor` sends input
XOR to coordinatewise addition in `ZMod 2`.

The actual retained seed type has cardinality `2^d`, where
`d=scheduledBlockSeedBits n h Q E L`. Its checked finite bound is

```text
d ≤ 8192*(L + (h+1)*(E+h+clog 2 (L+E+1)+1)).
```

This constant-rate schedule implements the recursive method of
[CGL Theorem 5.6](https://eccc.weizmann.ac.il/report/2021/075/download/)
with a factor-four entropy cost per level. It does not claim CGL's sharper
entropy bound. `Scheduled.Asymptotics` now fixes natural `a,e` and sets

```text
L = clog 2 (n+1),
h = a*clog 2 (L+1),
E = e+h+2,
Q = 4096*(L+E+1).
```

The named `polylogBlockExtractor a e n` is this actual scheduled map.
`polylogBlockEntropy_isLittleO` proves that its entropy-bit threshold
`k0=4^h*Q` is `o(n)`, so it eventually fits within the `n` source bits.
`eventually_polylogBlockSeedBits_le` bounds the actual total seed length
by `16384L`. The finite theorem `polylogBlockOutputBits_bounds` gives

```text
L^(a+1) ≤ output bits ≤ 2^a*(L+1)^(a+1).
```

`eventually_polylogBlockExtractor` supplies strong extraction with error
`2^-e` from every normalized source with point masses at most `2^-k0`.
All limits fix `a,e` before taking `n` large. The source support threshold
is `2^k0`; the quantity proved sublinear is its logarithm `k0`.

The full varying-depth bit program is also constructed. Its numerical
state tracks current width and entropy, updating entropy by division by four.
`Scheduled.State.Parameters` takes a runtime requested depth, clips it to
`L`, and proves the independent bound `4^depth≤4*(n+1)^2`. Bounded-power
generation then computes the initial entropy before the compressed width;
the selected reserve discharges all splitting budgets on every input.
`Scheduled.Run` bounds every complete intermediate state, including unary
dimensions, block count, payload, and unused seed suffix. Initial payload
generation, every block level, and final leaf extraction belong to one
uniform `FP` program (`scheduledBlockExtractorEval_mem_FP`). This theorem
has no numerical-validity premise and covers malformed paired inputs.

`Scheduled.Codec` gives an exact equivalence between the semantic seed
tuple and words of length `scheduledBlockSeedBits`, using the explicit
field coefficient codecs and no field enumeration. The layout is initial
seed, fresh internal seeds in level order, then the shared final condenser
and hash seeds. `scheduledBlockRun_eq_recursiveBlockMap` proves that the
runtime loop computes the exact semantic leaf tuple and leaves the final
seed suffix intact. `scheduledBlockExtractorBits_eq_scheduledBlockExtractor`
then identifies the complete program output with the statistical extractor's
tuple, serialized in block order. This equality has no entropy or reserve
premise. `eventually_polylogBlockDepth_le` shows that the fixed
family's raw depth is eventually at most `L`, so runtime clipping eventually
preserves its parameters exactly.
`polylogBlockExtractorProgram_mem_FP` certifies one total string function
for each fixed `a,e`, on `pair source seedWord`.
`eventually_polylogBlockExtractorProgram` proves its exact eventual
agreement with the serialized family for every input and canonical seed.

`scheduledBlockBooleanExtractor` runs this bit program on fixed-length
Boolean source and seed vectors and reads its output in block order.
Its coordinate equality and fixed-seed XOR law hold for all natural
parameters. `scheduledBlockBooleanExtractor_dyadic` proves the same
strong-extraction guarantee with the entire Boolean seed retained, requiring
only `clog 2 (n+1) ≤ L` and `h ≤ L`. The statistical statement needs no
caller-supplied finite-field instances: the codec and Boolean output
equivalences preserve the normalized joint guarantee exactly.

`Scheduled.BoundedDepth` supplies conservative finite parameters for the
short alternating calls in a correlation breaker. If `clog 2 (n+1) ≤ L`,
`64 ≤ L`, `h ≤ 64`, and `E ≤ L`, the actual scheduled seed has at most
`2^24*L` bits. With reserve `4096*(L+E+1)`, depths 24 and 64 have entropy-bit
thresholds at most `2^62*L` and `2^142*L`, respectively, whenever
`1 ≤ L` and `E ≤ L`. Their exact output lengths are `2^24*L` and `2^64*L`.
`Scheduled.Matched` packages these widths into `matchedBlockExtractor`:
its padded seed has `2^24*L` bits and its flat output has `2^h*L` bits.
Only the prescribed seed prefix enters the actual bit program; the entire
padded seed remains retained in the strong guarantee. For `E=e+h+2≤L`,
the error is `2^-e`. The exact XOR law holds for every parameter choice.
`Matched.Program` supplies one total uniform `FP` evaluator, including
generation of all parameters and the exact seed cut. Invalid parameters
return the empty word; canonical valid inputs compute the vector extractor
exactly, even with an arbitrary extra seed suffix.

`CorrelationBreaker.FlipFlop.Program` defines and computes the concrete
three-call look-ahead and eight-call advice-bit step of
[CGL Algorithm 1](https://arxiv.org/pdf/1505.00107). The two refresh calls
use depth 64 on the original full right source. All other calls use depth
24, so their output fits the common seed width. The two advice choices
select opposite look-ahead outputs at the refreshes. Exact runtime/vector
agreement is proved for a common scale satisfying `e+66≤L` and the
ceiling-log bounds for both original source lengths and the intermediate
state width `2^64*L`. Registered `polytime` certificates cover the complete
step, variable parameters, and conditional choices. Statistical estimates
for its component calls are proved separately from the runtime.

`FlipFlop.LookAhead` connects the actual three-call program to the checked
two-round probability argument. Its second output is close to uniform
retaining the full right state and honest/tampered first outputs, with
error `3*2^-e+δ+K*(1+M)*∑μ+K*M*∑ν`, where `K=2^(2^62*L)` and
`M=2^(2*2^24*L)`. The statement assumes the original joint source envelopes
and seed-prefix error `δ`; it derives the intermediate-seed guarantee
from the actual computation.

`Strong.Weighted.Coupling.Factored` repairs a nearly uniform right-state
coordinate at exactly its joint distance from uniform given the transcript.
The original left and right sources keep their full joint law. The new
coordinate is uniform given the transcript and may remain correlated with
the original right source. Transferring a later guarantee to the actual
law costs at most twice the repair distance, or once when the retained
marginal is proved unchanged.

`FlipFlop.UniformState` applies this repair to the actual matched look-ahead.
If the whole input state has joint error `ρ`, its bound is
`3*2^-e+2ρ+K*(1+M)*∑μ+K*M/C`, where `C=2^(2^64*L)` and `K,M` are as
above. There is no pointwise entropy premise for the approximately uniform
state. The prefix of an exactly uniform state is proved uniform.

`Strong.Weighted.LookAhead.Refresh` derives both first-refresh estimates
from the original prefix error and source envelopes. The transcript records
both initial states and all four first look-ahead outputs; the second-output
refresh also retains the tampered refresh seeded by its first output.
Exact factorizations preserve conditional independence. The left envelope
pays for four short outputs, and the right envelope pays for the initial
state pair. `FixedTampering` proves the next extraction and refresh when
the tampered seed is an arbitrary function of the left source and transcript.
These statements derive their seed estimates from the actual computations.

`FlipFlop.Opposite.False` composes these steps into the complete actual
honest-zero/tampered-one execution. It retains both full look-ahead histories,
both refreshed states, the tampered final output, and the original left state.
Only the original source envelopes and initial prefix error are assumed.
Writing `D=2^(2^24*L)`, `C=2^(2^64*L)`, `K=2^(2^62*L)`,
`J=2^(2^142*L)`, and `ε=2^-e`, its first-refresh error is
`ρ=2ε+δ+K*∑μ+J*C²*∑ν`. The final bound is
`2ρ+4ε+K*(1+D²)*D⁴*∑μ+K*D²/C+J*C⁵*∑ν`.
The approximate refreshed state is repaired in the proof, with its distance
charged explicitly; the theorem concerns the original deterministic program.
The other opposite-bit orientation and the preservation case remain open.

`CorrelationBreaker.Advice` initializes from the right-source prefix and
folds the concrete step over the advice bits in order, preserving both
original sources. This is the loop in
[Chattopadhyay--Goyal--Li Algorithm 2](https://arxiv.org/pdf/1505.00107).
`adviceCorrelationBreaker` adds a final depth-24 left-source extraction;
that finishing call is additional to Algorithm 2. The total string runtime
agrees with this vector construction under the common size guard and is
uniformly polynomial-time for arbitrary inputs and advice lengths. Its
loop proof bounds the complete encoding, including both sources, unary
parameters, remaining advice, and current state. The opposite-advice and
preservation estimates must still be composed into a statistical invariant
across the complete advice chain.

The one-shot primitive alone has finite seed cost of order `ell+e+log n`;
the checked recursion supplies the larger polylogarithmic output with
logarithmic total seed length.

The separate `NearHalving` schedule supplies the linear-output extractor
needed for the amplification neighbor map `Γ`. For depth `h`, reserve `Q`,
and local error exponent `E`, it starts with the unchanged input and uses

```text
u = 16*(h+1),
k(i) = 2^(h-i)*(8*h+8+(h-i))*Q,
ell = (8*h+7)*Q,
M = 2^h*ell.
```

The exact accounting identity `9*M + 2^h*Q = 8*k(0)` keeps a constant
fraction of the source entropy as output. The sufficient reserve inequality
`12*(u+1)*T + 4*E ≤ Q`, where `T` bounds the initial condenser budget,
pays every splitting inequality at the actual rounded widths. Intermediate
payloads have at most twice the original source width.

For the named Gamma family, set

```text
L = clog 2 (b+1),
R = clog 2 (L+1),
h = log 2 b - 3*R - 15,
E = h+4,
Q = ceil(b / (2^h*(8*h+7))).
```

`GammaBlockSizeGuard b` is the explicit condition `3*R+15 ≤ log 2 b`.
`eventually_gammaBlockSizeGuard` proves it for all sufficiently large `b`.
Under that guard, the finite arithmetic proves `M≥b`, `k(0)≤2b`, the
full reserve inequality, and an actual total seed length at most `2^27*L^3`.
`gammaBlockExtractor_weighted` then gives retained-seed strong extraction
on `8b` input bits, at support threshold `2^(2b)` and error `1/4`, keeping
the first `b` output bits. Its ordinary flat-source corollary is
`gammaBlockExtractor_flat`. No caller-supplied extractor or field instances
occur in these statements. This is a conservative finite specialization of
the CGL recursive construction, with an explicit cubic-logarithmic seed
bound; it does not claim the sharper seed dependence of their general theorem.

The runtime uses the actual variable-rate block condenser and the shared
one-shot leaf extractor. Its size proof counts numeric workspace, payload,
block count, and unused seed suffix. `2^h≤b+1` certifies parameter generation
on every input, while an explicit zero-iteration fallback handles failure of
the size guard. Exact codecs and loop correctness identify the runtime with
the statistical map; both final seeds use fixed-width slices, so extra
trailing bits are ignored. The retained-seed padding theorem preserves the
strong error even for tests that inspect those unused bits.

`gammaBlockExtractorEval_mem_FP` certifies the single total evaluator on
`pair source seedWord`, inferring `b` as the source length divided by eight.
`gammaBlockPaddedExtractor` reads that actual program on a Boolean seed of
the simple computed width `gammaBlockSeedBudget b = 2^27*L^3`.
`gammaBlockPaddedExtractor_eval` identifies its entire output with the
paired evaluator for every `b`. Under the guard, its weighted strong and
ordinary flat guarantees hold for every source at threshold `2^(2b)`,
with all bits of the padded seed uniformly sampled. The padding prefix is
proved to give exactly the original semantic Gamma output.

The affine correlation breaker, its internal extractor parameters, the
required parity estimates, and the final uniform `P` hard family with
sublinear log-threshold remain open.

## The graph theorem is proved

`Bisection.exists_bisectionBound` proves the
[Monien–Preis conclusion](https://doi.org/10.1016/j.jda.2005.12.009): for every
`ξ > 0`, all sufficiently large simple cubic graphs on `n` vertices have
a balanced cut of at most `(1/6 + ξ) n` edges. The checked
[Fomin–Høie reduction](https://fedorvf.github.io/articles/2006/2006b.pdf)
then gives `exists_pathwidthBound` with no graph assumption.

The local helpful-set proof uses a connected-cluster argument developed in
this formalization, replacing the source proof's marked-tree reorganization.
Let `B` be the simple black graph and `R` a loopless red multigraph on the
same vertices, with `degree B + degree R = 3` at every vertex. Parallel red
edges retain distinct identities. For `M > 0`, let `U` be the union of black
components of size at most `M`, and let `W` be its complement.

If a red edge has both endpoints in `U`, its endpoint components give a
positive set of size at most `2 M`. Otherwise partition `W` into connected
clusters `P` of size at most `3 M`, with `M · number_of_clusters ≤ 2 |W|`.
If every cluster had at most as many red edges into `U` as black edges
leaving it, connectivity and the degree sum would give

```text
2 M |E(R)| ≤ (M + 4) |W| ≤ (M + 4) |V|.
```

Consequently, density `(M + 4) |V| < 2 M |E(R)|` forces a cluster with a
surplus. Attach the original small black components reached by those red
edges. Their black cuts are empty, and the resulting positive set has at
most `3 M (1 + 3 M)` vertices. Repeated attachments and parallel edges are
covered by the incidence-counting proof.

For a normalized cubic side of cut density above `1/3 + ξ`, suppression
gives red density above `1/2 + 3ξ/2`. Taking `4 ≤ 3ξM` and lifting the positive
set gives a helpful set of at most `12 M (1 + 3 M)` vertices. Only the first
boundary-normalization phase is needed; reversing it multiplies the size
by at most three. Thus `Bisection.exists_bounded_helpful` gives the uniform
bound `36 M (1 + 3 M)` for arbitrary cubic sides. Accumulation and
logarithmic-cost rebalancing complete the bisection argument.

The thin-path, weighted-tree, and restoration developments remain reusable
APIs. The later color-swap and leaf-reorganization steps of the original
route are not prerequisites for this proof.

## What is proved

| Step | Formal development |
| --- | --- |
| Cut counting | `Network.card_accepting_le` in `Algebraic.LowerBound.Cutwidth.Network`: for `1 < K`, a network of cutwidth `w` and maximum degree three computing a `K`-rectangle-free function either accepts fewer than `K · 2 ^ (n − n')` inputs, where `n'` inputs are read, or accepts at most `|V| · 2 ^ (w + 3) · (K − 1)²` inputs. |
| Wiring graph | `Wiring.network`, `Wiring.network_computes`, `Wiring.loopless`, `Wiring.maxDegreeLE_three`, `Wiring.connected`, and the counts `Wiring.card_edge_sub_card_vertex`, `Wiring.card_vertex_le_two_mul_size` in `Algebraic.LowerBound.Cutwidth.Wiring`. In particular, `|V| ≤ 2s + 1` independently of the declared input count. |
| Boundary transition | `PathDecomposition.exists_between_of_crossing`: the induced graph on the two cut boundaries has a path decomposition starting and ending with the respective boundaries, with bags of size at most the number of crossing edges plus one. |
| Endpoint deletion | `PathDecomposition.exists_endsAt_of_delete` restores a deleted boundary vertex once all its neighbors are in the terminal bag, then appends the prescribed endpoint subset. |
| Tree component | `boundary_reduction` gives the large-boundary induction alternatives: a vertex with at most one outside neighbor, or a tree component outside the boundary. `complement_card_edges_lt` and `exists_tree_component_of_card_edgeFinset_lt` prove the counting step. |
| Tree decomposition | `exists_tree_centroid` leaves components of at most half the tree's size. `PathDecomposition.exists_of_components` concatenates their decompositions, and `exists_addVertex` restores the centroid at a cost of one vertex per bag. `PathDecomposition.exists_tree` and `exists_forest` give bags of size at most `Nat.clog 2 n + 1`. |
| Endpoint assembly | `PathDecomposition.exists_glue` concatenates induced decompositions whose adjoining bags contain every shared vertex. `exists_pad` and `exists_attach` add a subgraph along a fixed boundary. |
| Subcubic endpoints | `PathDecomposition.exists_subcubic_endsAt` completes the endpoint induction for every prescribed `X`, with bags of size at most `max X.card (n / 3 + 1) + Nat.clog 2 n + 1`. No bisection hypothesis is needed for this lemma. |
| Bisection assembly | `PathDecomposition.exists_of_cut` joins both sides through their boundary graph. `exists_of_balanced_cut` gives bags of size at most `max b ((n + 1) / 6 + 1) + Nat.clog 2 n + 1`, where `b` is the cut size. |
| Bisection to pathwidth | `BisectionBound.exists_pathwidthBound` turns `BisectionBound ξ N₀` into `PathwidthBound (ξ + δ) N₁` for `ξ ≥ 0` and `δ > 0`. `pathwidthBound_of_bisectionBound` preserves the quantification over every positive slack. |
| Cut improvement | `helpfulness_eq_sub`, `helpfulness_add`, and `Bisection.two_moves_le_zero` give exact accounting for the two moves. `Bisection.exists_min_bisection` provides a minimum balanced cut, including odd graph orders. |
| Local helpful sets | `helpfulness_eq_degree_sum` counts outside neighbors and internal edges. `one_le_helpfulness_singleton` covers a subcubic vertex with two crossing edges; `one_le_helpfulness_of_connected_boundary` covers three or more connected boundary vertices. |
| Normalization configurations | `Bisection.exists_helpful_of_boundary_pair_three_neighbors`, `exists_helpful_of_shared_boundary_neighbor`, and `exists_helpful_of_boundary_neighbor_configuration` construct the remaining witnesses with bounds five, seven, and eleven. `helpfulness_union_boundaryLift_of_closed` supplies the common closure argument. |
| Switching neighbor | Excluding helpful sets of at most eleven vertices gives `outside_eq_one_of_no_small_helpful`, `boundary_degree_le_one_of_no_small_helpful`, and `exists_switch_neighbor`. The latter finds the interior neighbor with at most one boundary neighbor needed for either normalization switch. |
| One normalization switch | `Switchable` and `switchEdges` describe replacing two disjoint edges by two absent edges. `exists_boundary_switch` and `exists_three_neighbor_switch` construct valid configurations. `switchEdges_degree`, `switchEdges_cut`, and `switchEdges_boundary` preserve the relevant invariants. |
| Local reverse transfer | `helpfulness_switchEdges` gives the exact indicator formula. `exists_restore_boundary_switch` and `exists_restore_three_neighbor_switch` extend a moved set by at most two or four vertices without losing helpfulness. An enlargement completes a pair with exactly one previously selected endpoint. |
| Boundary-edge normalization | `Bisection.exists_independent_boundary_or_small_helpful` gives either a helpful set of size at most 33 or a cubic graph with the same cut and boundary, an independent boundary, and one outside edge per boundary vertex. Every moved set transfers back with at most a factor-three size increase and no loss of helpfulness. This completes the first normalization phase, including its uniform reverse bound. |
| Complete normalization | `Bisection.exists_no_three_neighbors_or_small_helpful` completes the second phase with a factor-five reverse bound or a helpful set of at most 55 vertices. `exists_normalization_or_small_helpful` combines both phases for any cubic side: either a helpful set of at most 165 vertices exists, or a graph with the same cut and boundary has an independent boundary, one outside edge per boundary vertex, and at most two boundary neighbors per interior vertex. Every moved set transfers back with a factor-fifteen size bound and no loss of helpfulness. |
| Boundary lift | `Bisection.helpfulness_boundaryLift` proves that adding all adjacent boundary vertices gives helpfulness equal to internal red edges minus external black edges. `exists_helpful_set_of_red_surplus` bounds the lifted size by four times the witness size. These statements require an independent boundary with one outside neighbor per vertex. |
| Small black components | `exists_small_tree_component_of_edge_deficit` gives a tree component of at most `M` vertices when `(M + 1) |E| < M |V|`. `Bisection.card_interior_edges` and `boundary_red_density` turn normalized cut density into this deficit; `exists_small_interior_tree_component` applies it with a bound depending only on the density slack. |
| Suppressed graph | `Bisection.exists_boundarySuppression` constructs a loopless red multigraph indexed by boundary vertices. `BoundarySuppression.degree_sum`, `internalEdges_card`, and `boundaryInterior_cut_card` prove the exact correspondences. `BoundarySuppression.exists_helpful_set_of_positive` transfers a positive witness to a helpful set with at most four times as many vertices. |
| Positive red/black sets | `RedBlack.exists_positive_of_component_edge` gives a set of size at most `2 M` from a red edge joining black components of size at most `M`. `exists_positive_of_thin_walk` uses gap averaging to select three nearby red attachments and produces a positive set of size at most `8 M + 1`. These prove the first two constructions of Monien–Preis's core lemma. |
| Connected clusters | `RedBlack.ConnectedPartition.exists_partition` partitions a connected subcubic graph of order greater than `M > 0` into connected sets of size at most `3 M`, with `M · number_of_parts ≤ 2 · order`. |
| Red density | `RedBlack.exists_positive_of_density` produces a positive set of size at most `3 M (1 + 3 M)` from `(M + 4) |V| < 2 M |E(R)|`. `exists_positive_of_red_density` accepts real density `1/2 + ε` and `2 ≤ ε M`. |
| Bounded helpful sets | `Bisection.exists_bounded_helpful` gives size at most `36 M (1 + 3 M)` when `4 ≤ 3ξM` and cut density exceeds `1/3 + ξ`. |
| Sharp graph bounds | `Bisection.exists_bisectionBound` and `exists_pathwidthBound` prove the sharp asymptotic cubic bisection and pathwidth bounds for every positive slack. |
| Weighted trees | `WeightedTree.sum_nonneg_of_leaf_nonneg` gives the forest weight inequality. `exists_adjacent_pair_lt_of_sum_lt` shifts it by a threshold, and `exists_adjacent_pair_le` proves Monien–Preis's weighted-tree light-pair lemma for natural-number weights. |
| Edge restoration | `RedBlack.positive_restore_cut` transfers positivity from a graph with a deleted black cut to the original graph by adding the isolated set. It counts only new internal red edges and allows overlap with empty black cut. `positive_restore_two_boundary` covers an added set with at most two boundary edges. |
| Simultaneous restoration | `RestorationFamily` records disjoint regions with black cuts of size at most two and closed red attachments. `RestorationFamily.exists_positive_restore` bounds the enlarged witness by `|X| + L |cut(X)|`; `exists_positive_restore_of_degree` gives `(1 + d L) |X|` when black degree on the witness is at most `d`. The bound is independent of the number of regions and permits overlapping attachments. |
| Closed core witnesses | `RestorationFamily.exists_positive_of_closed_core` creates positivity when a closed core set absorbs one entire nonempty region boundary. The degree version gives the same `(1 + d L) |X|` size bound, restoring all incident regions in one step. |
| Adjacent core witnesses | `RestorationFamily.exists_positive_of_restricted_core_adj` applies restoration to adjacent actual core pieces. `exists_positive_of_light_core_forest` and `exists_positive_of_light_core_tree` turn their explicit weight hypotheses into a positive witness of size at most `2 M (1 + d L)`. |
| Cycle selection | `RedBlack.exists_delete_to_bridges` preserves reachability while leaving every retained designated edge a bridge. `cycle_contains_boundary_of_meets_region` shows that a cycle entering a connected degree-two region uses every boundary edge. `exists_isolate_regions_without_cycles` selects at most the original cycle rank many regions to isolate and excludes all cycles through a supplied family with distinct chosen boundary edges. |
| Accumulation | `Bisection.exists_helpful_set_of_margin` proves the iteration and its size bound, assuming the bounded local helpful-set lemma. `abs_helpfulness_le_mul_card` controls the cut change by the maximum degree times the number of moved vertices. |
| Rebalancing | `Bisection.exists_subset_cut_le` selects a subset of every requested size with cut at most `max cut(S) (|S| / 3 + 1) + Nat.clog 2 |S| + 2`. `exists_rebalancing_set` specializes this to a logarithmic-cost move from a side of cut density above `1/3`. Neither theorem assumes a bisection bound. |
| Local-to-global reduction | `Bisection.exists_bisection_of_helpful` and `exists_bisectionBound_of_helpful` derive the finite and asymptotic sharp bisection bounds from the bounded local helpful-set lemma alone. They use a gain of `Nat.clog 2 n + 3`; the maximum in the rebalancing bound handles overshoot. |
| Compression | `Multigraph.Compression` in `Algebraic.LowerBound.Cutwidth.Compression`: merging adjacent blocks until the quotient is simple and 3-regular, with `quotient_isRegularOfDegree` and the excess bound `card_blocks_add_le`. |
| Median ordering | `MedianOrdering.card_cutFinset_key_lt_le` in `Algebraic.LowerBound.Cutwidth.MedianOrdering`: a path decomposition with bags of size at most `p + 1` gives a vertex ordering of a cubic graph with prefix cuts at most `p + 2`. |
| Expansion | `Compression.exists_linearOrder` and `Multigraph.orderingBound_of_pathwidthBound` in `Algebraic.LowerBound.Cutwidth.Expansion`: `PathwidthBound ξ N₀` implies `OrderingBound (2 ξ) (N₀ + 9)`. |
| Assembly | `lt_size_of_log_bounds` and `eventually_lt_size_of_rectangleFree` in `Algebraic.LowerBound.Cutwidth.FourN` handle subexponential thresholds; the original polynomial-threshold entry points remain available. |
| Extraction | `FlatSumsetExtractor.balanced`, `FlatSumsetExtractor.rectangleFree`, `FlatSumsetExtractor.card_accepting_ge`, and `eventually_hard_of_flatSumsetExtractor` in `Algebraic.LowerBound.Cutwidth.Extractor`. |
| Balanced padding | `FlatSumsetExtractor.balancePad_rectangleFree` doubles the threshold for any error below `1/2`; `card_accepting_balancePad` proves exact balance and `balancePadEval_mem_FP` preserves any supplied `FP` evaluator. `eventually_lt_size_balancePad_of_flatSumsetExtractor` and its nondeterministic counterpart give the lower bound at the full padded length. |
| Majority components | `Extractor.majorityEval_mem_FP` and the margin lemmas prove evaluation and robustness. `signSum_first_moment` through `signSum_fourth_moment` derive raw moment bounds from `ParityBiasBound`. `fourthMoment_positive_tail_of_approx` and its negative counterpart give tail mass at least `1/36` from approximate normalized moment bounds. |
| Nondeterministic circuits | `Network.forget` in `Algebraic.LowerBound.Cutwidth.Forget` drops witness ports, keeping the multigraph; `nondet_eventually_lt_size_of_rectangleFree` gives the same `(4 − ε) n` bound for circuits on `n + m` inputs with arbitrary `m`, computing `f` as an existential projection. The polynomial-threshold pathwidth entry point remains `nondet_eventually_lt_size_of_pathwidthBound`. |
| Average case | `Wiring.trace_eq_of_agree_backward` in `Algebraic.LowerBound.Cutwidth.Direction`, the one-sided count `Network.card_accepting_inter_le` in `Algebraic.LowerBound.Cutwidth.Balanced`, and `eventually_card_agree_le_of_balanced` in `Algebraic.LowerBound.Cutwidth.AverageCase`: a circuit with at most `(4 − ε) n` gates agrees with a `(K, ν)`-balanced function on at most `(1/2 + 3ν) 2ⁿ + 2 ^ ((1 − ε/24) n)` inputs. See the [average-case note](average-case-cutwidth.md). |

### The cut-counting lemma

A `Network` is a multigraph with a local check at every vertex and a port
for every variable it reads. For a linear order on the vertices and a prefix
`L`, the *past set* of a cut assignment `σ` consists of the assignments to the
variables read in `L` that extend to an edge assignment satisfying the checks
of `L` and agreeing with `σ` on the cut; the *future set* is defined
symmetrically. Gluing shows that the past and future sets of one cut
assignment form a one-rectangle, so one of them has fewer than `K` elements.

Each accepted input is charged to the first vertex at which its past set
reaches size `K`. Its key is that vertex together with the bits on the cut
before the vertex and on the vertex's at most three incident edges, at most
`w + 3` bits. Inputs with the same key are determined by an element of the
small past set before the vertex and the small future set after it, giving
at most `(K − 1)²` inputs per key and at most `|V| · 2 ^ (w + 3)` keys.

Variables not read by the network are never queried, so the past set of the
whole vertex set consists of the accepted inputs restricted to the read
variables. If that set is smaller than `K`, the lemma returns the bound
`K · 2 ^ (n − n')` for `n'` read variables instead; the assembly rules this
case out with the support lemma.

### The wiring graph

Only wires with a path to the output gate become vertices, so the graph is
connected without pruning the circuit. A signal feeding `f ≥ 2` slots is
routed through a chain of `f − 1` copy vertices; slot `i` attaches to copy
`min(i, f − 2)`, so the last copy carries the last two slots. This gives
`M − N = s' − n'` for `s'` reachable gates and `n'` reachable inputs, and at
most three edges at every vertex. Every signal except the output feeds a
slot. Charging a signal and its copy vertices to its outgoing slots gives
`N ≤ 2s' + 1 ≤ 2s + 1`. This bound also applies with arbitrarily many declared
witness inputs.

Gate vertices check that their outgoing edge carries the gate's function of
its two slot bits, the output gate checks that this value is `1`, copy
vertices check that their incident edges agree, and input vertices carry the
variable on their outgoing edge. The circuit's own evaluation satisfies every
check, and a satisfying assignment agrees with the evaluation on every edge by
induction along the topological order, so the network accepts exactly the
circuit's accepting inputs.

### From pathwidth to the ordering bound

A `Compression` is a set of blocks, each an ordered list of original
vertices, forming a partition. Two blocks merge when an edge joins them and
one has boundary at most two or they are joined by parallel edges; the larger
block is listed first. The invariants are that every block has boundary at
most three, every proper prefix of a block has boundary at most
`3 ⌈log₂ |block|⌉`, and the number of blocks plus the number of edges inside
blocks is at least the number of vertices. When no merge applies and at least
two blocks remain, connectivity forces every block to have boundary exactly
three with at most one edge to each other block, so the quotient graph on the
blocks is simple and 3-regular, and its vertex count `h` satisfies
`h + 2N ≤ 2M`.

Given a path decomposition of the quotient, every edge receives a position in
a bag containing its endpoints, distinct across edges and increasing with the
bag index. Each vertex has three incident positions; vertices are ordered by
the middle one. For a prefix ending at `v`, a crossing edge below the median
of `v` is the unique low edge of its later endpoint, one above it is the
unique high edge of its earlier endpoint, and the median of `v` is one edge.
Consecutiveness places every charged vertex in the bag of that median edge,
so the cut has at most one more edge than the bag.

Listing the vertices block by block in that order, each block in its own
order, every lower set is a union of whole blocks plus a prefix of one block.
Its cut is at most the quotient cut of the block prefix plus the prefix
boundary of the partial block, giving
`(1/6 + ξ) h + N₀ + 2 + 3 ⌈log₂ N⌉ + 3 ≤ (1/3 + 2ξ)(M − N)⁺ + 3 log₂ N + N₀ + 9`.

### The assembly

With `η = min(ε, 1) / 18` and `k = ⌈log₂ K⌉`, a circuit with
`s ≤ (4 − ε) n` gates whose output is a gate reads more than `n − k` inputs,
so the cut bound is at most `(1/3 + η)((3 − ε) n + k) + O(log n)`. Comparing
`2 ^ (n − 2)` accepted inputs with `|V| · 2 ^ (w + 3) · K ²` gives
`ε n / 6 ≤ O(log n + log K)`, which fails for large `n` under the sublinear
logarithm hypothesis. A circuit whose output is an
input wire depends on one coordinate and is excluded by the support lemma.
The asymptotic conditions are discharged by `eventually_mul_logb_add_lt`
(`log₂ n = o(n)`) and the source-entropy hypothesis. The polynomial-threshold
corollaries use `logb_isLittleO_of_eventually_le_pow`.

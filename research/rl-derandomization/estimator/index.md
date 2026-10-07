# Why the actual estimator is accurate

OpenAI's Theorem 9.8 concerns the estimator with compression, approximate
numerical access tests, and short fingerprints already included. Its proof
compares that estimator with a calculation using exact endpoint equality
within one block of statistical budgets [oai26][oai26]. This note reconstructs
that argument, using the [exact hierarchy and sampler](../target/index.md)
and leaving its [space implementation](../implementation/index.md) separate.

Fix $H=4,h_0=2$ and moment order eight. Write $B$ for logarithmic input
size, $N=2^{O(B)}$ for a stage-universe bound, $f=b_l$ for the current
stage rate, $h_l$ for the deterministic continuation vector, and $W_l$
for the deterministic accumulated reward. Statistical budget $M$ determines
an accuracy exponent $p$; neither is a requested numerical digit.
Specializing a reward task to start rate $u=f$, the exported estimate is

$$
 \frac1N\mathbb E_\sigma\sum_{v\in V_l}\frac{X_f(v)}f
       |\bar W_l(v;\sigma)-W_l(v)|^8\le C^8 2^{-8p}.
$$

This is an integrated bound: conditioning on a specified start costs a
factor proportional to $N$. Crucially, $\bar W_l$ here must be the
same fixed estimator evaluated later, on every environment.

## Sparse atoms with exact conditional means

An exact matrix row can be wide. Its stochastic representation must permit
boundedly many outgoing accesses, and correction products additionally need
boundedly many incoming accesses. For a raw matrix $G$, the hierarchy
supplies bounded row mass and entries $G(x,y)\le C f$. Split entries into
nonnegative bins at scales $a=16^{-k}$, with bin weights summing to one.
A row-rank gate $R$ suppresses a bin whenever too many retained entries
are large. Smooth switches make eighth roots Lipschitz; this permits stable
comparison even where a value becomes zero.

Suppressing rows introduces bias, so each normalized atom has an earlier
preparatory task. On the retained slice $X_u(x)=Y_t(y)=1$, where $u\le f$
and $t\le a\le C f$, its true target supplies the exact mean

$$
 q(x,y)=\mathbb E[\psi(G(x,y)/a)R T\mid X_u(x)=Y_t(y)=1],
 \qquad c(q)=\min(1,\max(1/2,q)).
$$

Here $T=1$ for dense bins and is an incoming-rank gate for corrections;
the preparatory cutoff $\psi$ equals one on the main factor's support.
Conditional retained-count estimates make $q\ge7/8$ for a nonzero dense
bin and $q\ge3/4$ for a nonzero correction with positive column multiplier.
Dividing the main gated factor by $c(q)$ therefore restores its exact
conditional mean. If the column multiplier is zero, both contributions
vanish and no positive denominator bound is needed (Lemmas 5.1, 5.3).
Preparations remain on the broad $Y_a$ domain; their mean is taken on the
narrower $Y_t$ slice. The second raw signal is
$\zeta q(x,y)\mathbf1_{Y_t(y)}$, with fixed small $\zeta>0$.

True product means are exact because the normalized right bin, after its
midpoint membership is fixed, uses only its terminal channel; the left
correction uses the independent source and midpoint channels. Importance
factors $\pi_a/\pi_{\min(a,b)}$ and $f/\pi_f$ correct terminal and
midpoint sampling. Approximate factors share randomness and are **not**
assumed independent or unbiased (Lemma 7.1). Computed normalization uses
the same clipped formula on estimated signals; it does not store $q$.

For the reward update, let $\mathcal F_l$ be the true correction table,
with conditional mean $E_l(x,z)/f$ when source and midpoint are retained.
The true sample on the inherited source slice is
$$
T_l^{\rm rew}(x_i;\sigma)=r_i(x)\left(W_l(x)+\frac f{\pi_f}
  \sum_{z:Z_f(z)=1}\mathcal F_l(x,z;\sigma)W_l(z)\right).
$$
Its conditional mean is exactly $W_{l+1}(x_i)$ (Lemma 7.1).
A budget-$m$ sample substitutes budget-$m$ estimates for the earlier tables
and vectors, including detector inputs to $r_i$; $r_0=1$ stays fixed.
These recursive samples may be biased; the following difference schedule
controls their error. [oai26][oai26]

A port is a short index naming an exposed neighbor; a paired port also
provides an inverse index for returning to the source.
Access relations require more than numerical support. An exposed port may
have weight zero, yet affect later representative selection. Every exposed
class has bounded size and a smooth witness equal to one at all its ports.
For corrections, delete every precursor port at any column exceeding the
incoming cap $K_c$: its incoming gate already makes every such weight zero.
This bounds the entire exposed relation, including zero-weight ports
(Lemmas 5.5–5.6). Values, gates, witnesses, and port orders use one common
task tuple and effective environment. A right child drops the old source
from its parameters.

## Budget differences pay for averaging

For raw arrays use

$$
 \|Z\|_{u,a;8}^8=
 \frac1N\mathbb E\sum_x\frac{X_u(x)}u
                       \sum_{y:Y_a(y)=1}|Z(x,y)|^8.
$$

Nonnegative atom outputs are compared through their eighth roots; vectors
use ordinary differences. Bounded row supports control endpoint sums.
Bounded incoming correction support controls changes of source: summing a
right-child error over old starts costs at most $K_c f/u$ in moment power.
This follows by counting incoming ports pointwise, without independence.

Lemma 7.3 gives scale costs $b/a$ for $b\ge a$, and $(b/a)^7$ for
$b<a$, in moment power. The latter exponent includes the narrower-slice
importance correction. The fixed finite task order per stage gives ranks
$\iota=O(l+1)$, decreasing on every input dependency. Set

$$
 p=\frac{M}{K_{\rm prec}}-\frac12\log_2(1/a)
       -\frac12\log_2(1/u)-A\iota.
$$

Inactive tasks, with $p\le0$, return zero and empty access classes.
For a child of budget $m$, the exact precision difference is

$$
 p'-p=-\frac{M-m}{K_{\rm prec}}
       +\frac12\log_2(a'/a)+\frac12\log_2(u'/u)
       +A(\iota-\iota').
$$

For bin terms $a'\ge c b$. Consequently the inductive child bound
$C_b2^{-p'}$, after scale conversion, is at most

$$
 CC_b2^{-p-A+(M-m)/K_{\rm prec}}
             2^{-3|\log_2(b/a)|/8}.
$$

The source-release cost is likewise paid: its eighth root times the
precision gain is $(f/u)^{1/8-1/2}\le1$. These geometric margins make
summing across scales possible.

For each sample term $T_{b,m}$, average **paired differences**
$T_{b,m}-T_{b,m-1}$, using identical walk words and wrap guesses.
Budget-zero sample terms vanish. Group increments by dyadic slack
$d\le M-m<2d$, using conditional walks of length $O(M-m)$.
Add groups in decreasing powers of two down to $d=1$, with exact base
contributions in the first group. A **prefix** is the sum through one group.
A candidate **descriptor** records formula, copy and sign choices, scale
and budget offsets, walk word, wraps, and bounded port choices. Included
scale offsets and walks have length $O(d)$, so it occupies $O(d)$ bits
(Lemma 7.5). It describes an immediate candidate, not its entire recursive path.
Contributions at the same actual endpoint are combined before measuring
the difference. Subtracting the same true stochastic term from both budgets
gives absolute norm $C C_b2^{-p-A+O(d)}$; a full sample need not be this
small (Lemma 7.7).

Uniform slice means telescope up to child budget
$\max\{0,M-\max(d,c_b)\}$, where
$c_b=\lceil c_0(1+|\log_2(b/a)|)\rceil$. Entirely omitted bins are
fine, and bounded row mass gives omission norm $O((b/a)^{7/8})$.
Conditional mixing suppresses the paired difference noise exponentially.
Thus every prefix has deterministic mean error at most
$c_*2^{-p+B_1d}$ and absolute noise at most
$c_*2^{-p-K_nd}$ (Lemmas 7.6–7.8), with $K_n$ arbitrarily large.
The first mean error is clipped relative to $1+G(x,y)/a$; the second is
absolute and retains its $Y_t$ mask. Determinism requires averaging every
coordinate used by the estimand, a condition established below.

## Compression preserves the needed errors

At slack $d$, represent a row by a common default and at most
$n_d=2^{c_2d}$ listed positions, possibly including default-valued slots.
The compression floor is $\rho_d=2^{-c_1d}$. The update
uses size ranks to choose a threshold $u_0\ge\rho_d$, maps entries of
size at most $2u_0$ to the new default, and preserves entries of size at
least $3u_0$. Its full-array map is uniformly Lipschitz. Dummy default
copies participate in ranks but never in endpoint sums or access ports.

An overflow means $u_0>\rho_d$. Before the first overflow, accumulated
changes are much smaller than the next floor. At overflow, either many
true entries exceed $\rho_d/4$, or many small-target entries have error at least
$c\rho_d$. The latter event is charged directly to prefix error power,
with factor $O((n_d\rho_d^8)^{-1})$.

The true-heavy event has conditional probability $O((n_d\rho_d)^{-1})$,
even after fixing one retained endpoint: bounded row mass bounds the heavy
set, and the conditional pair estimate bounds its expected retained count.
This rarity multiplies **deterministic mean-error magnitudes**. Noise may
correlate with overflow, so its rapidly decaying unconditional norm pays
for it instead. Only one first-overflow event occurs per row.

A stationary reference starting from truth plus earlier compression losses
preserves the relevant row functions: its $K$th first-entry rank stays
fixed or inside the flat full-gate region. When a gate is open, the separation
between entry-support and rank-gate thresholds places every supported entry
above $3u_0$, where compression is the identity. Saturation and a separate
closed-gate case prevent large raw entries from causing uncontrolled
relative error. Lipschitz propagation through the remaining dyadic groups
costs only a polynomial in $d$. Taking $c_1>B_1$, then
$c_2>8c_1+8B_1$, makes all overflow charges summable
(Lemmas 8.2–8.4, Proposition 8.5).
Range clamps beyond all remaining additive variation preserve these row
functions for exact grouping, and are nonexpansive in comparisons.
They need not preserve access lists. Assembly adds incoming-gate and column
errors using the same caps and $f/u$ accounting. Proposition 8.7 leaves
half the target error allowance unused.

## Adaptive fingerprints spend the reserve

A salt of $O(\log B)$ fair bits gives keys in $\{1,\ldots,B\}$ with
fixed-pair collision probability $O(1/B)$ (Lemma 9.1). A union bound over
the actual candidates is invalid: their discovery can depend on that salt.
Partition budgets into blocks of width $k=\lfloor\epsilon\log_2B\rfloor$,
with independent salts. A block-$b$ task may use only salts through
$b$; its conditional walks vary earlier salts and freeze current/later
salts, in its effective environment. This rule includes all structural
tests and inverse accesses. There are $O(B/\log B)$ blocks, so all salts
occupy $O(B)$ bits. Enumerating environments retains the original
fair-bit strings, including multiplicities created by reduction modulo the
fingerprint field size.

The block-clean calculation uses exact equality recursively throughout the
current block and the actual algorithm below it. It is independent of the
current salt. Earlier salts are all averaged, so its conditional means
satisfy the determinism condition above (Lemma 9.2).

Large-slack groups $d>2k$ already coincide. Their boundary list, including
default-valued representatives, and the small-group clean witness supports
over every fixed descriptor variant form an envelope of $2^{O(k)}$
endpoints independent of the current salt. Each such variant preserves
measure and freezes that salt; no adaptively chosen variant is presumed
uniform.
Any actual candidate escaping it has an actual witness equal to one where
the clean witness is zero. Charge that event to a child discrepancy,
including zero-weight candidates. For a right-factor escape, the **actual**
left correction's incoming cap pays the source sum and its $f/u$ cost
(Lemmas 9.3–9.4).

Within the envelope, the key rule aliases only new increments: add each
bucket sum to every old representative with that key, or introduce its
first valid candidate starting at the old default. Never merge stored
values. Thus collisions multiply the small paired increment height, rather
than an old value. The envelope and clean height are salt independent;
conditioning on other coordinates gives direct error
$2^{-p}2^{Ck}B^{-1/16}$, using the weaker collision bound
$O(B^{-1/2})$. This integration does **not** condition on the salt-dependent
event of staying inside the envelope (Lemmas 9.5–9.6).

For block bottom $M_b$, Proposition 9.7 closes the simultaneous induction
with $\lambda_M=2^{-D_1k+D_2(M-M_b)}$. Child errors at slack $d$
within the same block cost at most $2^{-p}2^{Cd}\lambda_{M-d}$, so the relative coupling
charge is bounded by

$$
 \lambda_M\sum_{d=1}^{2k}2^{-(D_2-C)d}
       +2^{Ck}B^{-1/16}.
$$

Choose $D_2$ to make the sum at most $1/4$, then $D_1>D_2+1$, then
$1/(16\epsilon)>C+D_1+2$. The direct term is at most
$\lambda_M/4$ after fixed minimum-size padding. Coupling fits the
reserved half; adding the clean error proves Theorem 9.8 [oai26][oai26].
The earlier analytical constants are fixed before this choice of
$\epsilon$; every resulting constant is independent of the input and $B$.

## Finite parameters close the construction

At the final reward task take $a=u=f=16^{-L}$. Its precision is
$$
p=M_{\rm top}/K_{\rm prec}-4L-A\iota.
$$
Since $L=O(B)$ and $\iota=O(L+1)$, choosing the fixed linear coefficient
of $M_{\rm top}=O(B)$ sufficiently large attains the main argument's
$p\ge(\log_2N)/8+O(1)$ requirement.

For a sufficiently large fixed $c$, every requested retention rate $r$ at
descendant budget $M$ obeys
$\log_2(1/r)\le4L+c(M_{\rm top}-M)$. A child at slack $d$ can extend
these logarithms by only $O(d)$ and loses at least $d$ of budget.
Stage resets are covered by $4L$, usage rates are minima of available rates,
and inherited suffixes add at most one copy digit per stage. Thus all
descendant rate exponents and identifier lengths remain $O(B)$.

Choose the field only after fixing these constants and ranges. For a large
fixed $C_P$, a prime $2^{C_PB}\le P\le2^{C_PB+1}$ exceeds all identifiers
and the copy radix and satisfies $P2^{-k}\ge1$ at every requested rate
$16^{-k}$. Bertrand's postulate supplies the prime; trial division finds
one using $O(B)$ space. The fixed number of rank channels and the $O(B)$
raw salt bits therefore give a uniform $O(B)$-bit environment
(Sections 7 and 12.1). [oai26][oai26]

Exact threshold fractions and switch polynomials can disappear from this
exposition; their separation, root-Lipschitz bounds, caps, and witnesses
cannot. Neither can fixed structural-test accuracy and tie rules independent
of the requested numerical digit: changing them changes the estimator.
This reconstruction is not a full independent proof audit; the cited sampler
and evaluator obligations remain part of the proposed theorem.

[Back to the main argument](../index.md).

[oai26]: ../sources.md#oai26

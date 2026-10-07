# The exact target and its sampler

[Return to the main account](../index.md).

This note reconstructs the exact hierarchy in Sections 2–4 and the sampler in
Sections 3 and 6 of [oai26][oai26]. We fix $H=4$ and two coefficient
columns (the source's $h_0=2$); below $h_l$ denotes only a value vector.
The vector formulation and sharper sampler constants below are
checked deductions; the detector and implementation claims retain their source
attributions. They do not certify the proposed derandomization theorem.
Write $B=\Theta(\log(n+2))$, $N=2^{O(B)}$ for a common stage-size bound,
and $N_0=|V_0|$. The estimator's budget $M$ and precision exponent $p$
are separate parameters.

An elementary randomized machine step has boundedly many successors and
predecessors when the full configuration is retained. Add a time coordinate,
advance halted configurations without merging their tapes, and put reward
$e(x)=1$ exactly at accepting final-time configurations. The resulting
transition matrix $S$ is nonnegative, has row sums at most one, and only
moves forward in time. Backward induction on time defines the continuation
probabilities, equivalently the finite sum
$$
h_0=\sum_{j=0}^{T}S^je\in[0,1]^{V_0}.
$$
These coordinates are acceptance probabilities, not a distribution summing to
one. In particular, $h_0(x_0)$ is the original acceptance probability.
Local incoming and outgoing ports, including inverse ports, have logarithmic
space access by the source's configuration reduction, Lemma 2.1.
[oai26][oai26]

The hierarchy keeps the invariant
$$
h_l=W_l+C_lh_l,\qquad 0\le W_l\le h_l\le1,
\qquad C_0=S,\quad W_0=e.
$$
At one stage abbreviate $C=C_l$. A nonnegative correction $E$ defines
$$
D=C-E+EC,\qquad W'=W_l+EW_l.
$$
Since $I-D=(I+E)(I-C)$, the same vector satisfies
$h_l=W'+Dh_l$. This algebra alone does not make $D$ nonnegative or
small. Those properties are the purpose of the correction and copying
construction in Section 4. [oai26][oai26]

Assume $C(x,y)\le f$. Choose fixed
$0<\theta_1<\theta_2<1/512$ and a nondecreasing Lipschitz cutoff
$$
(t-\theta_2)_+\le Q(t)\le(t-\theta_1)_+.
$$
The source also gives it the eighth-root regularity needed by estimation.
For a **fixed** column multiplier $g(y)\in[0,1]$, iterate
$$
E_0=0,\qquad E_i(x,y)=fQ((C+E_{i-1}C)(x,y)/f)g(y).
$$
Lemma 4.1 proves a size-independent iteration count. Its key argument deserves
to remain explicit. Forwardness defines a unique fixed point $E_*$, one
column at a time. Its residual $T_*=C-E_*+E_*C$ is substochastic; every
positive position of $E_*(x,\cdot)$ leaves at least $\theta_1f$ in
that residual. Hence its support $A_x$ has size at most
$1/(\theta_1f)$. Unrolling along this *single row's* increasing support
gives
$$
E_*(x,y)\le f(1+f)^{|A_x|}\le fe^{1/\theta_1},
\qquad
\frac{E_*(x,y)-E_k(x,y)}f
\le e^{1/\theta_1}\frac{(L_Q/\theta_1)^k}{k!}.
$$
There are at most $\binom{|A_x|}{k}$ increasing intermediate sequences;
each contributes $k$ factors bounded by $f$. This explains the factorial
and removes dependence on the whole graph's size. Choose a fixed $k_*$
making the last bound at most $1/512$. Acyclicity alone would only give a
graph-size bound; a constant $k_*$ keeps every stage a fixed recipe.
[oai26][oai26]

The source first runs $k_*$ pilot updates with inputs
$G_i=C+\widehat E_{i-1}C$. Deterministic scores $U_i(y)$
are true conditional expectations of sampled rank tests: they detect columns
with many substantial entries while gating heavily sampled rows. The final
multiplier is $g(y)=\gamma(\max_iU_i(y))$, where $\gamma=1$ through
$1/2$ and vanishes from $4/5$. Only then are the actual $k_*$ updates
run with this same $g$. Lemmas 4.2–4.4 establish
$$
D\ge0,\quad D\mathbf1\le\mathbf1,\quad
D(x,y)\le(k_*+1)f,\quad
g(y)=1\Rightarrow D(x,y)<f/256.
$$
They also prove $D\ge c(C+E+EC)$ for a fixed $c>0$, allowing later
estimation of the signed formula through its unsigned terms. These are
inherited detector and residual bounds. [oai26][oai26]

Copy each vertex $D_0>16(k_*+1)$ times. Let $s_j(t)$ route an entry
among its destination copies: below $1/128$ use only the primary copy;
from $1/64$ onward split equally; interpolate between. The fractions sum
to one. Put $r_0(x)=1$, and let extra row factors rise from zero to one as
$U^{\max}(x)=\max_iU_i(x)$ rises from $1/4$ to $1/2$. Define
$$
C^+(x_i,y_j)=r_i(x)D(x,y)s_j(D(x,y)/f),\qquad
P(x_i,x)=r_i(x).
$$
All other entries of $P$ vanish. Extra routing implies $g(y)<1$, hence
$U^{\max}(y)>1/2$ and every destination factor equals one. Consequently
$\sum_js_j(D(x,y)/f)r_j(y)=1$ on positive entries, proving
$C^+P=PD$. Set
$h_{l+1}=Ph_l$, $W_{l+1}=P(W_l+E_lW_l)$; the invariant follows
immediately. This uses Proposition 4.5's intertwining and replaces
Proposition 4.7's cumulative matrices by vectors. [oai26][oai26]

Every copied entry is at most $f/16$, but the full domain grows by
$D_0$. The essential count concerns **active** vertices, meaning nonzero
rows or columns. If $n'$ parents are active, Lemma 4.3 says each parent
with $U^{\max}>1/4$ consumes more than $J/(4C_\pi f)$ substantial
pilot incidences. Here an incidence means $G_i(x,y)>\delta_0f$, for a
fixed detector threshold $\delta_0>0$. Pilot row sums give at most
$n'k_*(k_*+1)/(2\delta_0f)$ such incidences overall. Taking
$$
J\ge\frac{2C_\pi(D_0-1)k_*(k_*+1)}{\delta_0}
$$
limits these parents to $n'/(D_0-1)$. All active extra copies have such
parents, so there are at most $2n'$ active children. Thus
$$
|\mathcal A(C_l)|\le N_0 2^l,\quad C_l(x,y)\le16^{-l},\quad
0\le h_0(x)-W_l(\bar x_l)\le N_0 8^{-l}.
$$
Here $\bar x_l$ is the all-primary copy; its projection factors are one.
Choose $3L\ge\log_2(32N_0)$. Then $L=O(B)$ and the error is at most
$1/32$, as required by the main argument. The full domain
$N_0D_0^L$ still has $O(B)$-bit addresses. These are Propositions 4.5
and 4.7 specialized to $H=4$. [oai26][oai26]

The sampler simplifies further. Independently for each channel choose
$$
u\text{ uniform in }\mathbb F_P^4,\qquad
v\text{ uniform in }\mathbb F_P^4\setminus\{0\},\qquad a(y)=u+yv,
$$
where prime $P$ exceeds every identifier. This is exactly the source's
rank-conditioned two-column channel. At rate $b_k=16^{-k}$, retain
$y$ when $a(y)\in A_k=\{0,\ldots,L_k-1\}^4$, where
$L_k=\lceil P2^{-k}\rceil$. Its probability is
$\pi_k=(L_k/P)^4\in[b_k,16b_k]$ whenever $P2^{-k}\ge1$.
The [reachable-rate bound](../estimator/index.md#finite-parameters-close-the-construction)
gives $k=O(B)$ even for descendant tasks. Once the reachable identifier and
rate ranges are fixed, Section 12.1 chooses a sufficiently large prime
$P=2^{O(B)}$ satisfying these requirements. Testing successive integers by
trial division finds one in $O(B)$ space. This specializes Section 2,
Lemma 3.1, and Section 12.1.
[oai26][oai26]

For distinct $x,y$, the map $(u,v)\mapsto(a(x),a(y))$ bijects onto
ordered distinct vectors. Writing $R=P^4$, we obtain, for arbitrary sets
$A,B\subseteq\mathbb F_P^4$,
$$
\Pr(a(x)\in A,a(y)\in B)
=\frac{|A||B|-|A\cap B|}{R(R-1)}.
$$
This checked specialization implies conditional retention at rate $b_k$
is at most $32b_k$, regardless of the other retention rate. For the same
box, indicators at distinct identifiers have covariance
$-\pi_k(1-\pi_k)/(R-1)$. Therefore a count $Z$ on any deterministic
set of $m>0$ identifiers has variance at most $m\pi_k$, and
$$
\Pr(Z<m\pi_k/2)\le4/(m\pi_k).
$$
Thus $C_{\rm var}=4$ suffices. Substituting $\alpha y+\beta$,
$\alpha\ne0$, sends $(u,v)$ to $(u+\beta v,\alpha v)$, a
measure-preserving bijection. Fixed copy suffixes therefore preserve the
whole joint law, not merely its marginals.

Conditioning on retention of one identifier $y$ per channel leaves independent
coordinates $(v,w)$, with $v\ne0$ uniform and $w=a(y)$ uniform in
its box; recover $u=w-yv$. Identify the box with
$(\mathbb Z/L\mathbb Z)^4$. The action
$$
(v,w)\longmapsto(Tv,Tw+c),\qquad
(T,c)\in\mathrm{SL}_4(\mathbb Z)\ltimes\mathbb Z^4,
$$
uses modulus $P$ for $v$, modulus $L$ for $w$, and is transitive:
the linear group moves any nonzero slope to any other, then a translation
adjusts $w$. Take the lazy symmetric walk on unit elementary shears and
translations $\pm e_i$. The source's Lemma 6.1 derives a **uniform spectral
gap for these specific affine generators** from Shalom's relative property
(T), Theorem 2.1, and
linear-group property (T), Theorem 2.6. This remains an external ingredient.
[shalom99][shalom99] [oai26][oai26]

Pad each salt block to a multiple of four bits and concatenate all free bits
into one affine torus; frozen bits stay fixed. Updating one of the boundedly
many independent components gives the conditional operator
$K$, with $\|K^d-\Pi\|_{8\to8}\le C2^{-cd}$, uniformly in the
moduli and conditioned identifiers, by Lemma 6.2. To express a generator
without retaining $y$, enumerate fixed-wrap variants
$$
u'=Tu+c+Lz\pmod P,\qquad v'=Tv\pmod P.
$$
Each variant is an endpoint-independent bijection of the full channel.
Since generators are fixed, a constant-sized box of integer $z$'s contains
every possible wrap. Testing $w$ and $Tw+c+Lz$ in the retention box
selects exactly one variant. It keeps the original generator's weight,
without division by the number of variants. Length-$d$ variants therefore
have $O(d)$-bit descriptions and reproduce the conditional average
exactly. These are Lemma 6.3's properties; simultaneous recursive space is
left to the [implementation argument](../implementation/index.md).
[oai26][oai26]

The [finite validation script](data/validate_sampler.py) exhausts the
specialized pair law, covariance, affine substitutions, and representative
wrap variants at $P=2,3$. It checks these identities, not the spectral gap
or the main theorem.

[oai26]: ../sources.md#oai26
[shalom99]: ../sources.md#shalom99

# Biased messages and the finite geometry bound

The finite results described here are checked in
`Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/LowerBound.lean`.
They concern the actual signed conjunction / affine-parity circuit model in
`Geometry/Defs.lean`, with unrestricted arity, depth, repeated slots, and fanout.
The proof does not assume a communication or entropy bound as a circuit hypothesis.
This note makes no priority claim. The information argument is the usual Shannon
entropy bound, implemented directly through product weights and concavity of the
logarithm; affine gate elimination has the Demenkov–Kulikov provenance discussed in
[the geometry note](geometry.md). See [pairing](pairing.md) for its restriction invariant.

## Actual messages and small fibres

Fix an Alice coordinate set U and give its complement to Bob. Alice sends one bit
per gate: the parity or signed conjunction of slots directly fed by her primary
inputs. Bob evaluates the circuit in topological order from those summaries and his
own primary inputs. One extra bit covers the case in which the designated output is
an Alice primary input. Thus a circuit with g gates has a message in {0,1}^(g+1).
`circuitOneWaySummary` proves this protocol for the actual circuit semantics.

Suppose the output function is K-rectangle-free for both colors, and Bob has at least
2K assignments. Every message fibre contains fewer than K Alice assignments. Indeed,
if a fibre had K rows, its common row would have fewer than K accepting columns and
fewer than K rejecting columns; otherwise one color would give a forbidden rectangle.
These two column classes cannot cover Bob's at least 2K assignments. A two-sided
flat-sumset disperser supplies both rectangle-free properties.

## Exact finite entropy saving

Let X be a nonempty finite input set, and let its Boolean message have t coordinates.
Assume every fibre has size at most K. Suppose r designated coordinates each have a
specified rare value occurring on at most |X|/4 inputs. No independence of message
coordinates is assumed. Define a product probability weight on messages, assigning
probability 1/4 to each designated rare value, 3/4 to its other value, and 1/2 to
either value in every remaining coordinate. The weights sum to one. The fibre bound
therefore implies

    sum_(x in X) weight(message(x)) <= K.

Apply log z <= z-1 after rescaling by |X|/K. This bounds the mean log weight above by
log(K/|X|). Expanding the product, the quarter-bias assumptions bound that mean below
by -t log 2 + r(log 2 - binaryEntropy(1/4)). Consequently

    log2 |X| <= log2 K + t - c*r,
    c = 1 - H2(1/4) > 0.

`Entropy.log_card_le_of_fibres_and_bias` proves the natural-log form;
`Entropy.input_le_bits_of_biased_oneWay` applies it to the circuit interface.
This avoids importing a probabilistic independence premise that the messages need
not satisfy.

For each of the h2 conjunction gates reading at least two distinct direct primary
variables, designate two such variables. Whenever both lie in U, the gate's true
summary forces two independently chosen Alice coordinates to specified values. It
therefore occurs on at most one quarter of Alice assignments, including inconsistent
or repeated literal cases. This is `outputKey_quarter_of_selectedPair`.

Among all a-element Alice sets, a fixed designated pair survives with frequency

    alpha = a(a-1)/(n(n-1)).

Double counting and a maximum argument give a set retaining at least alpha*h2 pairs.
No concentration estimate is needed. `Entropy.exists_subset_pair_ratio` proves the
exact finite statement, including its binomial-counting origin.

## Combining entropy with affine pairing

Set k=ceil(log2 K), b=k+1, and a=n-b, assuming k+3<=n. Bob has 2^b>=2K assignments.
The resulting checked circuit inequality is

    n <= g + 1 + b + log2 K - c*alpha*h2,
    alpha = (n-k-1)(n-k-2)/(n(n-1)).

The independently checked affine pairing bound is

    2n <= g + h2 + 2k.

Writing d=c*alpha, their combination gives

    (1+2d)n - 2dk - k - 2 - log2 K <= (1+d)g.

This is exactly `Geometry.size_lowerBound_of_sumsetDisperser`, including the extra
output-message bit. If k=o(n), alpha tends to one and the leading gate coefficient is

    (1+2c)/(1+c) = 1.1587603285... .

The asymptotic integration is separate from the finite theorem. This coefficient
counts actual gates of the stronger unbounded basis; it is not a superlinear lower
bound for a binary basis obtained by expanding the unbounded gates.

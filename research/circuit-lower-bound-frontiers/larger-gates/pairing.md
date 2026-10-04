# Pairing affine restrictions with newly constant gates

This is the affine ingredient of the stronger whole-basis argument. The circuit
restriction theorem is checked in
[`Geometry/Affine/Pairing.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Affine/Pairing.lean).
Its sumset-disperser consequence is exposed by
[`Geometry/Affine.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Geometry/Affine.lean).
The entropy argument needed for a coefficient above one is a separate ingredient.
We make no priority claim for the pairing argument or its combination with entropy.

The affine-elimination mechanism is classical; see
[Demenkov and Kulikov (2011)](https://eccc.weizmann.ac.il/report/2011/026/).
The present proof uses restrictions to construct a monochromatic affine flat, rather
than claiming a size-preserving substitution of an eliminated variable into a circuit.
This distinction matters for unbounded XOR gates: no replacement XOR gate is silently
granted for free in the size accounting below.

## Circuit model and statement

Use the existing finite acyclic `Program` model. An operation is either an affine
Boolean function of its ordered input slots, or a conjunction of signed input
literals, optionally complemented at the output. The latter representation includes
OR by De Morgan's law. Arbitrary binary Boolean operations have a one-gate normal
form of one of these two kinds. Fan-in, fanout, depth, repeated slots, and output
polarity are unrestricted. The designated output may be a primary input.

Let `g` be the number of actual gate occurrences. Let `h2` count conjunction-form
occurrences having at least two distinct direct primary-input variables among their
slots. Repeating the same primary variable does not count as two variables. Every
conjunction slot in this normalized model is a genuine literal; neutral or absorbing
constant slot maps in a more general aggregate representation must first be removed
or collapsed.

**Pairing theorem.** There is a nonempty monochromatic affine flat `S` in the original
Boolean input cube and a nonnegative integer `d` such that

```
2^d |S| = 2^n,
2d <= g + h2 + 2.
```

Thus its codimension is at most `floor((g+h2)/2)+1`. The formalization represents
affine flats as nonempty finite sets closed under ternary XOR. Translating such a
set by one of its points gives an XOR-closed set of the same size; this equivalence
is checked in `Affine/Coset.lean`. The representation does not restrict the flats
to coordinate subcubes.

## The invariant

Process the gates in their actual topological order. Maintain a nonempty affine
flat `S`, and let `d` be the number of independent affine restrictions made so far.
Every processed output is affine on `S`. Let `c` be the number of processed gate
outputs that are constant on `S`, and let `m` be the number of processed gates
counted by `h2`. Maintain

```
2^d |S| = 2^n,
2d <= c + m.
```

Initially the full cube works, with all four counts zero. Restricting a nonconstant
affine Boolean function to either value gives a nonempty affine flat of exactly
half the previous cardinality. Previously constant functions stay constant on every
later restriction.

If the next output is already affine, make no restriction. The constant-output count
cannot decrease and the multiple-primary count cannot decrease, so the invariant
persists. This includes every affine gate, including a wide XOR of previous affine
outputs.

Otherwise the next gate has conjunction form. There are two cases.

1. **A live internal predecessor exists.** Choose an internal input whose value is
   nonconstant on `S`. It is affine by the invariant. Fix it to the value falsifying
   its signed literal at the new conjunction. One independent affine equation makes
   both that previous gate and the current gate constant. The previous gate was not
   constant before this restriction, and the current gate is new. Consequently `c`
   increases by at least two while `d` increases by one.

2. **All internal predecessors are constant.** If the gate involves at most one
   distinct direct primary variable, its output is a unary Boolean function of that
   variable and hence affine, contrary to the case under consideration. Therefore
   this gate is counted by `h2`. Its nonconstant output also ensures some input slot
   is nonconstant. Fix that affine input to its literal's falsifying value. The current
   gate becomes constant, so `c` increases by at least one; `m` increases by one; and
   `d` increases by one.

This proves the invariant for every actual gate. No matching data structure is needed:
the constant-output count records that a charged gate can never become a live partner
again. Arbitrary fanout and repeated primary labels may make additional outputs
constant, which only strengthens the inequality.

At the end, `c <= g` and `m=h2`, so `2d <= g+h2`. The designated output is affine,
whether it is an internal gate or a primary input. If it is not already constant,
one further affine restriction makes it constant, giving the additional two in the
stated bound.

## Consequence for the existing hard family

Suppose `f` is a two-sided sumset disperser with threshold `K`. If a monochromatic
affine flat is `a+V`, then the two sources `a+V` and `V` have all their XOR sums inside
that flat. Consequently `|V|<K`. This finite obstruction and the eventual sumset
dispersion of the actual `sourceReductionHardFamily` are already checked in
[`Capacity/Polarity.lean`](../../../Complexitylib/Algebraic/LowerBound/Cutwidth/Aggregate/Capacity/Polarity.lean).

Put `k=ceil(log2 K)`. Combining `|S|<K<=2^k` with the exact cardinality identity gives
`n<d+k`. The pairing inequality therefore yields the checked finite bound

```
2n <= g + h2 + 2k.
```

In particular, circuits with no multiple-primary conjunctions need at least
`2n-2k` gates. More generally, this gives a precise tradeoff to combine with the
communication entropy cost of multiple-primary conjunctions. The affine theorem
alone does not establish the stronger coefficient for unrestricted placement.

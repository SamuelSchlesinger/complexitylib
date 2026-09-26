# Descriptive complexity expansion

This track connects logical definitions and structural reductions to
Complexitylib's existing machine classes. The immediate objective is to make a
new completeness proof consist mainly of a definability witness and a structural
reduction, with encoding and resource arguments supplied by shared theorems.

## Source and comparison

Pierre Senellart and Anton Gnatenko, [*Descriptive Complexity in Lean:
Completeness by First-Order Reductions*](https://arxiv.org/abs/2609.18261),
arXiv:2609.18261v1, September 16, 2026, develops a substantial library of logical
classes and complete problems. Its most relevant design choices are tagged tuple
interpretations, formula pullback, invariant decision problems, and explicit
encoding/decoding interfaces. See Sections 3--5 and the
[companion repository](https://github.com/PierreSenellart/descriptive-complexity).
The companion source is [Apache 2.0 licensed](https://github.com/PierreSenellart/descriptive-complexity/blob/master/LICENSE).
The paper is separately licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/),
as recorded on its arXiv page.

The paper defines classes through logics and proves bridges to structural machine
acceptance problems. Our `P`, `NP`, and other classes already have definitions over
binary languages and resource-bounded machines. Matching names are not a formal
equivalence: our capture statements must mention `queryLanguage`, malformed
encodings, and the actual resource predicates. This comparison is based on the
paper and repository documentation; it is not an independent audit of their
complete proof corpus.

The mathematical background remains Neil Immerman's [*Descriptive Complexity*](https://people.cs.umass.edu/~immerman/book/descriptiveComplexity.html)
(1999), especially interpretations and capture theorems, and Ronald Fagin's
*Generalized First-Order Spectra and Polynomial-Time Recognizable Sets* (1974).
The tagged pullback formalizes the full-product, source-constant-tuple case of
[Chapter 3](https://people.cs.umass.edu/~immerman/book/ch3.pdf), Definition 3.3,
Proposition 3.5, and Remark 3.6. Consult the author's
[corrections](https://people.cs.umass.edu/~immerman/book/corrections.html) when
selecting subsequent statements.
The circuit expansion follows the finite quantifier construction in
[Chapter 5](https://people.cs.umass.edu/~immerman/book/ch5.pdf), Section 5.4,
Theorem 5.22. We implement that construction for unordered FO with constants;
we do not yet assert the theorem's uniform class equivalences.
The SO closure layer implements the capture-avoiding existential-prefix
manipulations of [Chapter 7](https://people.cs.umass.edu/~immerman/book/ch7.pdf),
Section 7.1. The matrix evaluator implements the verification step of Proposition
7.6: guessed relation tables supply the witnesses for an FO matrix. The binary
certificate format, its exact length, and sound and complete checking are also
formalized. First-order sentence evaluation and SO certificate checking now have
polynomial-time machine proofs. The certificate checker and its witness bound
prove the upper direction of Fagin's theorem against the library's existing `NP`.
The two-copy graph construction and bipartite sentence below are credited to the
worked examples in Senellart--Gnatenko, Sections 3.2 and 2.1. Their implementations
here are written against our syntax; no companion-library source was vendored.

## Present boundary

Our structures use `Fin n`, require `n ≥ 2`, and allow relation and constant
symbols. The syntax uses de Bruijn indices and has no built-in order atoms.
It also has no built-in `BIT`, `ADD`, or `MUL` predicates. The canonical order
helpers on `Fin n` and the arithmetic used to access binary encodings are outside
the object logic. No theorem `FO[BIT] = FO[ADD, MUL]` is formalized here.
`BooleanQuery.IsOrderIndependent` means invariance under structure isomorphism;
it is distinct from independence of an auxiliary order in an ordered logic.
The companion library instead uses Mathlib model theory and quantifies its
reduction correctness over finite nonempty structures. An interoperability layer
must account for these differences explicitly.

The original `FOInterpretation` preserves the universe and maps target constants
to source constants. Its `FOReduces` relation composes and transports FO truth.
`FOProjReduces` is a legacy name for its quantifier-free restriction; it is not
Immerman's exact first-order projection normal form. The existing `Embedding`
already preserves and reflects relations; `InjectiveHom` is the weaker notion.

This change adds:

- SO formula transport with arbitrary free element and relation environments,
  preserving both FO matrices and existential SO prefixes, and SO reduction
  closure (`SecondOrder/Reduction.lean`).
- `ExistSODefinable`, FO inclusion, invariance, and reduction closure
  (`SecondOrder/Definable.lean`). The downstream machine theorem now puts the
  induced binary languages in `NP`.
- Arity-preserving relation renaming, lifting through binders, and environment
  pullback (`SecondOrder/Renaming.lean`). Identity and composition hold exactly
  on syntax. Satisfaction is preserved for arbitrary element and relation
  environments; size, FO matrices, and existential SO prefixes are preserved.
- Existential-prefix conjunction and disjunction (`SecondOrder/Connectives.lean`).
  Leading relation quantifiers move outward while the other operand is weakened
  to prevent capture. The operations have their ordinary semantics on all open
  formulas and preserve existential SO form. Each result has size exactly
  `φ.size + ψ.size + 1`. They prove `ExistSODefinable.inter` and `.union` with
  actual existential-prefix witnesses.
- Boolean relation environments and a computable evaluator requiring an FO-matrix
  certificate (`SecondOrder/ModelChecking.lean`). Boolean tables represent exactly
  the semantic relation environments. Matrix evaluation agrees with SO satisfaction
  and with the existing FO evaluator on embedded formulas. Existential and universal
  matrix truth can use Boolean relation assignments, including nullary relations
  and empty contexts.
- Canonical binary relation certificates (`SecondOrder/Encoding.lean`), listing
  the context's truth tables with no headers or padding. Encoding and decoding
  are inverse, the decoder rejects exactly wrong lengths, and every string of
  length `∑ n ^ arity` represents one environment. Nullary relations use one bit;
  empty contexts use none. This exact length is a fixed polynomial in `n`.
- An executable certificate checker for every existential-SO formula
  (`SecondOrder/Certificate.lean`). It consumes prefix tables from outermost to
  innermost, then checks the matrix with no trailing bits. Acceptance is sound
  and complete for satisfaction under arbitrary free element and Boolean
  relation environments. The encoded sentence checker characterizes the entire
  query language, rejects malformed structures, and has a polynomial certificate
  bound in encoded input length. `ExistSODefinable.exists_bounded_certificate`
  packages the result for definable queries. `SecondOrder/PolynomialTime.lean`
  supplies the machine running-time bound. For bipartiteness, one bit per vertex
  gives exactly the existing Boolean-coloring check.
- Tagged full-product interpretation semantics, exact size `tags * n ^ dim`,
  coordinatewise isomorphism transport, and compatibility with the old
  dimension-one API (`Interpretation.lean` and `Interpretation/Defs.lean`). Both
  counts are positive; constants are tagged tuples of source constants.
- Finite connectives, quantifier blocks, and their semantics
  (`FirstOrder/Blocks.lean`), including empty families and blocks.
- Tagged formula pullback with arbitrary free-variable coordinate terms, an
  open-formula satisfaction theorem, sentence transport, and preservation of FO
  definability (`Interpretation/Pullback.lean`). Equality checks both tags and
  coordinates; quantifiers range over every tag and coordinate tuple.
- Tagged composition with parameters `t₂ * t₁ ^ d₂` and `d₂ * d₁`, proved
  isomorphic to successive application, plus the identity isomorphism and
  semantic composition of sentence translations (`Interpretation/Composition.lean`).
- Invariant `DecisionProblem`s, concrete `TaggedFOReduction` witnesses, and a
  reducibility preorder with complement closure, an embedding of the original
  reduction relation, and downward closure of FO definability (`Problem.lean`
  and `TaggedReduction.lean`). The preorder is available explicitly without
  installing a global order instance on decision problems.
- A bipartite sentence proved equivalent to Boolean graph coloring, with no
  symmetry or loop-freeness assumption. Edgeless graphs satisfy the query;
  self-loops prevent it. A two-copy graph interpretation has exact relation
  semantics and a proved bipartition. Taking any positive number of disjoint
  copies preserves and reflects bipartiteness and supplies a tagged reduction
  with a larger universe when the copy count exceeds one (`Problems/`). The
  executable `checkBipartition` uses matrix evaluation and is proved to accept
  exactly the proper Boolean colorings.
- Finite quantifier expansion into the existing `AC0Formula` representation,
  with semantic correctness for open formulas and varying constant values,
  exact polynomial tree size, and depth at most the source formula's size plus
  one (`Circuit.lean`). Relation and equality atoms select through one-hot
  constant blocks. A fixed numbering of table sites represents every structure;
  its input width is `∑ n ^ arity + numConsts * n`. The numbering is chosen
  noncomputably, while compilation from a supplied layout is computable.
- Circuit realizations of arbitrary `AC0Formula` trees at positive input width,
  with exactly the tree's size and depth at most one greater
  (`Circuits/AC0/Compilation.lean`). Parallel packing preserves a common depth
  bound and sums sizes exactly. Consequently, the FO expansion has an actual
  `Circuit Basis.unboundedAndOr` realization of size `Pφ(n)` and depth at most
  `φ.size + 2`, computing the expansion on every input. Satisfaction follows
  on inputs satisfying `StructureInput.Represents`.
- Computable bit positions in the existing encoder, with exact lookup and a
  strictly increasing encoded-length function (`Encoding/Positions.lean`).
  The table-site enumeration has no duplicates; correct header and table bits
  characterize the complete encoding at its prescribed length.
  `Circuit/Encoding.lean` supplies the corresponding computable input layout,
  proves correctness on `encodeStruct`, and specializes circuit realization to
  that layout. The unary prefix makes this input width positive even for the
  empty vocabulary.
- A computable decoder with exact round trips, encoding injectivity, and
  rejection precisely outside the encoder's image (`Encoding/Decoding.lean`).
  It checks the unary size and total length, reads a candidate, and validates
  it by re-encoding. Query-language membership is equivalent to successful
  decoding followed by the query. `Sentence.evalEncoded` recognizes the full
  induced binary language, including malformed-input rejection
  (`ModelChecking/Encoded.lean`). Its polynomial-time machine bound is supplied
  by the arithmetic evaluation layer below.
- An encoding validator of depth at most three and exact size
  `n + 4 + numConsts * (1 + n * (1 + n))`, proved to accept precisely the
  encoder's image at the chosen length (`Circuit/Validity.lean`). Combining
  it with a sentence expansion gives a circuit deciding the full induced
  language at that length, including malformed inputs.
- `FODefinable.queryFamily_mem_AC0`, connecting FO definability to the existing
  nonuniform `AC0` class (`AC0.lean`). The family covers every binary input
  length; lengths outside the encoder's image and the empty input are rejected.
  If `Vφ(X) = 1 + X + 4 + numConsts * (1 + X * (1 + X)) + Pφ(X)`,
  circuits at positive length `N` have size at most `Vφ(N)` and depth at most
  `φ.size + 5`. `queryFamily` is the characteristic family of `queryLanguage`.
- Arithmetic tuple indices and relation/constant bit addresses
  (`Encoding/Arithmetic.lean`). Their exact equality with `encodingPosition`
  connects arithmetic access to the existing encoder, including nullary
  relations and arbitrary constant blocks.
- Machine-level polynomial-time bit reads, unary-prefix parsing, address
  computations, and structure/certificate lengths (`Classes/P/StringAccess.lean`
  and `Encoding/PolynomialTime.lean`). Missing bits read as false, and parsing
  remains total on an unterminated unary prefix.
- `validEncodings_mem_P` and a polynomial-time predicate for successful decoding
  (`Encoding/Validity.lean`). Explicit length, header, and one-hot conditions
  characterize the encoder's image, and bounded quantifiers implement the tests
  in the existing deterministic machine class. Relation tables need no validity
  restrictions.
- Arithmetic first-order evaluation and its polynomial-time machine proof
  (`ModelChecking/PolynomialTime.lean`). Constants use bounded search of their
  one-hot blocks, and quantifiers enumerate the parsed universe. Correctness
  holds for open formulas on encoded structures; polynomial time holds whenever
  the input, universe size, and free-variable values are polynomial-time inputs.
  Combining this with encoding validation proves
  `FODefinable.queryLanguage_mem_P`, including malformed-input rejection.
  `Sentence.evalEncoded_mem_FP` gives the existing evaluator's one-bit verdict
  an `FP` implementation. Each formula is fixed; this is a data-complexity result,
  with no assertion of polynomial combined complexity or logarithmic space.
- Polynomial-time existential-SO verification and `∃SO ⊆ NP`
  (`SecondOrder/PolynomialTime.lean`). Arithmetic matrix evaluation reads
  relation-witness tables by tuple index. Prefix checking consumes their blocks
  by polynomial-time slicing, rejecting short tables and trailing data. Both
  evaluators agree exactly with the existing checkers on structure encodings,
  including arbitrary free element and relation environments. Encoding validation
  gives `SOSentence.checkEncoded_mem_FP` for the existing complete binary checker.
  Its polynomial witness bound and the proved guess-and-verify NTM yield
  `ExistSODefinable.queryLanguage_mem_NP`. This is Fagin's upper direction for
  fixed formulas and vocabularies, including malformed-input rejection.
- Numeric tuple decoding and polynomial-time truth-table generation for fixed
  open formulas (`Encoding/Arithmetic.lean`, `ModelChecking/PolynomialTime.lean`).
  Scanning the `n ^ k` tuple indices gives the encoder's exact assignment order,
  and the generated table agrees with `encodeRelC` of the semantic evaluator.
- The universe-preserving encoded reduction bridge (`Reduction/Encoding.lean`).
  `FOInterpretation.applyDec` agrees exactly with the original structure map;
  `mapEncoding` belongs to `FP`, re-encodes the interpreted structure on valid
  inputs, and sends malformed inputs to `[]`. The full output length, including
  relation and constant blocks, is bounded by the target encoding polynomial
  in input length. `FOReduces.mapReducesPoly` yields actual binary many-one
  reductions and transports machine `P` and `NP` membership backward.
  `ExistSODefinable.npComplete_of_foReduces` packages the completeness method:
  an ESO target is NP-complete when an NP-hard encoded query FO-reduces to it.
- Exact encoded semantics for tagged interpretations (`TaggedReduction/Encoding.lean`).
  Arithmetic tag and coordinate extraction agrees with the existing finite
  equivalences; generating the relation tables and packed constants gives exactly
  the interpreted structure's encoding. Its full length is
  `encodingLength W (tags * n ^ dim)`. The decoder-based map rejects malformed
  input. Its polynomial-time machine bound remains to be proved.

The tagged encoding machine bound, tagged SO pullback, and domain-restricted
interpretations remain open. In
particular, the current SO reduction-closure theorem still concerns the original
universe-preserving interpretations. The circuit result proves the nonuniform
FO-to-AC0 inclusion on the existing structure encoding. The ordered uniform
capture theorem and the NP-to-ESO tableau construction remain open.
The graph constructions are semantic examples, not completeness or hardness results.

## Sequence of independently checkable expansions

1. **Extend the completed interpretation core.** Full-product tagged FO
   pullback, composition, and the invariant reduction preorder now compile,
   including arbitrary arities, constants, and open formulas. Add definable
   subuniverses with explicit proofs of minimum output cardinality; handle
   definable constants and quotients as separate interfaces. State exact
   first-order projections using mutually exclusive numeric cases and at most
   one input literal per case. Retain the legacy quantifier-free API without
   claiming it has this more restrictive syntax.
2. **Make SO fragments practical.** Relation-context renaming and existential
   prefix merging are complete, including semantic and exact-size theorems.
   Existential SO queries are closed under intersection and union. Boolean
   relation environments, the verified FO-matrix evaluator, exact binary
   certificate encoding, and the sound and complete existential-SO checker are
   complete. Certificate length is polynomially bounded in encoded input length,
   the checker is polynomial-time, and its connection to the NP witness interface
   proves `∃SO ⊆ NP`.
   Add universal SO and complement duality, then
   alternation blocks. For tagged pullback, replace an arity-`a` relation variable
   by `tags ^ a` variables of arity `a * dim`; prove an equivalence of relation
   assignments before the satisfaction theorem. Build fixed-`k` colorability
   and SAT membership witnesses against ordinary semantic predicates.
3. **Close the machine encoding bridge.** `decodeStruct`, exact round trips,
   injectivity, malformed-input rejection, and encoded model-checking
   correctness are complete for the unary-cardinality, truth-table, one-hot
   format. Arithmetic addresses match that format exactly; polynomial-time
   bit access, cardinality parsing, size computation, and complete encoding
   validation are now proved. Fixed-formula evaluation is in `FP`, and
   `FODefinable Q → queryLanguage Q ∈ P` is proved against the existing machine
   definitions. Universe-preserving interpretations now give binary
   polynomial-time reductions with exact output tables, a full encoded-length
   bound, and malformed-input rejection. Tagged tuple packing and exact output
   tables are now proved too. Next give the tagged generator an `FP` implementation,
   using fixed finite formula selection and polynomial-time coordinate extraction.
4. **Extend the completed circuit connection.** The compilation to
   `AC0Formula` now has correctness, exact polynomial size, and constant-depth
   proofs, and these trees have circuit realizations of exactly the same size
   with at most one extra depth layer. The computable layout now matches the
   existing bit-string encoding. Encoding validation and the length-zero case
   complete the `CircuitFamily` construction and prove nonuniform `FO ⊆ AC0`.
   Next use the bridge with circuit lower bounds to obtain inexpressibility
   results. Develop the ordered `FO[BIT]` capture of uniform `AC0` separately;
   its uniformity predicate and ordered syntax are not defined yet.
   First add canonical numerical-predicate extensions for `<`, `BIT`, `ADD`,
   and `MUL`. Interpret addition and multiplication as ternary graphs of natural
   arithmetic restricted to the finite universe, with no modular wraparound.
   Prove explicit formula translations for `FO[BIT] = FO[ADD, MUL]`, uniformly
   in the universe size. The mathematical equivalence, including definability
   of order from `BIT`, is stated in Schweikardt and Schwentick,
   [*A note on the expressive power of linear orders*, Theorem 1.1](https://lmcs.episciences.org/1008/pdf).
5. **Complete Fagin against our NP.** The upper direction is proved:
   `ExistSODefinable Q → queryLanguage Q ∈ NP`. Its sound and complete binary
   checker has a polynomial-time machine implementation and certificates of
   exactly `∑ n ^ arity` bits. For the converse, encode a machine computation
   tableau indexed by tuples, checking the
   initial encoding, local transitions and acceptance. Reuse existing tableau
   correctness results where their statements fit. State the full equivalence
   only after both directions compile; then transfer structural completeness to
   machine `NPComplete` via the encoding bridge.
6. **Grow a catalog and the logics together.** Use SAT/3SAT, fixed-color graph
   coloring, independent set and vertex cover to test the reduction API. Add
   ordered vocabulary extensions, tuple transitive closure, and monotone least
   fixed points with bounded finite iteration. Prioritize reachability and
   circuit value as consumers before NL and P capture. Partial fixed points and
   SO alternation can then connect to PSPACE and the existing PH. Keep exact
   projections and ordered/unordered hypotheses explicit throughout.
7. **Add inexpressibility tools.** Ehrenfeucht--Fraïssé and pebble games should
   prove bounded-rank indistinguishability before any headline lower bound. Use
   an elementary concrete pair family first, then parity or reachability.

The mathematical status and dependencies live in the descriptive-complexity
blueprint chapter. Each expansion should update its nodes, credit adapted
sources, and pass all six builds plus style, environment, axiom, and blueprint
checks. Prefer a small correspondence layer to importing a second complete
complexity hierarchy. Evaluate a Mathlib syntax bridge before duplicating large
model-theoretic constructions such as the game infrastructure.

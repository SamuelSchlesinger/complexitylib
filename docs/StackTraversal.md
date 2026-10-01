# Shared polynomial-space traversal: implementation map

## Completed encoding layer

`Encoding.Stack` supplies `StackEncoding.encode`, the exact top-first,
right-nested `pair` encoding. It imports only the neutral pairing module.
Projection, emptiness, exact fold-length, and uniform frame-length bounds are
shared. Empty frame encodings are allowed: their pair separator distinguishes
them from an empty stack. Raw push/top/rest remain `pair`/`pairFst`/`pairSnd`,
with their existing FP rules in `Classes.P.Pairing` and unchanged behavior on
malformed inputs.

Two consumers use this encoder directly:

- `SavitchFrame.encStack` specializes it to already-encoded frames with `id`.
  `SavitchSim.encStack_length_le` reuses the common bound.
- `IPEnc.IPM.encStk` specializes it to `IPM.encFrm`.
  `IPM.encStk_length_le` reuses the same bound.

The old names, nil/cons reduction rules, exact bitstrings, frame and state
layouts, and quantitative state bounds are retained. `StackEncodingCheck.lean`
checks the public API and compatibility using kernel-checked examples in CI.
This extraction does not provide a generic recursive traversal theorem.

## Remaining traversal obligations

- **Control and semantics:** preserve Savitch's two-phase, short-circuit
  midpoint search and IP's nested sum/max traversal. IP leaves themselves
  enumerate exponentially many coin strings; they are not one FP leaf call.
- **Depth and live state:** Savitch's `StkSize` bounds depth by `Lmax + 1`;
  IP's `StkDepth` bounds it by `D`. IP additionally needs `BodyOk`, `SizeOk`,
  and `EncOk` for transcript bodies, counters, accumulators, and returns.
- **Counts:** IP sums, maxima, and returned counts have width `t + 1`.
  `Protocol.treeVal_le_two_pow` supplies the semantic coin-space bound; it
  is not true for arbitrary `IPM.Params.ok`.
- **Returns:** Savitch encodes `Option Bool`; IP uses the empty word for
  absence and excludes empty valid returns via `EncOk.retLen`. Do not assume
  IP's return encoding is injective on all `Option (List Bool)`.
- **Termination:** `Sav.run_frame` and `IPM.run_frame` establish different
  local progress measures and `runBound` recurrences. A shared engine must
  prove these obligations with meaningful instances for both algorithms.
- **FP realization and all-prefix bounds:** retain the abstract/encoded step
  correspondence, initialization, every intermediate state's polynomial
  length, and the exponential stopping bound needed by `SpaceIter`.
- **Completion:** `done` is a completion pulse, followed one step later by
  the verdict. A rejecting verdict can set it back to false. It is not an
  absorbing halted-state flag.

`Space.BitstringFold` remains the depth-one ordered fold. It does not replace
these recursive-stack obligations. No PH, PP, or TQBF migration is part of
the encoding-only slice.

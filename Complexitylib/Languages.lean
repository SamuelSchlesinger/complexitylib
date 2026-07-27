/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Languages.Trivial
public import Complexitylib.Languages.FirstCell
public import Complexitylib.Languages.LengthParity
public import Complexitylib.Languages.AnBn
public import Complexitylib.Languages.ZeroPrefix
public import Complexitylib.Languages.Balanced
public import Complexitylib.Languages.AllSymbol
public import Complexitylib.Languages.Contains
public import Complexitylib.Languages.LengthDivBy
public import Complexitylib.Languages.LastBit
public import Complexitylib.Languages.Palindromes

/-!
# Concrete languages and their complexity — aggregation

Each file under `Complexitylib.Languages` defines a family of concrete
languages together with complexity-class memberships. They serve as
non-emptiness witnesses for the classes in `Complexitylib.Classes` and as
worked examples of building TMs from reusable building blocks.

## Submodules

- `Trivial`      — `∅` and `Set.univ`, decided in `O(1)` by `writeTM`.
- `FirstCell`    — languages determined by the first input bit:
                   `{[]}`, `firstBitOne`, `firstBitZero`, `nonempty`, and
                   their Boolean combinations.
- `LengthParity` — `evenLength`, `oddLength` — the first genuinely linear-time
                   examples, proved by induction on the input.
- `AnBn`         — `{0ⁿ 1ⁿ : n ≥ 0}` — the first non-regular example,
                   decided in linear time by a push-down TM that uses its
                   work tape as a unary counter.
- `ZeroPrefix`   — `{0ⁿ 1ᵐ : n ≥ m}` — an `AnBn` variant that accepts
                   strings with at least as many leading zeros as trailing
                   ones, decided by the same push-down construction.
- `Balanced`     — strings with equal numbers of `false`s and `true`s —
                   generalizes `anbn` to arbitrary interleavings, decided
                   in linear time by a push-down TM whose control state
                   records the sign of the count difference.
- `AllSymbol`    — `allZeros`, `allOnes` — strings consisting entirely of
                   a single bit, decided by the `scannerTM` combinator.
- `Contains`     — `containsZero`, `containsOne` — strings containing at
                   least one copy of a given bit, also decided via
                   `scannerTM`.
- `LengthDivBy`  — `lengthDivBy k` — strings whose length is divisible
                   by `k`, with `ZMod k` counter as the scan state.
- `LastBit`      — `lastBitOne`, `lastBitZero` — strings whose final bit
                   equals a target, with `Option Bool` scan state.
- `Palindromes`  — strings equal to their reverse, decided in linear time
                   by a 1-work-tape TM that copies the input then compares
                   forward against backward.
-/

@[expose] public section

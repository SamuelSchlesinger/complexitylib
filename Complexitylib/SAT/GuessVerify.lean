/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Samuel’s dot
-/

module
public import Complexitylib.Classes.NP.Internal.GuessVerify

/-!
# Compatibility API for the concrete SAT guess-and-verify machine

Import this module for the legacy `satGuessVerifyNTM` machine and its exact
`satGuessVerifyTime` bounds, including `guessVerify_decidesInTime` and the
`SAT.linearGuessVerify_*` theorems. These remain statements about the original
concrete machine, not about the generic finite-verifier compiler.

For new NP membership proofs, use `Complexitylib.Classes.NP.Verifier` instead.
It exposes the language-independent verifier route without importing SAT.
-/

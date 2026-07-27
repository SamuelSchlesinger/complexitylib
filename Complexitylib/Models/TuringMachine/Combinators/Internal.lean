/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Combinators.Internal.Complement
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Seq
public import Complexitylib.Models.TuringMachine.Combinators.Internal.If
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Loop
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Union

/-!
# Combinator proof internals (aggregation)

This file aggregates the proof-internal modules for the Turing machine
combinators (`Complement`, `Seq`, `If`, `Loop`, `Retarget`, `Scanner`,
`Generic`, `Union`). It contains no definitions of its own; it exists so
that the surface module `Combinators.lean` can pull in all combinator
proof internals with a single import.
-/

@[expose] public section

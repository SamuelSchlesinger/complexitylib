/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.DataEncode
public import Complexitylib.Classes.Containments.Internal.PVerdict
public import Complexitylib.Classes.PCP.Internal.BinCounter
public import Complexitylib.Classes.P.Range
public import Complexitylib.Classes.P.Range.Internal

/-!
# Writing out a list of encoded entries

The list encoder `listEncFn` and the loop behind it moved to
`Complexitylib.Classes.P.Range`, where `listEncFn_mem_FP` needs no bound on the
loop's state, and to its internals `Complexitylib.Classes.P.Range.Internal`,
which keep `listStep`, `entryCat`, `listStep_iterate`, `listEncFn_eq` and
`bitstringEncode_of_entries` under their old names. Writing and reading encoded
lists and numbers (the former `NatEncode`, `PositionsFP` and `PosScan`) moved to
`Complexitylib.Classes.P.DataEncode`. This module re-exports all three, together
with the modules those used to bring in, so that its importers see the same
names as before.
-/

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Action
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.EmptyReject
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.PositiveReject
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Attempt
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Reject
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Loop
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.LoopReject
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.PositiveLoopReject
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Family
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Evaluator
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Hoare
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Pure
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Stage
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Tape

/-!
# Streaming evaluator proof internals

Internal aggregation module for the evaluator's action, exact execution,
successful and rejecting gate loops, total tagged-family semantics, quadratic
core and end-to-end contracts, and tape-cursor proof seams.
-/

@[expose] public section

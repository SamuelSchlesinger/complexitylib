/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.Space.Iterate.Internal
public import Complexitylib.Classes.Space.Iterate

/-!
# Compatibility import for polynomial-space iteration

The public theorem `Complexity.SpaceIter.mem_PSPACE_of_iterate` now lives in
`Complexitylib.Classes.Space.Iterate`. This module re-exports that surface and
the existing machine construction so earlier imports retain every declaration.
New consumers of the iteration theorem should import the surface module.
-/

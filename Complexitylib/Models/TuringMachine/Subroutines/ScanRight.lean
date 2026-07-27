/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.Internal.ScanRight

/-!
# Frame-preserving right scan

Public compositional contract for `TM.scanRightTM`. A completed binary string
is converted into its appendable tape shape by moving the target head to the
first blank. Every stable tape outside that target is preserved exactly.

## Main result

- `TM.scanRightTM_reachesIn_frame` — exact linear-time endpoint with a full frame.
- `TM.scanRightTM_hoareTime_frame` — bounded compositional form of that endpoint.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Starting at cell one of a completed binary string, `scanRightTM` reaches
the append blank in exactly `|bits| + 1` transitions. The input, output, and
unrelated work tapes are preserved exactly. -/
theorem scanRightTM_reachesIn_frame {n : ℕ}
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hstring : (work₀ idx).HasBinaryString bits)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (scanRightTM idx).reachesIn (bits.length + 1)
        { state := (scanRightTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (scanRightTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).cells = (work₀ idx).cells ∧
      (c'.work idx).HasBinaryPrefix bits ∧
      c'.output = out₀ :=
  scanRightTM_reachesIn_frame_internal
    idx bits inp₀ work₀ out₀ hstring hinp hother hout

/-- Bounded compositional form of `scanRightTM_reachesIn_frame`. The
off-start frame hypotheses are the minimal conditions needed to keep the
structurally mandatory idle moves from changing unrelated head positions. -/
theorem scanRightTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hstring : (work₀ idx).HasBinaryString bits)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (scanRightTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).HasBinaryPrefix bits ∧
        out = out₀)
      (bits.length + 1) := by
  exact scanRightTM_hoareTime_frame_internal
    idx bits inp₀ work₀ out₀ hstring hinp hother hout

end TM

end Complexity

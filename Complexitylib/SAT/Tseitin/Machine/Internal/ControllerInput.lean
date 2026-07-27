/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerRead
public import Complexitylib.SAT.Tseitin.Machine.Internal.RuntimeBounds

/-!
# Input framing for the Tseitin streaming controller

The streaming controller never rewinds while reading a valid token stream.
`framedTokenInput pre rest` fixes the original cells for `pre ++ rest` and
places the head immediately after the encoded prefix. These lemmas identify
the next two cells with the next token and normalize the frame after those two
cells have been consumed.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- Original token-stream cells with the head immediately after `pre`. -/
def framedTokenInput (pre rest : List EncToken) : Tape :=
  { head := (encodeTokens pre).length + 1
    cells := (Tape.init ((encodeTokens (pre ++ rest)).map Γ.ofBool)).cells }

/-- Every framed token input is parked. -/
theorem framedTokenInput_parked (pre rest : List EncToken) :
    TM.Parked (framedTokenInput pre rest) := by
  refine ⟨by simp [framedTokenInput], fun j hj => ?_⟩
  simp only [framedTokenInput]
  exact Tape.init_ofBool_cells_ne_start (encodeTokens (pre ++ rest)) j hj

/-- The next two cells of a nonempty remainder are exactly its first token. -/
theorem framedTokenInput_tokenAt (pre rest : List EncToken) (tok : EncToken) :
    InputTokenAt (framedTokenInput pre (tok :: rest)) tok := by
  constructor
  · change (Tape.init ((encodeTokens (pre ++ tok :: rest)).map Γ.ofBool)).cells
        ((encodeTokens pre).length + 1) = Γ.ofBool (tokenFirstBit tok)
    have hlt : (encodeTokens pre).length <
        (encodeTokens (pre ++ tok :: rest)).length := by
      simp [encodeTokens_length_internal]
    rw [Tape.init_ofBool_cells_lt _ _ hlt]
    simp [token_encode_eq_bits]
  · change (Tape.init ((encodeTokens (pre ++ tok :: rest)).map Γ.ofBool)).cells
        ((encodeTokens pre).length + 1 + 1) = Γ.ofBool (tokenSecondBit tok)
    have hlt : (encodeTokens pre).length + 1 <
        (encodeTokens (pre ++ tok :: rest)).length := by
      simp [encodeTokens_length_internal]
    rw [Tape.init_ofBool_cells_lt _ _ hlt]
    simp [token_encode_eq_bits]

/-- Consuming the next token advances the framing prefix by that token. -/
theorem controllerScheduledCfg_framedTokenInput
    (mode : StreamMode) (pre rest : List EncToken) (tok : EncToken)
    {Q : Type} (c : Cfg workTapeCount Q)
    (hinput : c.input = framedTokenInput pre (tok :: rest)) :
    (controllerScheduledCfg mode tok c).input =
      framedTokenInput (pre ++ [tok]) rest := by
  apply Tape.ext
  · rw [controllerScheduledCfg_input_head, hinput]
    simp [framedTokenInput, encodeTokens_length_internal]
  · rw [controllerScheduledCfg_input_cells, hinput]
    simp [framedTokenInput, List.append_assoc]

/-- With no tokens remaining, the framed input head reads the first trailing
blank. -/
theorem framedTokenInput_nil_read (pre : List EncToken) :
    (framedTokenInput pre []).read = Γ.blank := by
  rw [Tape.read]
  have hge : (encodeTokens pre).length ≥ (encodeTokens pre).length := le_rfl
  simpa [framedTokenInput] using
    Tape.init_ofBool_cells_ge (encodeTokens pre) (encodeTokens pre).length hge

/-- The empty-prefix frame is the input tape handed to the controller after
rewind. -/
theorem framedTokenInput_nil_prefix (toks : List EncToken) :
    framedTokenInput [] toks =
      ⟨1, (Tape.init ((encodeTokens toks).map Γ.ofBool)).cells⟩ := by
  rfl

end Machine

end ThreeSAT

end SAT

end Complexity

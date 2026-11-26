module

public import Veil

/-! # Assignment: the Alternating Bit Protocol

This file is a skeleton. The task is described in `README.md` in this
directory; "Part N" below refers to the parts of Section 3 of that file.

The state and the outlines of the actions are given, after the TLA+
specification the README points to. You may change them, as long as you can
say why.

Where to find the protocol:
- TLA+ specification, from Lamport's *Specifying Systems*, Chapter 14:
  https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/TLC/AlternatingBit.tla
  (the protocol), `ABCorrectness.tla` (what it should achieve) and
  `MCAlternatingBit.tla` (the model-checking setup) in the same directory.
- The book: https://lamport.azurewebsites.net/tla/book.html
- The original paper: Bartlett, Scantlebury, Wilkinson. A note on reliable
  full-duplex transmission over half-duplex links. CACM 12(5), 1969.
  https://doi.org/10.1145/362946.362970
- https://en.wikipedia.org/wiki/Alternating_bit_protocol

Check the file from the repository root with

    lake lean Examples/Assignment/AlternatingBit.lean

or open it in VS Code with the Lean 4 extension and read the results in the InfoView.
-/

veil module AlternatingBit

-- Makes the temporal operators (`□`, `◇`, `𝒲ℱ`, ...) available.
open Lentil

-- Typing the temporal symbols in VS Code (Lean 4 extension): type the
-- abbreviation, then a space or Tab.
--   □  \square      ◇  \Diamond     ↝  \leadsto
--   ⌜  \ulcorner    ⌝  \urcorner    ⟨ ⟩  \<  \>
--   𝒲ℱ  \McW\McF   𝒮ℱ  \McS\McF

/-! ## Part 1 (the model): types, constants and state -/

-- The values handed to the sender.
type data

-- What travels on the data link: a value tagged with one bit.
@[veil_decl] structure Frame (data : Type) where
  bit : Bool
  val : data

immutable individual cap : Nat        -- capacity of each link

individual msgQ : List (Frame data)   -- data link, head arrives first
individual ackQ : List Bool           -- ack link, head arrives first
individual sBit : Bool                -- bit of the last value the sender sent
individual sAck : Bool                -- last acknowledgement bit the sender received
individual rBit : Bool                -- bit of the last frame the receiver received
individual sent : data                -- last value sent
individual rcvd : data                -- last value received

#gen_state

/-! ## Part 1: initial state -/

after_init {
  -- TODO: the remaining fields
  msgQ := []
  ackQ := []
}

/-! ## Part 1: actions

Each action is atomic. Fill in the bodies: when is the step possible
(`require`), and what does it change? -/

/-! ### Sender -/

-- Send a new value `d`, once the previous one has been acknowledged.
action sndNewValue (d : data) {
  -- TODO
  require false
}

-- Retransmit the current value while it is unacknowledged.
action reSndMsg {
  -- TODO
  require false
}

-- Take an acknowledgement off the ack link.
action rcvAck {
  -- TODO
  require false
}

/-! ### Receiver -/

-- Take a frame off the data link.
action rcvMsg {
  -- TODO
  require false
}

-- Put an acknowledgement on the ack link.
action sndAck {
  -- TODO
  require false
}

/-! ### Links -/

-- The data link loses a frame.
action loseMsg {
  -- TODO
  require false
}

-- The ack link loses an acknowledgement.
action loseAck {
  -- TODO
  require false
}

/-! ## Part 2 (safety)

State what must hold in every reachable state. `safety` clauses are checked
by `#model_check`; give each one a name. -/

-- TODO: safety [name] ...

/-! ## Part 3 (reachability) and Part 4 (liveness)

Temporal properties must be declared before `#gen_spec`. A reachability probe
is a property you expect to FAIL, whose counterexample is the witness you are
after. -/

-- TODO: temporal [name] ...

#gen_spec

/-! ## Checks

Keep the instances small: every command here is re-run whenever the file is
elaborated. A check that is expected to report a violation must be preceded by
`set_option veil.violationIsError false in`, on the line directly above it. -/

-- TODO: #model_check { data := Fin 2 } { cap := ... }

-- TODO: set_option veil.violationIsError false in
--       #temporal_check [some_probe] { data := Fin 2 } { cap := ... }

-- TODO: #temporal_check [some_liveness_property] { data := Fin 2 } { cap := ... }

end AlternatingBit

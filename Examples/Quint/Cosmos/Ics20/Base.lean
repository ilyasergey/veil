module

public import Veil.Quint

/-!
# Quint example `cosmos/ics20/base.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/cosmos/ics20/base.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module base {
  --/ A hop is a step taken by a token sent from one chain to another. In this
  --/ spec, we only care about one element of the hop (sometimes the source
  --/ chain, sometimes the destination chain). A `HopElement` is a representation
  --/ of either the source or the destination chain of a hop.
  type HopElement = {
    port: str,
    channel: str,
  }

  --/ A denomination trace is a representation of the original denomination
  --/ (also: base denomination) and all the hops it has done to get where it is.
  --/ For every token transfer, ICS-020 either adds or removes one hop from the
  --/ list. In the implementation, a `DenomTrace` is represented as a string of
  --/ the form
  --/ `{ics20Port_n}/{ics20Channel_n}/.../{ics20Port_1}/{ics20Channel_1}/{baseDenom}`,
  --/ where `ics20Port_i` and `ics20Channel_i` are the destination port and
  --/ channel of the i-th hop. A token transfer then means adding or dropping a
  --/ prefix.
  type DenomTrace = {
    path: List[HopElement],
    baseDenom: str,
  }

  type UINT256 = int
  type Address = str

  type Channel = str
  --/ Map from channel name in a chain to its counterparty on other chain
  type ChannelCounterparties = Channel -> Channel
  --/ Map from a chain to other chains and the channel used to send packets from
  --/ the first chain to the second
  type ChannelTopology = str -> str -> Channel

  pure def toDenom(baseDenom: str): DenomTrace = {
    { baseDenom: baseDenom, path: [] }
  }

  --/ Test whether a set is non-empty
  --/
  --/ - @param __set a map to query
  --/ - @returns true if and only if __set is non-empty (.size() != 0)
  pure def setNonEmpty(__set: Set[a]): bool = {
    __set.size() != 0
  }
}

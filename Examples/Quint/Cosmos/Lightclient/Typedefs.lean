module

public import Veil.Quint

/-!
# Quint example `cosmos/lightclient/typedefs.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/cosmos/lightclient/typedefs.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module typedefs {

    type BlockHeader = {
        height: int,
        time: int,
        lastCommit: Set[str],
        VS: Set[str],
        NextVS: Set[str]
    }

    type LightBlock = {
        header: BlockHeader,
        Commits: Set[str]
    }

    type Blockchain = int -> BlockHeader
    type LightBlockMap = int -> LightBlock
    type LightBlockStatus = int -> str    
    
}

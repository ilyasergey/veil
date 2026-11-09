module

public import Veil.Quint

/-!
# Quint example `language-features/records.qnt`

Source: https://github.com/quint-co/quint/blob/07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0/examples/language-features/records.qnt
(Apache-2.0). The Quint text below is the original, with the comment markers
`//`, `/* */` written `--`, `/- -/`, and `(n).f(...)` for a method on a numeral;
`scripts/quint2veil.py` does this rewrite.

The module elaborates into a Veil module; no Veil checks are configured for it.
-/

module records {
    var rec1: { f1: int, f2: str }
    var rec2: { f2: str, f3: bool }
    var rec3: { f1: int }

    val rec1FieldNames = rec1.fieldNames()

    -- Should give a type error:
    -- val fieldNamesTest = (1).fieldNames()

    -- Should give a type error:
    -- val setOfRecords = Set(rec1, rec2)

    def updateF1(r) = r.with("f1", 1) 

    action init = all {
        rec1' = { f1: 1, f2: "hello" },
        rec2' = { f2: "world", f3: true },
        rec3' = { f1: 2 },
    }

    action step = all {
        rec1' = updateF1(rec1),
        rec2' = rec2.with("f3", true),
        rec3' = updateF1(rec3),
    }

    def d(p) = rec1.with("f1", p.f1)
    val t = d({ f1: 2 }).fieldNames()
}

#gen_spec
#model_check { } { } (maxDepth := 3)
#simulate { } { } (numTraces := 1000) (maxSteps := 20) (seed := 42)
end records

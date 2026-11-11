module

public import Veil
public import Veil.Frontend.Quint.Prelude
public meta import Veil.Frontend.Quint.Prelude
public meta import Veil.Frontend.Quint.Module
public meta import Veil.Frontend.Quint.Test
public import Veil.Frontend.Quint.Tactic
public meta import Veil.Frontend.Quint.Smt

/-!
# Veil's Quint frontend

`public import Veil.Quint` makes Quint modules (`module M { ... }`) available in a Lean file.
See `Veil.Frontend.Quint.Elab` for the translation and `Examples/Quint` for examples.
-/

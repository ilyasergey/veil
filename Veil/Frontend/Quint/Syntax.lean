module

public meta import Lean
public meta import Veil.Frontend.Quint.ParserUtil

/-!
# Quint surface syntax

A Lean grammar for [Quint](https://github.com/informalsystems/quint) modules, following Quint's
ANTLR grammar (`quint/src/generated/Quint.g4`). A Quint module parses as written, with three
lexical exceptions that Lean's tokenizer imposes:

1. comments: `//` and `/* */` must be written `--` and `/- -/` (same length, so positions agree);
2. a method called on a numeral needs parentheses: `(0).to(10)` instead of `0.to(10)`;
3. identifiers that are Lean keywords (e.g. `from`, `at`, `fun`) need `«»` quotes when they stand
   alone; as a method name after a dot (`x.then(y)`) they need no quotes.

The `quint-to-veil` skill and `scripts/quint2veil.py` apply these rewrites mechanically.

Importing this module makes `and`, `or`, `iff`, `implies` and `leadsTo` keywords, as in Quint.
-/

public meta section

namespace Veil.Quint
open Lean Parser

declare_syntax_cat quint_expr (behavior := both)
declare_syntax_cat quint_type (behavior := both)
declare_syntax_cat quint_decl (behavior := both)

/-- A qualified identifier `A::B::c`. -/
syntax quintQualId := ident (noWs "::" noWs ident)*

/-! ## Types -/

syntax:max quintQualId : quint_type
syntax:max quintQualId noWs "[" quint_type,+ "]" : quint_type
syntax:max "(" ")" : quint_type
syntax:max "(" quint_type ")" : quint_type
syntax:max "(" quint_type "," quint_type,+,? ")" : quint_type
syntax quintRowField := ident ":" quint_type
syntax:max "{" quintRowField,*,? "}" : quint_type
syntax:20 quint_type:21 " -> " quint_type:20 : quint_type
syntax:20 quint_type:21 " => " quint_type:20 : quint_type
syntax:20 atomic("(" quint_type,* ")" " => ") quint_type:20 : quint_type

/-! ## Expressions -/

/-- A lambda parameter: a name or `_`. -/
syntax quintParam := ident <|> hole
/-- A definition parameter, possibly with a type annotation. -/
syntax quintAnnotParam := quintParam (":" quint_type)?

syntax quintRecElem := (ident ":" quint_expr) <|> ("..." quint_expr)

/-- A variant pattern in a `match`. -/
syntax quintMatchPat := hole <|> (ident (noWs "(" quintParam ")")?)
syntax quintMatchCase := quintMatchPat " => " quint_expr

syntax quintQualifier :=
    &"val" <|> "def" <|> (&"pure" (&"val" <|> "def")) <|> &"action" <|> &"run"
  <|> &"temporal" <|> &"nondet"

/-- An operator definition `qualifier name(params): T = e`. -/
syntax quintOperDef :=
  quintQualifier quintQualId ("(" quintAnnotParam,*,? ")")? (":" quint_type)? (" = " quint_expr)? (";")?

/-- A destructuring `val (a, b) = e` or `val { f, g } = e`. -/
syntax quintValTuple := (&"pure")? &"val" (("(" quintParam,+ ")") <|> ("{" ident,+ "}")) " = " quint_expr (";")?

syntax:max num : quint_expr
syntax:max str : quint_expr
syntax:max quintQualId : quint_expr
syntax:max "(" ")" : quint_expr
syntax:max "(" quint_expr ")" : quint_expr
syntax:max "(" quint_expr "," quint_expr,+,? ")" : quint_expr
syntax:max "[" quint_expr,*,? "]" : quint_expr
syntax:max "{" quint_expr "}" : quint_expr
syntax:max "{" quintRecElem,+,? "}" : quint_expr
syntax:max "and" "{" quint_expr,+,? "}" : quint_expr
syntax:max "or" "{" quint_expr,+,? "}" : quint_expr
syntax:max &"all" "{" quint_expr,+,? "}" : quint_expr
syntax:max &"any" "{" quint_expr,+,? "}" : quint_expr
syntax:max "and" noWs "(" quint_expr,*,? ")" : quint_expr
syntax:max "or" noWs "(" quint_expr,*,? ")" : quint_expr
syntax:max "if" "(" quint_expr ")" quint_expr "else" quint_expr : quint_expr
syntax:max "match" quint_expr "{" ("|")? quintMatchCase ("|" quintMatchCase)* "}" : quint_expr
syntax:max atomic(quintParam " => ") quint_expr : quint_expr
syntax:max atomic("(" quintParam,+ ")" " => ") quint_expr : quint_expr
syntax:max atomic("(" "(" quintParam,+ ")" ")" " => ") quint_expr : quint_expr
syntax:max quintOperDef quint_expr : quint_expr
syntax:max quintValTuple quint_expr : quint_expr

-- dot calls, applications, list access
syntax:max quint_expr "." noWs rawIdent : quint_expr
syntax:max quint_expr noWs "[" quint_expr "]" : quint_expr

/-- `f(e_1, ..., e_n)`, `e.f(e_1, ..., e_n)`: no line break before `(`. -/
@[quint_expr_parser] def quintApp := trailing_parser:maxPrec:maxPrec
  checkNoLinebreakBefore >> "(" >> sepBy (categoryParser `quint_expr 0) "," (allowTrailingSep := true) >> ")"

/-- Binary minus: no line break before `-`, so that `a \n -b` is two expressions. -/
@[quint_expr_parser] def quintSub := trailing_parser:65:65
  checkNoLinebreakBefore >> " - " >> categoryParser `quint_expr 66

syntax:75 quint_expr:76 " ^ " quint_expr:75 : quint_expr
syntax:73 "-" quint_expr:73 : quint_expr
syntax:70 quint_expr:70 " * " quint_expr:71 : quint_expr
syntax:70 quint_expr:70 " / " quint_expr:71 : quint_expr
syntax:70 quint_expr:70 " % " quint_expr:71 : quint_expr
syntax:65 quint_expr:65 " + " quint_expr:66 : quint_expr
syntax:50 quint_expr:51 " == " quint_expr:51 : quint_expr
syntax:50 quint_expr:51 " != " quint_expr:51 : quint_expr
syntax:50 quint_expr:51 " < " quint_expr:51 : quint_expr
syntax:50 quint_expr:51 " <= " quint_expr:51 : quint_expr
syntax:50 quint_expr:51 " > " quint_expr:51 : quint_expr
syntax:50 quint_expr:51 " >= " quint_expr:51 : quint_expr
syntax:45 quint_expr:46 " = " quint_expr:46 : quint_expr
syntax:35 quint_expr:35 atomic(" and " notFollowedBy("{")) quint_expr:36 : quint_expr
syntax:30 quint_expr:30 atomic(" or " notFollowedBy("{")) quint_expr:31 : quint_expr
syntax:25 quint_expr:26 " iff " quint_expr:26 : quint_expr
syntax:22 quint_expr:23 " leadsTo " quint_expr:23 : quint_expr
syntax:20 quint_expr:21 " implies " quint_expr:20 : quint_expr
syntax:15 quint_expr:16 " -> " quint_expr:15 : quint_expr

/-! ## Declarations -/

syntax quintTypeHead := quintQualId (noWs "[" ident,+ "]")?
syntax quintVariant := ident (noWs "(" quint_type ")")?
syntax quintSumDef := ("|")? quintVariant ("|" quintVariant)*
syntax quintImportArg := ident " = " quint_expr
syntax quintFrom := &"from" str
/-- `M.*`, `M.name` (the parser reads `M.name` as one dotted identifier), or `M`. -/
syntax quintImportTarget := atomic(quintQualId noWs "." noWs "*") <|> quintQualId

syntax (name := quintConst) &"const" quintQualId ":" quint_type : quint_decl
syntax (name := quintVar) &"var" quintQualId ":" quint_type : quint_decl
syntax (name := quintAssume) &"assume" quintParam " = " quint_expr : quint_decl
syntax (name := quintTypeAbstract) &"type" quintQualId : quint_decl
-- A sum type needs a leading `|`, two variants, or a variant with an argument; otherwise the
-- right-hand side is a type alias.
syntax (name := quintTypeSum) &"type" quintTypeHead " = " quintSumDef : quint_decl
syntax (name := quintTypeAlias) &"type" quintTypeHead " = " quint_type : quint_decl
syntax (name := quintOper) quintOperDef : quint_decl
syntax (name := quintValDestr) quintValTuple : quint_decl
syntax (name := quintImport) "import" quintImportTarget (&"as" quintQualId)? (quintFrom)? : quint_decl
syntax (name := quintInstance) "import" quintQualId "(" quintImportArg,+,? ")"
  ((noWs "." noWs "*") <|> (&"as" quintQualId)) (quintFrom)? : quint_decl
syntax (name := quintExport) &"export" quintImportTarget (&"as" quintQualId)? : quint_decl

/-- A Quint module. -/
syntax (name := quintModule) "module " quintQualId "{" quint_decl* "}" : command

end Veil.Quint

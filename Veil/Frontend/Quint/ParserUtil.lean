module

public meta import Lean

public meta section

namespace Veil.Quint
open Lean Parser

private def checkTailNoLinebreak (prev : Syntax) : Bool :=
  match prev.getTailInfo with
  | .original _ _ trailing _ => !(trailing.toString.contains '\n')
  | _ => true

/-- Succeeds iff there is no line break between the previous token and this location. Quint
reads `a \n -b` and `f \n (x)` as two expressions; this keeps binary minus and application on one
line, as in Quint's own parser. -/
def checkNoLinebreakBefore (errorMsg : String := "no line break") : Parser where
  info := epsilonInfo
  fn := fun _ s =>
    let prev := s.stxStack.back
    if checkTailNoLinebreak prev then s else s.mkError errorMsg

open Lean.PrettyPrinter in
@[combinator_formatter checkNoLinebreakBefore]
def checkNoLinebreakBefore.formatter (_errorMsg : String := "") : Formatter := pure ()

open Lean.PrettyPrinter in
@[combinator_parenthesizer checkNoLinebreakBefore]
def checkNoLinebreakBefore.parenthesizer (_errorMsg : String := "") : Parenthesizer := pure ()

/-- Quint's own keywords, which are never identifiers. -/
def quintKeywords : List String :=
  ["if", "else", "match", "and", "or", "iff", "implies", "leadsTo", "import", "export", "module",
   "def", "val", "var", "const", "pure", "action", "run", "temporal", "nondet", "type", "assume",
   "all", "any", "from", "as"]

/-- An identifier that Lean (or Veil, or another package) has made a keyword, such as `from`,
`trusted` or `assert`. Quint code uses these as ordinary names. -/
def quintKwIdentFn : ParserFn := fun c s =>
  let startPos := s.pos
  let s := tokenFn ["identifier"] c s
  if s.hasError then s else
  match s.stxStack.back with
  | .atom info val =>
    if val.length > 0 && val.front.isAlpha && val.all (fun ch => ch.isAlphanum || ch == '_')
        && !quintKeywords.contains val then
      s.popSyntax.pushSyntax (Syntax.ident info val.toRawSubstring (Name.mkSimple val) [])
    else s.mkErrorAt "identifier" startPos
  | _ => s.mkErrorAt "identifier" startPos

def quintKwIdent : Parser where
  info := { firstTokens := .unknown }
  fn := quintKwIdentFn

open Lean.PrettyPrinter in
@[combinator_formatter quintKwIdent]
def quintKwIdent.formatter : Formatter := Formatter.identNoAntiquot.formatter

open Lean.PrettyPrinter in
@[combinator_parenthesizer quintKwIdent]
def quintKwIdent.parenthesizer : Parenthesizer := Parenthesizer.identNoAntiquot.parenthesizer

end Veil.Quint

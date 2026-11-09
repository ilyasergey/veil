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

end Veil.Quint

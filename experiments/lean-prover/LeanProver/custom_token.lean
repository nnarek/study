import Lean
open Lean
open Lean.Parser


private def asStringAux (quoted : Bool) (startPos : String.Pos) (transform : String → String) : ParserFn := fun c s =>
  let input    := c.input
  let stopPos  := s.pos
  let leading  := mkEmptySubstringAt input startPos
  let val      := input.extract startPos stopPos
  let val      := transform val
  let trailing := mkEmptySubstringAt input stopPos
  let atom     :=
    mkAtom (SourceInfo.original leading startPos trailing stopPos) <|
      if quoted then val.quote else val
  s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
def asStringFn (p : ParserFn) (quoted := false) (transform : String → String := id ) : ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError then s
  else asStringAux quoted startPos transform c (s.shrinkStack iniSz)

def iNameKind := `iNameNode

-- copied from https://github.com/leanprover/verso/blob/20793dbbe6f09258629e62343563df22540d3145/src/verso/Verso/Output/Html.lean#L186
def iNameFn : ParserFn :=
  atomicFn <|
    nodeFn iNameKind <|
      asStringFn <|(manyFn iNameCharFn) -- asStringFn needed for colors
where
  iNameCharFn := satisfyFn iNameChar "attribute name"
  iNameChar (c : Char) : Bool := Char.isAlpha c -- only ascii chars

def iNameNoAntiquot : Parser where
  fn := andthenFn iNameFn (takeWhileFn Char.isWhitespace)

def iName : Parser :=
  withAntiquot (mkAntiquot "iName" iNameKind) iNameNoAntiquot

@[combinator_parenthesizer iName]
def iName.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter iName]
def iName.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous



syntax "[[" iName "]]" : term 

macro_rules
  | `([[ $n:iName ]]) => `($(Lean.mkIdent (Name.mkSimple n.raw[0].getAtomVal)))

def aaa : Nat := 8

#eval [[ aaa ]] -- we can even jump to original variable via Ctrl key

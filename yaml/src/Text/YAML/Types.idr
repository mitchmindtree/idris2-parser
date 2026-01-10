module Text.YAML.Types

import public Data.Time.Time
import Derive.Prelude
import Text.Bounds
import Text.ParseError

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          YAML Value
--------------------------------------------------------------------------------

||| Data type for YAML values.
public export
data YAMLValue : Type where
  ||| Null value (null, ~, or empty)
  YNull   : YAMLValue

  ||| Boolean value
  YBool   : Bool -> YAMLValue

  ||| Integer value
  YInt    : Integer -> YAMLValue

  ||| Floating point value (includes nan, inf, -inf)
  YFloat  : Double -> YAMLValue

  ||| String value
  YStr    : String -> YAMLValue

  ||| Sequence (list) of values
  YSeq    : List YAMLValue -> YAMLValue

  ||| Mapping (dictionary) of key-value pairs
  YMap    : List (YAMLValue, YAMLValue) -> YAMLValue

  ||| Timestamp value (ISO 8601 date/time)
  YTime   : AnyTime -> YAMLValue

%runElab derive "YAMLValue" [Eq, Show]

--------------------------------------------------------------------------------
--          Tokens
--------------------------------------------------------------------------------

||| Token type for YAML lexemes
public export
data YAMLToken : Type where
  ||| Sequence item indicator '-'
  TDash     : YAMLToken

  ||| Mapping value indicator ':'
  TColon    : YAMLToken

  ||| Comma separator in flow context
  TComma    : YAMLToken

  ||| Start of flow mapping '{'
  TLBrace   : YAMLToken

  ||| End of flow mapping '}'
  TRBrace   : YAMLToken

  ||| Start of flow sequence '['
  TLBracket : YAMLToken

  ||| End of flow sequence ']'
  TRBracket : YAMLToken

  ||| A scalar value (string, number, bool, null)
  TScalar   : YAMLValue -> YAMLToken

  ||| Newline (significant in block context)
  TNewline  : YAMLToken

  ||| Indent (indentation increased)
  TIndent   : YAMLToken

  ||| Dedent (indentation decreased)
  TDedent   : YAMLToken

  ||| End of input
  TEOI      : YAMLToken

  ||| Document start marker '---'
  TDocStart : YAMLToken

  ||| Document end marker '...'
  TDocEnd   : YAMLToken

  ||| Tag (e.g., !tag, !!str, !<uri>)
  TTag      : String -> YAMLToken

  ||| Directive (e.g., %YAML 1.2, %TAG !prefix! uri)
  TDirective : (name : String) -> (value : String) -> YAMLToken

  ||| Complex key indicator '?'
  TQuestion : YAMLToken

%runElab derive "YAMLToken" [Eq, Show]

export
Interpolation YAMLToken where
  interpolate TDash       = "'-'"
  interpolate TColon      = "':'"
  interpolate TComma      = "','"
  interpolate TLBrace     = "'{'"
  interpolate TRBrace     = "'}'"
  interpolate TLBracket   = "'['"
  interpolate TRBracket   = "']'"
  interpolate (TScalar v) = case v of
    YNull     => "null"
    YBool b   => if b then "true" else "false"
    YInt i    => show i
    YFloat d  => show d
    YStr s    => show s
    YSeq _    => "sequence"
    YMap _    => "mapping"
    YTime t   => interpolate t
  interpolate TNewline    = "<newline>"
  interpolate TIndent     = "<indent>"
  interpolate TDedent     = "<dedent>"
  interpolate TEOI        = "end of input"
  interpolate TDocStart   = "'---'"
  interpolate TDocEnd     = "'...'"
  interpolate (TTag t)    = "tag '!\{t}'"
  interpolate (TDirective n v) = "directive '%\{n} \{v}'"
  interpolate TQuestion   = "'?'"

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

||| YAML-specific parse errors
public export
data YAMLParseError : Type where
  ||| Invalid indentation level
  IndentError     : (expected : Nat) -> (got : Nat) -> YAMLParseError

  ||| Tab character used for indentation (not allowed in YAML)
  TabIndent       : YAMLParseError

  ||| Unclosed flow context
  UnclosedFlow    : Char -> YAMLParseError

  ||| Invalid escape sequence in string
  InvalidEscape   : Char -> YAMLParseError

  ||| Expected a specific token
  ExpectedToken   : String -> YAMLParseError

%runElab derive "YAMLParseError" [Eq, Show]

export
Interpolation YAMLParseError where
  interpolate (IndentError exp got) =
    "Invalid indentation: expected \{show exp} spaces, got \{show got}"
  interpolate TabIndent =
    "Tab characters are not allowed for indentation in YAML"
  interpolate (UnclosedFlow c) =
    "Unclosed flow context starting with '\{pack [c]}'"
  interpolate (InvalidEscape c) =
    "Invalid escape sequence: '\\{pack [c]}'"
  interpolate (ExpectedToken t) =
    "Expected \{t}"

||| Error type for lexing and parsing YAML files
public export
0 YAMLErr : Type
YAMLErr = InnerError YAMLParseError

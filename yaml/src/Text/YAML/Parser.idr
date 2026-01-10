module Text.YAML.Parser

import Data.List1
import Data.SnocList
import public Text.Parse.Manual
import Text.YAML.Lexer
import Text.YAML.Types

%default total

--------------------------------------------------------------------------------
--          Parser Types
--------------------------------------------------------------------------------

0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded YAMLToken)
  -> (0 acc : SuffixAcc xs)
  -> Res b YAMLToken xs YAMLParseError t

--------------------------------------------------------------------------------
--          Tag Application
--------------------------------------------------------------------------------

||| Convert a YAMLValue to its string representation for !!str coercion
valueToString : YAMLValue -> String
valueToString YNull = "null"
valueToString (YBool True) = "true"
valueToString (YBool False) = "false"
valueToString (YInt i) = show i
valueToString (YFloat d) = show d
valueToString (YStr s) = s
valueToString (YSeq _) = ""  -- Can't meaningfully convert
valueToString (YMap _) = ""  -- Can't meaningfully convert
valueToString (YTime t) = interpolate t

||| Try to parse a string as a boolean
parseBoolFromString : String -> Maybe Bool
parseBoolFromString "true" = Just True
parseBoolFromString "True" = Just True
parseBoolFromString "TRUE" = Just True
parseBoolFromString "false" = Just False
parseBoolFromString "False" = Just False
parseBoolFromString "FALSE" = Just False
parseBoolFromString _ = Nothing

||| Force value to string
tagToStr : YAMLValue -> YAMLValue
tagToStr v = YStr (valueToString v)

||| Try to parse a string as an integer (reusing Lexer's tryNumber)
tryParseInt : String -> Maybe Integer
tryParseInt s = case tryYamlInteger s of
  Just i  => Just i
  Nothing => case tryNumber s of
    Just (YInt i) => Just i
    _             => Nothing

||| Try to parse a string as a float (reusing Lexer's tryNumber)
tryParseFloat : String -> Maybe Double
tryParseFloat s = case tryNumber s of
  Just (YFloat d) => Just d
  Just (YInt i)   => Just (cast i)
  _               => Nothing

||| Force value to integer
tagToInt : YAMLValue -> YAMLValue
tagToInt (YStr s) = maybe (YStr s) YInt (tryParseInt s)
tagToInt (YInt i) = YInt i
tagToInt (YFloat d) = YInt (cast d)
tagToInt v = v

||| Force value to float
tagToFloat : YAMLValue -> YAMLValue
tagToFloat (YStr s) = maybe (YStr s) YFloat (tryParseFloat s)
tagToFloat (YInt i) = YFloat (cast i)
tagToFloat (YFloat d) = YFloat d
tagToFloat v = v

||| Force value to boolean
tagToBool : YAMLValue -> YAMLValue
tagToBool (YStr s) = maybe (YStr s) YBool (parseBoolFromString s)
tagToBool (YBool b) = YBool b
tagToBool v = v

||| Normalize a tag to its canonical short name
||| Handles: "!str" -> "str", "tag:yaml.org,2002:str" -> "str", "str" -> "str"
normalizeTag : String -> String
normalizeTag s =
  let yamlPrefix = "tag:yaml.org,2002:"
      prefixLen  = length yamlPrefix
   in if isPrefixOf (unpack yamlPrefix) (unpack s)
        then substr prefixLen (length s `minus` prefixLen) s
        else case unpack s of
          '!' :: rest => pack rest
          _           => s

||| Apply a core schema tag to a value
||| Returns the coerced value, or the original if coercion not applicable
applyTag : String -> YAMLValue -> YAMLValue
applyTag tag v = case normalizeTag tag of
  "str"   => tagToStr v
  "int"   => tagToInt v
  "float" => tagToFloat v
  "bool"  => tagToBool v
  "null"  => YNull
  "seq"   => v  -- Structure already determined
  "map"   => v  -- Structure already determined
  _       => v  -- Unknown tag - keep as-is

--------------------------------------------------------------------------------
--          Flow Collection Parsers
--------------------------------------------------------------------------------

mutual
  flowSeq : Bounds -> SnocList YAMLValue -> Rule True YAMLValue

  flowMap : Bounds -> SnocList (YAMLValue, YAMLValue) -> Rule True YAMLValue

  -- Parse a nested block value (consumes TIndent, parses value, leaves TDedent for caller)
  -- Returns just the parsed value, caller handles continuation
  blockNestedValue : Rule True YAMLValue
  blockNestedValue (B TIndent _ :: xs) (SA r) = succT $ value xs r
  blockNestedValue xs _ = fail xs

  -- Handle continuation after parsing a nested value in block mapping
  -- Takes the result from blockNestedValue and continues parsing
  blockMapAfterNested :
       YAMLValue
    -> SnocList (YAMLValue, YAMLValue)
    -> Res True YAMLToken xs YAMLParseError YAMLValue
    -> (0 acc : SuffixAcc xs)
    -> Res True YAMLToken xs YAMLParseError YAMLValue
  blockMapAfterNested k sv (Succ0 v (B TNewline _ :: B TDedent _ :: B (TScalar k2) _ :: B TColon _ :: ys)) (SA r) =
    -- After nested block, more pairs at parent level
    succT $ blockMapAfterColon k2 (sv :< (k, v)) ys r
  blockMapAfterNested k sv (Succ0 v rest@(B TNewline _ :: B TDedent _ :: ys)) _ =
    -- End of this mapping level
    Succ0 (YMap $ sv <>> [(k, v)]) rest
  blockMapAfterNested k sv (Succ0 v rest@(B TDedent _ :: ys)) _ =
    -- End of this mapping level (no newline before dedent)
    Succ0 (YMap $ sv <>> [(k, v)]) rest
  blockMapAfterNested k sv (Succ0 v ys) _ =
    -- End of document
    Succ0 (YMap $ sv <>> [(k, v)]) ys
  blockMapAfterNested k sv (Fail0 err) _ = Fail0 err

  -- Handle result after parsing nested value in block sequence
  blockSeqAfterNested :
       SnocList YAMLValue
    -> Res True YAMLToken xs YAMLParseError YAMLValue
    -> (0 acc : SuffixAcc xs)
    -> Res True YAMLToken xs YAMLParseError YAMLValue
  blockSeqAfterNested sv (Succ0 v (B TNewline _ :: B TDedent _ :: B TDash _ :: ys)) (SA r) =
    -- After nested block, more items at parent level
    succT $ blockSeqItems (sv :< v) ys r
  blockSeqAfterNested sv (Succ0 v rest@(B TNewline _ :: B TDedent _ :: ys)) _ =
    -- End of this sequence level
    Succ0 (YSeq $ sv <>> [v]) rest
  blockSeqAfterNested sv (Succ0 v rest@(B TDedent _ :: ys)) _ =
    -- End without preceding newline
    Succ0 (YSeq $ sv <>> [v]) rest
  blockSeqAfterNested sv (Succ0 v ys) _ =
    -- End of document
    Succ0 (YSeq $ sv <>> [v]) ys
  blockSeqAfterNested sv (Fail0 err) _ = Fail0 err

  -- Parse remaining items in a block sequence (after the first dash was consumed)
  blockSeqItems : SnocList YAMLValue -> Rule True YAMLValue
  -- Content on next line after dash (handles: -\n  content)
  blockSeqItems sv (B TNewline _ :: xs@(B TIndent _ :: _)) (SA r) =
    succT $ blockSeqAfterNested sv (blockNestedValue xs r) r
  -- Parse value on same line
  blockSeqItems sv xs acc@(SA r) = case value xs acc of
    -- Continue at same level
    Succ0 v (B TNewline _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) ys r
    Succ0 v (B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) ys r
    -- Continue at nested level (handles: - - a\n  - b)
    Succ0 v (B TNewline _ :: B TIndent _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) ys r
    -- Continue after nested structure exits (handles: - - a\n  - b\n- c)
    -- Only applies when v is a nested seq/map, not a scalar
    Succ0 v@(YSeq _) (B TNewline _ :: B TDedent _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) ys r
    Succ0 v@(YMap _) (B TNewline _ :: B TDedent _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) ys r
    -- End at dedent - leave TDedent for outer parser to handle continuation
    Succ0 v rest@(B TNewline _ :: B TDedent _ :: ys) =>
      Succ0 (YSeq $ sv <>> [v]) rest
    Succ0 v rest@(B TDedent _ :: ys) =>
      Succ0 (YSeq $ sv <>> [v]) rest
    -- End of sequence
    Succ0 v ys =>
      Succ0 (YSeq $ sv <>> [v]) ys
    Fail0 err => Fail0 err

  -- Parse value after colon in block mapping, then check for more pairs
  -- k: the key we're parsing the value for
  -- sv: accumulated key-value pairs so far
  blockMapAfterColon : YAMLValue -> SnocList (YAMLValue, YAMLValue) -> Rule True YAMLValue
  -- Nested block: TNewline followed by TIndent starts nested content
  -- Use @ pattern to avoid consuming TIndent here, delegate to helper
  blockMapAfterColon k sv (B TNewline _ :: xs@(B TIndent _ :: _)) (SA r) =
    succT $ blockMapAfterNested k sv (blockNestedValue xs r) r
  -- Same level: next key-value pair (value is null)
  blockMapAfterColon k sv (B TNewline _ :: B (TScalar k2) _ :: B TColon _ :: xs) (SA r) =
    succT $ blockMapAfterColon k2 (sv :< (k, YNull)) xs r
  -- Complex key follows (value is null for current key)
  blockMapAfterColon k sv (B TNewline _ :: B TQuestion _ :: xs) (SA r) =
    case succT $ value xs r of
      Succ0 k2 (B TColon _ :: rest) =>
        succT $ blockMapAfterColon k2 (sv :< (k, YNull)) rest r
      Succ0 k2 (B TNewline _ :: B TColon _ :: rest) =>
        succT $ blockMapAfterColon k2 (sv :< (k, YNull)) rest r
      Succ0 _ ys => fail ys
      Fail0 err => Fail0 err
  -- End of block: TDedent signals end of this mapping level
  -- Note: Don't consume TDedent - it may be needed by outer parser
  blockMapAfterColon k sv (B TNewline _ :: ys@(B TDedent _ :: xs)) (SA r) =
    Succ0 (YMap $ sv <>> [(k, YNull)]) ys
  -- End of mapping: just newline
  blockMapAfterColon k sv (B TNewline _ :: xs) (SA r) =
    Succ0 (YMap $ sv <>> [(k, YNull)]) xs
  -- Value on same line
  blockMapAfterColon k sv xs acc@(SA r) =
    case value xs acc of
      Succ0 v (B TNewline _ :: B (TScalar k2) _ :: B TColon _ :: ys) =>
        -- Another key-value pair follows at same level
        succT $ blockMapAfterColon k2 (sv :< (k, v)) ys r
      Succ0 v (B TNewline _ :: B TQuestion _ :: ys) =>
        -- Complex key follows at same level
        case succT $ value ys r of
          Succ0 k2 (B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (sv :< (k, v)) rest r
          Succ0 k2 (B TNewline _ :: B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (sv :< (k, v)) rest r
          Succ0 _ zs => fail zs
          Fail0 err => Fail0 err
      Succ0 v (B TNewline _ :: B TIndent _ :: B (TScalar k2) _ :: B TColon _ :: ys) =>
        -- Another key-value pair at nested level (compact notation: - key: val\n  key2: val2)
        succT $ blockMapAfterColon k2 (sv :< (k, v)) ys r
      Succ0 v (B TNewline _ :: B TIndent _ :: B TQuestion _ :: ys) =>
        -- Complex key at nested level
        case succT $ value ys r of
          Succ0 k2 (B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (sv :< (k, v)) rest r
          Succ0 k2 (B TNewline _ :: B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (sv :< (k, v)) rest r
          Succ0 _ zs => fail zs
          Fail0 err => Fail0 err
      Succ0 v rest@(B TNewline _ :: B TDedent _ :: ys) =>
        -- End of this mapping level - leave TDedent for outer parser
        Succ0 (YMap $ sv <>> [(k, v)]) rest
      Succ0 v (B (TScalar k2) _ :: B TColon _ :: ys) =>
        -- After block scalar: key follows directly without TNewline
        -- (block scalar consumed the newline internally)
        succT $ blockMapAfterColon k2 (sv :< (k, v)) ys r
      Succ0 v ys =>
        -- No more key-value pairs
        Succ0 (YMap $ sv <>> [(k, v)]) ys
      Fail0 err => Fail0 err

  value : Rule True YAMLValue
  -- Tagged value: parse the tag, then the value, and apply the tag
  value (B (TTag tag) _ :: xs) (SA r) =
    case succT $ value xs r of
      Succ0 v ys => Succ0 (applyTag tag v) ys
      Fail0 err => Fail0 err
  -- Block sequence: parse first dash, then delegate to blockSeqItems
  value (B TDash _ :: xs) (SA r) = succT $ blockSeqItems [<] xs r
  -- Complex key: ? key : value (allows any value type as key)
  value (B TQuestion _ :: xs) (SA r) =
    case succT $ value xs r of
      -- Colon immediately after key
      Succ0 k (B TColon _ :: rest) =>
        succT $ blockMapAfterColon k [<] rest r
      -- Colon on next line after key
      Succ0 k (B TNewline _ :: B TColon _ :: rest) =>
        succT $ blockMapAfterColon k [<] rest r
      -- Missing colon after complex key
      Succ0 _ ys => fail ys
      Fail0 err => Fail0 err
  -- Block mapping: scalar followed by colon, delegate to blockMapAfterColon
  value (B (TScalar k) _ :: B TColon _ :: xs) (SA r) = succT $ blockMapAfterColon k [<] xs r
  -- Plain scalar value
  value (B (TScalar v) _ :: xs) _ = Succ0 v xs
  value (B TLBracket b :: B TRBracket _ :: xs) _ = Succ0 (YSeq []) xs
  value (B TLBracket b :: xs) (SA r) = succT $ flowSeq b [<] xs r
  value (B TLBrace b :: B TRBrace _ :: xs) _ = Succ0 (YMap []) xs
  value (B TLBrace b :: xs) (SA r) = succT $ flowMap b [<] xs r
  value xs _ = fail xs

  flowSeq b sv xs acc@(SA r) = case value xs acc of
    Succ0 v (B TComma _ :: ys)    => succT $ flowSeq b (sv :< v) ys r
    Succ0 v (B TRBracket _ :: ys) => Succ0 (YSeq $ sv <>> [v]) ys
    Succ0 v (B TEOI _ :: _)       => unclosed b TLBracket
    res@(Fail0 (B (Expected [] "end of input") _)) => unclosed b TLBracket
    res                           => failInParen b TLBracket res

  -- Complex key in flow mapping: {? key: value}
  flowMap b sv (B TQuestion _ :: xs) (SA r) =
    case succT $ value xs r of
      Succ0 k (B TColon _ :: rest) =>
        case succT $ value rest r of
          Succ0 v (B TComma _ :: ys)  => succT $ flowMap b (sv :< (k, v)) ys r
          Succ0 v (B TRBrace _ :: ys) => Succ0 (YMap $ sv <>> [(k, v)]) ys
          Succ0 v (B TEOI _ :: _)     => unclosed b TLBrace
          res@(Fail0 (B (Expected [] "end of input") _)) => unclosed b TLBrace
          res                         => failInParen b TLBrace res
      Succ0 _ ys => fail ys  -- Missing colon after complex key
      Fail0 err => Fail0 err
  flowMap b sv (B (TScalar k) _ :: B TColon _ :: xs) (SA r) =
    case succT $ value xs r of
      Succ0 v (B TComma _ :: ys)  => succT $ flowMap b (sv :< (k, v)) ys r
      Succ0 v (B TRBrace _ :: ys) => Succ0 (YMap $ sv <>> [(k, v)]) ys
      Succ0 v (B TEOI _ :: _)     => unclosed b TLBrace
      res@(Fail0 (B (Expected [] "end of input") _)) => unclosed b TLBrace
      res                         => failInParen b TLBrace res
  flowMap b sv (B (TScalar _) _ :: x :: xs) _ = expected x.bounds "':'" "\{x.val}"
  flowMap b sv (x :: xs) _ = expected x.bounds "key" "\{x.val}"
  flowMap b sv [] _ = eoi

--------------------------------------------------------------------------------
--          Entry Point
--------------------------------------------------------------------------------

||| Parse all YAML documents from a string (YAML streams can contain multiple documents)
export
parseYAML : Origin -> String -> Either (ParseError YAMLParseError) (SnocList YAMLValue)
parseYAML o str = case lexYAML str of
  Right ts => go [<] ts suffixAcc
  Left err => Left (toParseError o str err)
  where
    go : SnocList YAMLValue
      -> (ts : List (Bounded YAMLToken))
      -> (0 acc : SuffixAcc ts)
      -> Either (ParseError YAMLParseError) (SnocList YAMLValue)
    -- Base cases: end of stream
    go sx [] _ = Right sx
    go sx [B TEOI _] _ = Right sx
    -- Skip whitespace/doc markers/directives at start of each iteration
    go sx (B TNewline _ :: ts) (SA r) = go sx ts r
    go sx (B TIndent _ :: ts) (SA r) = go sx ts r
    go sx (B TDedent _ :: ts) (SA r) = go sx ts r
    go sx (B TDocStart _ :: ts) (SA r) = go sx ts r
    go sx (B TDocEnd _ :: ts) (SA r) = go sx ts r
    go sx (B (TDirective _ _) _ :: ts) (SA r) = go sx ts r  -- Skip directives
    -- Parse a document value, then skip to next doc boundary
    go sx ts (SA r) = case value ts (SA r) of
      Fail0 err => Left (toParseError o str err)
      Succ0 v [] => Right (sx :< v)
      Succ0 v [B TEOI _] => Right (sx :< v)
      Succ0 v (B TNewline _ :: ts2) => go (sx :< v) ts2 r
      Succ0 v (B TDedent _ :: ts2) => go (sx :< v) ts2 r
      Succ0 v (B TDocEnd _ :: ts2) => go (sx :< v) ts2 r
      Succ0 v (B TDocStart _ :: ts2) => go (sx :< v) ts2 r
      Succ0 v ts2 => go (sx :< v) ts2 r

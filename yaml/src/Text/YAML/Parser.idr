module Text.YAML.Parser

import Data.List1
import Data.SnocList
import Data.SortedMap
import public Text.Parse.Manual
import Text.YAML.Lexer
import Text.YAML.Types

%default total

--------------------------------------------------------------------------------
--          Parser Types
--------------------------------------------------------------------------------

||| Map from anchor names to their resolved values
public export
0 AnchorMap : Type
AnchorMap = SortedMap String YAMLValue

||| Standard rule type (no anchor tracking)
0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded YAMLToken)
  -> (0 acc : SuffixAcc xs)
  -> Res b YAMLToken xs YAMLParseError t

||| Anchor-aware rule type - threads anchor map and returns updated map with value
0 RuleA : Bool -> Type -> Type
RuleA b t =
     AnchorMap
  -> (xs : List $ Bounded YAMLToken)
  -> (0 acc : SuffixAcc xs)
  -> Res b YAMLToken xs YAMLParseError (AnchorMap, t)

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
--          Merge Key Helpers
--------------------------------------------------------------------------------

||| Check if value is the merge key indicator
isMergeKey : YAMLValue -> Bool
isMergeKey (YStr "<<") = True
isMergeKey _ = False

||| Type alias for map accumulator during parsing
0 MapAcc : Type
MapAcc = SortedMap YAMLValue YAMLValue

||| Add a key-value pair - O(log n), last wins automatically via insert
addPair : YAMLValue -> YAMLValue -> MapAcc -> MapAcc
addPair = insert

||| Merge pairs from a YMap into accumulated map
||| Only adds pairs whose keys don't already exist in acc (first wins for merge)
||| O(m log n) where m = source size, n = acc size
mergePairs : List (YAMLValue, YAMLValue) -> MapAcc -> MapAcc
mergePairs source acc = foldl addIfAbsent acc source
  where
    addIfAbsent : MapAcc -> (YAMLValue, YAMLValue) -> MapAcc
    addIfAbsent m (k, v) = case lookup k m of
      Just _  => m            -- Key exists, keep original (first wins)
      Nothing => insert k v m -- Key absent, add

||| Process a key-value pair, handling merge key specially
||| Returns updated accumulator
addOrMerge : YAMLValue -> YAMLValue -> MapAcc -> MapAcc
addOrMerge k v acc =
  if isMergeKey k
    then case v of
      YNull      => acc  -- No-op for null merge value
      YMap pairs => mergePairs pairs acc
      YSeq maps  => foldl (\a, m => case m of
                      YMap ps => mergePairs ps a
                      _       => a) acc maps
      _ => addPair k v acc  -- Invalid merge value
    else addPair k v acc    -- Regular key

--------------------------------------------------------------------------------
--          Flow Collection Parsers
--------------------------------------------------------------------------------

mutual
  flowSeq : Bounds -> SnocList YAMLValue -> RuleA True YAMLValue

  flowMap : Bounds -> MapAcc -> RuleA True YAMLValue

  -- Parse a nested block value (consumes TIndent, parses value, leaves TDedent for caller)
  -- Returns just the parsed value, caller handles continuation
  blockNestedValue : RuleA True YAMLValue
  blockNestedValue m (B TIndent _ :: xs) (SA r) = succT $ value m xs r
  blockNestedValue m xs _ = fail xs

  -- Handle continuation after parsing a nested value in block mapping
  -- Takes the result from blockNestedValue and continues parsing
  blockMapAfterNested :
       YAMLValue
    -> MapAcc
    -> Res True YAMLToken xs YAMLParseError (AnchorMap, YAMLValue)
    -> (0 acc : SuffixAcc xs)
    -> Res True YAMLToken xs YAMLParseError (AnchorMap, YAMLValue)
  blockMapAfterNested k sv (Succ0 (m', v) (B TNewline _ :: B TDedent _ :: B (TScalar k2) _ :: B TColon _ :: ys)) (SA r) =
    -- After nested block, more pairs at parent level
    succT $ blockMapAfterColon k2 (addOrMerge k v sv) m' ys r
  blockMapAfterNested k sv (Succ0 (m', v) rest@(B TNewline _ :: B TDedent _ :: ys)) _ =
    -- End of this mapping level
    Succ0 (m', YMap $ toList (addOrMerge k v sv)) rest
  blockMapAfterNested k sv (Succ0 (m', v) rest@(B TDedent _ :: ys)) _ =
    -- End of this mapping level (no newline before dedent)
    Succ0 (m', YMap $ toList (addOrMerge k v sv)) rest
  blockMapAfterNested k sv (Succ0 (m', v) ys) _ =
    -- End of document
    Succ0 (m', YMap $ toList (addOrMerge k v sv)) ys
  blockMapAfterNested k sv (Fail0 err) _ = Fail0 err

  -- Handle result after parsing nested value in block sequence
  blockSeqAfterNested :
       SnocList YAMLValue
    -> Res True YAMLToken xs YAMLParseError (AnchorMap, YAMLValue)
    -> (0 acc : SuffixAcc xs)
    -> Res True YAMLToken xs YAMLParseError (AnchorMap, YAMLValue)
  blockSeqAfterNested sv (Succ0 (m', v) (B TNewline _ :: B TDedent _ :: B TDash _ :: ys)) (SA r) =
    -- After nested block, more items at parent level
    succT $ blockSeqItems (sv :< v) m' ys r
  blockSeqAfterNested sv (Succ0 (m', v) rest@(B TNewline _ :: B TDedent _ :: ys)) _ =
    -- End of this sequence level
    Succ0 (m', YSeq $ sv <>> [v]) rest
  blockSeqAfterNested sv (Succ0 (m', v) rest@(B TDedent _ :: ys)) _ =
    -- End without preceding newline
    Succ0 (m', YSeq $ sv <>> [v]) rest
  blockSeqAfterNested sv (Succ0 (m', v) ys) _ =
    -- End of document
    Succ0 (m', YSeq $ sv <>> [v]) ys
  blockSeqAfterNested sv (Fail0 err) _ = Fail0 err

  -- Parse remaining items in a block sequence (after the first dash was consumed)
  blockSeqItems : SnocList YAMLValue -> RuleA True YAMLValue
  -- Content on next line after dash (handles: -\n  content)
  blockSeqItems sv m (B TNewline _ :: xs@(B TIndent _ :: _)) (SA r) =
    succT $ blockSeqAfterNested sv (blockNestedValue m xs r) r
  -- Parse value on same line
  blockSeqItems sv m xs acc@(SA r) = case value m xs acc of
    -- Continue at same level
    Succ0 (m', v) (B TNewline _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) m' ys r
    Succ0 (m', v) (B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) m' ys r
    -- Continue at nested level (handles: - - a\n  - b)
    Succ0 (m', v) (B TNewline _ :: B TIndent _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) m' ys r
    -- Continue after nested structure exits (handles: - - a\n  - b\n- c)
    -- Only applies when v is a nested seq/map, not a scalar
    Succ0 (m', v@(YSeq _)) (B TNewline _ :: B TDedent _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) m' ys r
    Succ0 (m', v@(YMap _)) (B TNewline _ :: B TDedent _ :: B TDash _ :: ys) =>
      succT $ blockSeqItems (sv :< v) m' ys r
    -- End at dedent - leave TDedent for outer parser to handle continuation
    Succ0 (m', v) rest@(B TNewline _ :: B TDedent _ :: ys) =>
      Succ0 (m', YSeq $ sv <>> [v]) rest
    Succ0 (m', v) rest@(B TDedent _ :: ys) =>
      Succ0 (m', YSeq $ sv <>> [v]) rest
    -- End of sequence
    Succ0 (m', v) ys =>
      Succ0 (m', YSeq $ sv <>> [v]) ys
    Fail0 err => Fail0 err

  -- Parse value after colon in block mapping, then check for more pairs
  -- k: the key we're parsing the value for
  -- sv: accumulated key-value pairs so far
  blockMapAfterColon : YAMLValue -> MapAcc -> RuleA True YAMLValue
  -- Nested block: TNewline followed by TIndent starts nested content
  -- Use @ pattern to avoid consuming TIndent here, delegate to helper
  blockMapAfterColon k sv m (B TNewline _ :: xs@(B TIndent _ :: _)) (SA r) =
    succT $ blockMapAfterNested k sv (blockNestedValue m xs r) r
  -- Same level: next key-value pair (value is null)
  blockMapAfterColon k sv m (B TNewline _ :: B (TScalar k2) _ :: B TColon _ :: xs) (SA r) =
    succT $ blockMapAfterColon k2 (addOrMerge k YNull sv) m xs r
  -- Null key follows at same level (value is null for current key)
  blockMapAfterColon k sv m (B TNewline _ :: B TColon _ :: xs) (SA r) =
    succT $ blockMapAfterColon YNull (addOrMerge k YNull sv) m xs r
  -- Complex key follows (value is null for current key)
  blockMapAfterColon k sv m (B TNewline _ :: B TQuestion _ :: xs) (SA r) =
    case succT $ value m xs r of
      Succ0 (m', k2) (B TColon _ :: rest) =>
        succT $ blockMapAfterColon k2 (addOrMerge k YNull sv) m' rest r
      Succ0 (m', k2) (B TNewline _ :: B TColon _ :: rest) =>
        succT $ blockMapAfterColon k2 (addOrMerge k YNull sv) m' rest r
      Succ0 _ ys => fail ys
      Fail0 err => Fail0 err
  -- End of block: TDedent signals end of this mapping level
  -- Note: Don't consume TDedent - it may be needed by outer parser
  blockMapAfterColon k sv m (B TNewline _ :: ys@(B TDedent _ :: xs)) (SA r) =
    Succ0 (m, YMap $ toList (addOrMerge k YNull sv)) ys
  -- End of mapping: just newline
  blockMapAfterColon k sv m (B TNewline _ :: xs) (SA r) =
    Succ0 (m, YMap $ toList (addOrMerge k YNull sv)) xs
  -- Value on same line
  blockMapAfterColon k sv m xs acc@(SA r) =
    case value m xs acc of
      Succ0 (m', v) (B TNewline _ :: B (TScalar k2) _ :: B TColon _ :: ys) =>
        -- Another key-value pair follows at same level
        succT $ blockMapAfterColon k2 (addOrMerge k v sv) m' ys r
      Succ0 (m', v) (B TNewline _ :: B (TAlias name) b :: B TColon _ :: ys) =>
        -- Alias as key at same level
        case lookup name m' of
          Just k2 => succT $ blockMapAfterColon k2 (addOrMerge k v sv) m' ys r
          Nothing => Fail0 (B (Custom (UndefinedAlias name)) b)
      Succ0 (m', v) (B TNewline _ :: B (TAnchor name) _ :: B (TScalar k2) _ :: B TColon _ :: ys) =>
        -- Anchor on scalar key at same level
        let m'' = insert name k2 m'
         in succT $ blockMapAfterColon k2 (addOrMerge k v sv) m'' ys r
      Succ0 (m', v) (B TNewline _ :: B TQuestion _ :: ys) =>
        -- Complex key follows at same level
        case succT $ value m' ys r of
          Succ0 (m'', k2) (B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (addOrMerge k v sv) m'' rest r
          Succ0 (m'', k2) (B TNewline _ :: B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (addOrMerge k v sv) m'' rest r
          Succ0 _ zs => fail zs
          Fail0 err => Fail0 err
      Succ0 (m', v) (B TNewline _ :: B TColon _ :: ys) =>
        -- Null key follows at same level
        succT $ blockMapAfterColon YNull (addOrMerge k v sv) m' ys r
      Succ0 (m', v) (B TNewline _ :: B TIndent _ :: B (TScalar k2) _ :: B TColon _ :: ys) =>
        -- Another key-value pair at nested level (compact notation: - key: val\n  key2: val2)
        succT $ blockMapAfterColon k2 (addOrMerge k v sv) m' ys r
      Succ0 (m', v) (B TNewline _ :: B TIndent _ :: B TQuestion _ :: ys) =>
        -- Complex key at nested level
        case succT $ value m' ys r of
          Succ0 (m'', k2) (B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (addOrMerge k v sv) m'' rest r
          Succ0 (m'', k2) (B TNewline _ :: B TColon _ :: rest) =>
            succT $ blockMapAfterColon k2 (addOrMerge k v sv) m'' rest r
          Succ0 _ zs => fail zs
          Fail0 err => Fail0 err
      -- After anchor+nested block: dedent followed by more keys at same level
      -- Only continue if value was a compound type (map/seq) - scalar values don't create dedents
      -- (e.g., "key: &anchor\n  nested\nsibling: val" - sibling is part of same map)
      Succ0 (m', v@(YMap _)) (B TNewline _ :: B TDedent _ :: B (TScalar k2) _ :: B TColon _ :: ys) =>
        succT $ blockMapAfterColon k2 (addOrMerge k v sv) m' ys r
      Succ0 (m', v@(YSeq _)) (B TNewline _ :: B TDedent _ :: B (TScalar k2) _ :: B TColon _ :: ys) =>
        succT $ blockMapAfterColon k2 (addOrMerge k v sv) m' ys r
      -- Null key after dedent from compound value
      Succ0 (m', v@(YMap _)) (B TNewline _ :: B TDedent _ :: B TColon _ :: ys) =>
        succT $ blockMapAfterColon YNull (addOrMerge k v sv) m' ys r
      Succ0 (m', v@(YSeq _)) (B TNewline _ :: B TDedent _ :: B TColon _ :: ys) =>
        succT $ blockMapAfterColon YNull (addOrMerge k v sv) m' ys r
      Succ0 (m', v) rest@(B TNewline _ :: B TDedent _ :: ys) =>
        -- End of this mapping level - leave TDedent for outer parser
        Succ0 (m', YMap $ toList (addOrMerge k v sv)) rest
      Succ0 (m', v) (B (TScalar k2) _ :: B TColon _ :: ys) =>
        -- After block scalar: key follows directly without TNewline
        -- (block scalar consumed the newline internally)
        succT $ blockMapAfterColon k2 (addOrMerge k v sv) m' ys r
      Succ0 (m', v) ys =>
        -- No more key-value pairs
        Succ0 (m', YMap $ toList (addOrMerge k v sv)) ys
      Fail0 err => Fail0 err

  value : RuleA True YAMLValue
  -- Anchor with null value (anchor followed by newline, NOT followed by indent)
  -- If followed by TNewline :: TIndent, it's a nested block value, not null
  value m (B (TAnchor name) _ :: xs@(B TNewline _ :: B TIndent _ :: _)) (SA r) =
    case succT $ value m xs r of
      Succ0 (m', v) ys => Succ0 (insert name v m', v) ys
      Fail0 err => Fail0 err
  value m (B (TAnchor name) _ :: xs@(B TNewline _ :: _)) _ =
    Succ0 (insert name YNull m, YNull) xs
  -- Anchor on scalar key: add anchor BEFORE parsing the mapping
  -- This makes the anchor available for the value and subsequent entries
  -- Must come BEFORE general anchor pattern for correct pattern matching
  value m (B (TAnchor name) _ :: B (TScalar k) _ :: B TColon _ :: xs) (SA r) =
    let m' = insert name k m
     in case succT $ blockMapAfterColon k empty m' xs r of
          Succ0 (m'', v) ys => Succ0 (m'', v) ys
          Fail0 err => Fail0 err
  -- Anchor: parse value, register in map, return both
  value m (B (TAnchor name) _ :: xs) (SA r) =
    case succT $ value m xs r of
      Succ0 (m', v) ys => Succ0 (insert name v m', v) ys
      Fail0 err => Fail0 err
  -- Alias: lookup in map, error if not found
  value m (B (TAlias name) b :: xs) _ =
    case lookup name m of
      Just v  => Succ0 (m, v) xs
      Nothing => Fail0 (B (Custom (UndefinedAlias name)) b)
  -- Nested block value (e.g., anchor before nested content: &ref\n  key: val)
  value m (B TNewline _ :: xs@(B TIndent _ :: _)) (SA r) =
    succT $ blockNestedValue m xs r
  -- Skip leading newline (e.g., after tag at document level: !!str\nhello)
  value m (B TNewline _ :: xs) (SA r) = succT $ value m xs r
  -- Tagged value: parse the tag, then the value, and apply the tag
  -- Tag followed by newline + indent = nested block content
  value m (B (TTag tag) _ :: B TNewline _ :: xs@(B TIndent _ :: _)) (SA r) =
    case succT $ blockNestedValue m xs r of
      Succ0 (m', v) ys => Succ0 (m', applyTag tag v) ys
      Fail0 err => Fail0 err
  -- Tag followed by newline (no indent) at document level (e.g., "--- !!str\nhello")
  value m (B (TTag tag) _ :: B TNewline _ :: xs) (SA r) =
    case succT $ value m xs r of
      Succ0 (m', v) ys => Succ0 (m', applyTag tag v) ys
      Fail0 err => Fail0 err
  -- In flow context: tag followed by flow indicator = empty tagged value
  value m (B (TTag tag) _ :: xs@(B TComma _ :: _)) _ =
    Succ0 (m, applyTag tag (YStr "")) xs
  value m (B (TTag tag) _ :: xs@(B TRBracket _ :: _)) _ =
    Succ0 (m, applyTag tag (YStr "")) xs
  value m (B (TTag tag) _ :: xs@(B TRBrace _ :: _)) _ =
    Succ0 (m, applyTag tag (YStr "")) xs
  -- In flow context: tag followed by colon = tagged empty value as key
  -- Leave colon for flow parser to handle as implicit key
  value m (B (TTag tag) _ :: xs@(B TColon _ :: _)) _ =
    Succ0 (m, applyTag tag (YStr "")) xs
  -- Tag with content on same line or nested
  value m (B (TTag tag) _ :: xs) (SA r) =
    case succT $ value m xs r of
      Succ0 (m', v) ys => Succ0 (m', applyTag tag v) ys
      Fail0 err => Fail0 err
  -- Block sequence: parse first dash, then delegate to blockSeqItems
  value m (B TDash _ :: xs) (SA r) = succT $ blockSeqItems [<] m xs r
  -- Complex key: ? key : value (allows any value type as key)
  value m (B TQuestion _ :: xs) (SA r) =
    case succT $ value m xs r of
      -- Colon immediately after key
      Succ0 (m', k) (B TColon _ :: rest) =>
        succT $ blockMapAfterColon k empty m' rest r
      -- Colon on next line after key
      Succ0 (m', k) (B TNewline _ :: B TColon _ :: rest) =>
        succT $ blockMapAfterColon k empty m' rest r
      -- Missing colon after complex key
      Succ0 _ ys => fail ys
      Fail0 err => Fail0 err
  -- Null key mapping: colon without preceding key (implicit null key)
  value m (B TColon _ :: xs) (SA r) = succT $ blockMapAfterColon YNull empty m xs r
  -- In flow context: scalar followed by colon then flow indicator - return scalar, leave colon
  -- This allows flowSeq/flowMap to handle the implicit key pattern
  value m (B (TScalar k) _ :: xs@(B TColon _ :: B TComma _ :: _)) _ = Succ0 (m, k) xs
  value m (B (TScalar k) _ :: xs@(B TColon _ :: B TRBracket _ :: _)) _ = Succ0 (m, k) xs
  value m (B (TScalar k) _ :: xs@(B TColon _ :: B TRBrace _ :: _)) _ = Succ0 (m, k) xs
  -- Block mapping: scalar followed by colon, delegate to blockMapAfterColon
  value m (B (TScalar k) _ :: B TColon _ :: xs) (SA r) = succT $ blockMapAfterColon k empty m xs r
  -- Plain scalar value
  value m (B (TScalar v) _ :: xs) _ = Succ0 (m, v) xs
  value m (B TLBracket b :: B TRBracket _ :: xs) _ = Succ0 (m, YSeq []) xs
  value m (B TLBracket b :: xs) (SA r) = succT $ flowSeq b [<] m xs r
  value m (B TLBrace b :: B TRBrace _ :: xs) _ = Succ0 (m, YMap []) xs
  value m (B TLBrace b :: xs) (SA r) = succT $ flowMap b empty m xs r
  value m xs _ = fail xs

  -- Handle trailing comma: if first token is ], we're done
  flowSeq b sv m (B TRBracket _ :: xs) _ = Succ0 (m, YSeq $ sv <>> []) xs
  flowSeq b sv m xs acc@(SA r) = case value m xs acc of
    -- Implicit key: value followed by colon becomes single-pair map
    Succ0 (m', k) (B TColon _ :: ys) =>
      case ys of
        -- Null value: [key:, ...] or [key:]
        (B TComma _ :: zs)    => succT $ flowSeq b (sv :< YMap [(k, YNull)]) m' zs r
        (B TRBracket _ :: zs) => Succ0 (m', YSeq $ sv <>> [YMap [(k, YNull)]]) zs
        -- Parse value after colon
        _ => case succT $ value m' ys r of
          Succ0 (m'', v) (B TComma _ :: zs)    =>
            succT $ flowSeq b (sv :< YMap [(k, v)]) m'' zs r
          Succ0 (m'', v) (B TRBracket _ :: zs) =>
            Succ0 (m'', YSeq $ sv <>> [YMap [(k, v)]]) zs
          Succ0 _ (B TEOI _ :: _)              => unclosed b TLBracket
          Succ0 _ (z :: _)                     => unexpected z
          Succ0 _ []                           => unclosed b TLBracket
          Fail0 err                            => Fail0 err
    -- Regular sequence elements
    Succ0 (m', v) (B TComma _ :: ys)    => succT $ flowSeq b (sv :< v) m' ys r
    Succ0 (m', v) (B TRBracket _ :: ys) => Succ0 (m', YSeq $ sv <>> [v]) ys
    Succ0 _ (B TEOI _ :: _)             => unclosed b TLBracket
    Fail0 (B (Expected [] "end of input") _) => unclosed b TLBracket
    Succ0 _ (y :: ys)                   => unexpected y
    Succ0 _ []                          => unclosed b TLBracket
    Fail0 err                           => Fail0 err

  -- Handle trailing comma: if first token is }, we're done
  flowMap b sv m (B TRBrace _ :: xs) _ = Succ0 (m, YMap $ toList sv) xs
  -- Complex key with plain scalar: {? foo: value} or {? foo :,}
  -- Must handle this before general complex key to prevent value from starting block map
  flowMap b sv m (B TQuestion _ :: B (TScalar k) _ :: B TColon _ :: rest) (SA r) =
    succT $ flowMapAfterColon b sv k m rest r
  -- Complex key in flow mapping: {? key: value}
  flowMap b sv m (B TQuestion _ :: xs) (SA r) =
    case succT $ value m xs r of
      Succ0 (m', k) (B TColon _ :: rest) =>
        case rest of
          -- Null value after complex key: { ? foo :, }
          (B TComma _ :: ys)  => succT $ flowMap b (addOrMerge k YNull sv) m' ys r
          (B TRBrace _ :: ys) => Succ0 (m', YMap $ toList (addOrMerge k YNull sv)) ys
          _ => case succT $ value m' rest r of
            Succ0 (m'', v) (B TComma _ :: ys)  => succT $ flowMap b (addOrMerge k v sv) m'' ys r
            Succ0 (m'', v) (B TRBrace _ :: ys) => Succ0 (m'', YMap $ toList (addOrMerge k v sv)) ys
            Succ0 _ (B TEOI _ :: _)            => unclosed b TLBrace
            Fail0 (B (Expected [] "end of input") _) => unclosed b TLBrace
            Succ0 _ (y :: ys)                  => unexpected y
            Succ0 _ []                         => unclosed b TLBrace
            Fail0 err                          => Fail0 err
      Succ0 _ ys => fail ys  -- Missing colon after complex key
      Fail0 err => Fail0 err
  -- Null key with null value: { :, } or { : }
  flowMap b sv m (B TColon _ :: B TComma _ :: xs) (SA r) =
    succT $ flowMap b (addOrMerge YNull YNull sv) m xs r
  flowMap b sv m (B TColon _ :: B TRBrace _ :: xs) _ =
    Succ0 (m, YMap $ toList (addOrMerge YNull YNull sv)) xs
  -- Null key: { : value }
  flowMap b sv m (B TColon _ :: xs) (SA r) =
    case succT $ value m xs r of
      Succ0 (m', v) (B TComma _ :: ys)  => succT $ flowMap b (addOrMerge YNull v sv) m' ys r
      Succ0 (m', v) (B TRBrace _ :: ys) => Succ0 (m', YMap $ toList (addOrMerge YNull v sv)) ys
      Succ0 _ (B TEOI _ :: _)           => unclosed b TLBrace
      Fail0 (B (Expected [] "end of input") _) => unclosed b TLBrace
      Succ0 _ (y :: ys)                 => unexpected y
      Succ0 _ []                        => unclosed b TLBrace
      Fail0 err                         => Fail0 err
  -- Tag as key: { !!str : bar }
  flowMap b sv m (B (TTag tag) _ :: B TColon _ :: xs) (SA r) =
    let k = applyTag tag (YStr "") in succT $ flowMapAfterColon b sv k m xs r
  -- Alias as key: { *alias : value }
  flowMap b sv m (B (TAlias name) bb :: B TColon _ :: xs) (SA r) =
    case lookup name m of
      Just k  => succT $ flowMapAfterColon b sv k m xs r
      Nothing => Fail0 (B (Custom (UndefinedAlias name)) bb)
  -- Anchor on scalar key: { &a foo : value }
  flowMap b sv m (B (TAnchor name) _ :: B (TScalar k) _ :: B TColon _ :: xs) (SA r) =
    let m' = insert name k m
    in succT $ flowMapAfterColon b sv k m' xs r
  flowMap b sv m (B (TScalar k) _ :: B TColon _ :: xs) (SA r) =
    succT $ flowMapAfterColon b sv k m xs r
  -- Scalar followed by comma = implicit key with null value
  flowMap b sv m (B (TScalar k) _ :: B TComma _ :: xs) (SA r) =
    succT $ flowMap b (addOrMerge k YNull sv) m xs r
  -- Scalar followed by } = implicit key with null value (last entry)
  flowMap b sv m (B (TScalar k) _ :: B TRBrace _ :: xs) _ =
    Succ0 (m, YMap $ toList (addOrMerge k YNull sv)) xs
  flowMap b sv m (B (TScalar _) _ :: x :: xs) _ = expected x.bounds "':'" "\{x.val}"
  flowMap b sv m (x :: xs) _ = expected x.bounds "key" "\{x.val}"
  flowMap b sv m [] _ = eoi

  -- Parse value after colon in flow map, handling null values (comma/brace = null)
  flowMapAfterColon : Bounds -> MapAcc -> YAMLValue -> RuleA True YAMLValue
  flowMapAfterColon b sv k m (B TComma _ :: xs) (SA r) =
    succT $ flowMap b (addOrMerge k YNull sv) m xs r
  -- RBrace after colon = null value, end of map
  flowMapAfterColon b sv k m (B TRBrace _ :: xs) _ =
    Succ0 (m, YMap $ toList (addOrMerge k YNull sv)) xs
  -- Otherwise parse value (use full list with matching suffix proof)
  flowMapAfterColon b sv k m xs@(_ :: _) acc@(SA r) =
    case value m xs acc of
      Succ0 (m', v) (B TComma _ :: ys)  => succT $ flowMap b (addOrMerge k v sv) m' ys r
      Succ0 (m', v) (B TRBrace _ :: ys) => Succ0 (m', YMap $ toList (addOrMerge k v sv)) ys
      Succ0 _ (B TEOI _ :: _)           => unclosed b TLBrace
      Fail0 (B (Expected [] "end of input") _) => unclosed b TLBrace
      Succ0 _ (y :: ys)                 => unexpected y
      Succ0 _ []                        => unclosed b TLBrace
      Fail0 err                         => Fail0 err
  -- Empty input
  flowMapAfterColon b sv k m [] _ = unclosed b TLBrace

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
    -- Each document starts with a fresh empty anchor map
    go sx ts (SA r) = case value empty ts (SA r) of
      Fail0 err => Left (toParseError o str err)
      Succ0 (_, v) [] => Right (sx :< v)
      Succ0 (_, v) [B TEOI _] => Right (sx :< v)
      Succ0 (_, v) (B TNewline _ :: ts2) => go (sx :< v) ts2 r
      Succ0 (_, v) (B TDedent _ :: ts2) => go (sx :< v) ts2 r
      Succ0 (_, v) (B TDocEnd _ :: ts2) => go (sx :< v) ts2 r
      Succ0 (_, v) (B TDocStart _ :: ts2) => go (sx :< v) ts2 r
      Succ0 (_, v) ts2 => go (sx :< v) ts2 r

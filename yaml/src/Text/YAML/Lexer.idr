module Text.YAML.Lexer

import Data.List
import Data.List1
import Data.List.Suffix
import Data.SnocList
import Data.String
import Text.Parse.Manual
import Text.Time.Lexer
import Text.YAML.Types

%default total

--------------------------------------------------------------------------------
--          Lexer State
--------------------------------------------------------------------------------

||| Flow context tracking: how deep are we in flow collections?
public export
data FlowCtxt : Type where
  ||| Not in a flow context (block mode)
  NoFlow   : FlowCtxt
  ||| In a flow collection at given depth
  InFlow   : Nat -> FlowCtxt

||| Chomping behavior for block scalars
data Chomping = Strip | Clip | Keep

--------------------------------------------------------------------------------
--          String Literals
--------------------------------------------------------------------------------

||| Valid YAML control characters that need escaping
yamlControl : Char -> Bool
yamlControl '\n' = True
yamlControl '\r' = True
yamlControl '\t' = True
yamlControl x    = x < ' '

||| Check if all characters in a list are hex digits
allHex : List Char -> Bool
allHex = all isHexDigit

||| Convert a list of hex digit characters to a Char (unicode codepoint)
||| Converts hex chars to Nat (the codepoint value), then casts to Char
hexChar : List Char -> Char
hexChar = cast . foldl (\acc, c => acc * 16 + hexDigit c) 0

||| Read a double-quoted string with escape sequences
dqString : SnocList Char -> AutoTok e String
dqString sc ('\\' :: esc :: xs) = case esc of
  '"'  => dqString (sc :< '"') xs
  '\\' => dqString (sc :< '\\') xs
  '/'  => dqString (sc :< '/') xs
  'n'  => dqString (sc :< '\n') xs
  'r'  => dqString (sc :< '\r') xs
  't'  => dqString (sc :< '\t') xs
  'b'  => dqString (sc :< '\b') xs
  'f'  => dqString (sc :< '\f') xs
  '0'  => dqString (sc :< '\0') xs
  ' '  => dqString (sc :< ' ') xs
  'a'  => dqString (sc :< '\x07') xs   -- Bell
  'v'  => dqString (sc :< '\x0B') xs   -- Vertical tab
  'e'  => dqString (sc :< '\x1B') xs   -- Escape
  '_'  => dqString (sc :< '\xA0') xs   -- Non-breaking space
  'N'  => dqString (sc :< '\x85') xs   -- Next line
  'L'  => dqString (sc :< '\x2028') xs -- Line separator
  'P'  => dqString (sc :< '\x2029') xs -- Paragraph separator
  'x'  => case xs of
    a :: b :: t =>
      if allHex [a, b]
        then dqString (sc :< hexChar [a, b]) t
        else invalidEscape p t
    _ => invalidEscape p xs
  'u'  => case xs of
    a :: b :: c :: d :: t =>
      if allHex [a, b, c, d]
        then dqString (sc :< hexChar [a, b, c, d]) t
        else invalidEscape p t
    _ => invalidEscape p xs
  'U'  => case xs of
    a :: b :: c :: d :: e :: f :: g :: h :: t =>
      if allHex [a, b, c, d, e, f, g, h]
        then dqString (sc :< hexChar [a, b, c, d, e, f, g, h]) t
        else invalidEscape p t
    _ => invalidEscape p xs
  _    => invalidEscape p xs
dqString sc ('"' :: xs) = Succ (cast sc) xs
dqString sc (c :: xs)   =
  if yamlControl c && c /= '\t'
    then range (InvalidControl c) p xs
    else dqString (sc :< c) xs
dqString sc []          = eoiAt p

||| Read a single-quoted string (only '' escapes to ')
sqString : SnocList Char -> AutoTok e String
sqString sc ('\'' :: '\'' :: xs) = sqString (sc :< '\'') xs
sqString sc ('\'' :: xs)         = Succ (cast sc) xs
sqString sc (c :: xs)            =
  if yamlControl c && c /= '\t' && c /= '\n'
    then range (InvalidControl c) p xs
    else sqString (sc :< c) xs
sqString sc []                   = eoiAt p

--------------------------------------------------------------------------------
--          Plain Scalars
--------------------------------------------------------------------------------

rtrimLine : SnocList Char -> SnocList Char
rtrimLine [<]          = [<]
rtrimLine (sx :< ' ')  = rtrimLine sx
rtrimLine (sx :< '\t') = rtrimLine sx
rtrimLine sx           = sx

||| Check if a line starts with a block indicator (- or : followed by whitespace)
||| These indicate a new block structure, not a plain scalar continuation
lineStartsWithBlockIndicator : List Char -> Bool
lineStartsWithBlockIndicator ('-' :: ' ' :: _) = True
lineStartsWithBlockIndicator ('-' :: '\t' :: _) = True
lineStartsWithBlockIndicator ('-' :: '\n' :: _) = True
lineStartsWithBlockIndicator ('-' :: '\r' :: _) = True
lineStartsWithBlockIndicator ('-' :: []) = True
lineStartsWithBlockIndicator _ = False

||| Check if a line contains a mapping indicator (: followed by whitespace/EOL)
||| This is used to disambiguate multi-line plain scalars from new mapping entries
lineHasMappingIndicator : List Char -> Bool
lineHasMappingIndicator [] = False
lineHasMappingIndicator ('\n' :: _) = False
lineHasMappingIndicator ('\r' :: _) = False
lineHasMappingIndicator ('#' :: _) = False  -- Comment, not content
lineHasMappingIndicator (':' :: []) = True
lineHasMappingIndicator (':' :: ' ' :: _) = True
lineHasMappingIndicator (':' :: '\t' :: _) = True
lineHasMappingIndicator (':' :: '\n' :: _) = True
lineHasMappingIndicator (':' :: '\r' :: _) = True
lineHasMappingIndicator (_ :: xs) = lineHasMappingIndicator xs

||| Characters that always terminate a plain scalar in block context
isPlainEndBlock : Char -> Bool
isPlainEndBlock '#' = True
isPlainEndBlock '\n' = True
isPlainEndBlock '\r' = True
isPlainEndBlock _   = False

||| Characters that always terminate a plain scalar in flow context
isPlainEndFlow : Char -> Bool
isPlainEndFlow ','  = True
isPlainEndFlow '['  = True
isPlainEndFlow ']'  = True
isPlainEndFlow '{'  = True
isPlainEndFlow '}'  = True
isPlainEndFlow c    = isPlainEndBlock c

||| Count leading spaces and return count with remaining chars (single pass)
countAndSkipSpaces : Nat -> List Char -> (Nat, List Char)
countAndSkipSpaces n (' ' :: xs) = countAndSkipSpaces (S n) xs
countAndSkipSpaces n xs = (n, xs)

||| Check if we should continue plain scalar on next line
||| Returns True if: more indented AND no block indicator at start AND no mapping indicator on line
shouldContinuePlain : (baseIndent : Nat) -> List Char -> Bool
shouldContinuePlain bi xs =
  let (spaces, rest) = countAndSkipSpaces 0 xs
   in spaces > bi
      && not (lineStartsWithBlockIndicator rest)
      && not (lineHasMappingIndicator rest)

||| Check if next line is blank (only spaces then newline)
isBlankLine : List Char -> Bool
isBlankLine [] = True
isBlankLine ('\n' :: _) = True
isBlankLine ('\r' :: '\n' :: _) = True
isBlankLine (' ' :: xs) = isBlankLine xs
isBlankLine _ = False

mutual
  ||| Continue reading plain scalar after deciding to continue
  ||| Called when we've determined the next line is a continuation
  plainScalarContinue :
       (baseIndent : Nat)
    -> SnocList Char
    -> AutoTok e String
  -- Count and skip spaces, then continue reading content
  plainScalarContinue bi sc (' ' :: xs) = plainScalarContinue bi sc xs
  -- Now at content - continue reading with fold (space already added to sc)
  plainScalarContinue bi sc xs = plainScalarBlockMulti bi sc xs

  ||| Handle blank line in plain scalar (preserve newline, then continue on next content line)
  ||| After the blank line, skip leading spaces and continue
  plainScalarBlankLine :
       (baseIndent : Nat)
    -> SnocList Char
    -> AutoTok e String
  plainScalarBlankLine bi sc (' ' :: xs) = plainScalarBlankLine bi sc xs
  -- Reached next newline (possibly another blank line) - add newline and recurse
  plainScalarBlankLine bi sc ('\n' :: xs) =
    if isBlankLine xs
      then plainScalarBlankLine bi (sc :< '\n') xs
      else if shouldContinuePlain bi xs
        then plainScalarContinue bi (sc :< '\n') xs  -- Add newline for blank, then continue
        else Succ (cast $ rtrimLine sc) ('\n' :: xs)  -- End scalar
  plainScalarBlankLine bi sc ('\r' :: '\n' :: xs) =
    if isBlankLine xs
      then plainScalarBlankLine bi (sc :< '\n') xs
      else if shouldContinuePlain bi xs
        then plainScalarContinue bi (sc :< '\n') xs
        else Succ (cast $ rtrimLine sc) ('\r' :: '\n' :: xs)
  plainScalarBlankLine bi sc xs = plainScalarBlockMulti bi sc xs  -- Content found after spaces

  ||| Read a plain (unquoted) scalar in block context (multi-line aware)
  ||| baseIndent is the column where the scalar started
  plainScalarBlockMulti : (baseIndent : Nat) -> SnocList Char -> AutoTok e String
  -- Colon followed by whitespace/EOF = mapping indicator, end scalar
  plainScalarBlockMulti bi sc (':' :: ' ' :: xs)  = Succ (cast $ rtrimLine sc) (':' :: ' ' :: xs)
  plainScalarBlockMulti bi sc (':' :: '\t' :: xs) = Succ (cast $ rtrimLine sc) (':' :: '\t' :: xs)
  plainScalarBlockMulti bi sc (':' :: '\n' :: xs) = Succ (cast $ rtrimLine sc) (':' :: '\n' :: xs)
  plainScalarBlockMulti bi sc (':' :: '\r' :: xs) = Succ (cast $ rtrimLine sc) (':' :: '\r' :: xs)
  plainScalarBlockMulti bi sc [':']               = Succ (cast $ rtrimLine sc) [':']
  -- Colon followed by other char = part of the scalar
  plainScalarBlockMulti bi sc (':' :: xs)         = plainScalarBlockMulti bi (sc :< ':') xs
  -- Newline: check for continuation using non-consuming lookahead
  plainScalarBlockMulti bi sc ('\n' :: xs) =
    if isBlankLine xs
      then plainScalarBlankLine bi sc xs  -- Handle blank line
      else if shouldContinuePlain bi xs
        then plainScalarContinue bi (rtrimLine sc :< ' ') xs  -- Fold newline to space
        else Succ (cast $ rtrimLine sc) ('\n' :: xs)  -- End scalar, return WITH newline
  plainScalarBlockMulti bi sc ('\r' :: '\n' :: xs) =
    if isBlankLine xs
      then plainScalarBlankLine bi sc xs
      else if shouldContinuePlain bi xs
        then plainScalarContinue bi (rtrimLine sc :< ' ') xs
        else Succ (cast $ rtrimLine sc) ('\r' :: '\n' :: xs)
  -- Comment or other line-ending chars
  plainScalarBlockMulti bi sc (c :: xs) =
    if isPlainEndBlock c
      then Succ (cast $ rtrimLine sc) (c :: xs)
      else plainScalarBlockMulti bi (sc :< c) xs
  plainScalarBlockMulti bi sc [] = Succ (cast $ rtrimLine sc) []

||| Read a plain (unquoted) scalar in flow context
||| In flow context, : always ends the scalar (mapping indicator)
plainScalarFlow : SnocList Char -> AutoTok e String
plainScalarFlow sc (':' :: xs) = Succ (cast $ rtrimLine sc) (':' :: xs)
plainScalarFlow sc (c :: xs) =
  if isPlainEndFlow c
    then Succ (cast $ rtrimLine sc) (c :: xs)
    else plainScalarFlow (sc :< c) xs
plainScalarFlow sc [] = Succ (cast $ rtrimLine sc) []

--------------------------------------------------------------------------------
--          Block Scalars
--------------------------------------------------------------------------------

||| Strip trailing empty strings from SnocList, returning count removed
stripTrailingEmpty : SnocList String -> (SnocList String, Nat)
stripTrailingEmpty [<] = ([<], 0)
stripTrailingEmpty (sx :< "") = let (sx', n) = stripTrailingEmpty sx in (sx', S n)
stripTrailingEmpty sx = (sx, 0)

||| Apply chomping to produce final block scalar content
finalizeContent : Chomping -> (trailingCount : Nat) -> (content : String) -> String
finalizeContent Strip _ content = content
finalizeContent Clip  _ "" = ""
finalizeContent Clip  _ content = content ++ "\n"
finalizeContent Keep  n "" = pack $ replicate n '\n'
finalizeContent Keep  n content = content ++ pack (replicate (S n) '\n')

||| Apply chomping to literal block scalar lines
applyChomping : Chomping -> SnocList String -> String
applyChomping chomp lines =
  let (stripped, trailingCount) = stripTrailingEmpty lines
      content = concat $ intersperse "\n" (stripped <>> [])
   in finalizeContent chomp trailingCount content

||| Check if a line has more indentation (for folded scalars)
isMoreIndented : String -> Bool
isMoreIndented s = case unpack s of
  (' ' :: _) => True
  _          => False

||| Fold lines for folded block scalar (tail-recursive with accumulator)
||| Returns folded content WITHOUT trailing newline (caller adds based on chomping)
foldLines : List String -> String
foldLines = go [<]
  where
    -- Append string chars to SnocList
    appendStr : SnocList Char -> String -> SnocList Char
    appendStr acc s = foldl (:<) acc (unpack s)

    go : SnocList Char -> List String -> String
    go acc [] = cast acc
    go acc [x] = cast (appendStr acc x)
    go acc (x :: y :: rest) =
      let accX = appendStr acc x
          sep = if x == "" || isMoreIndented x || isMoreIndented y || y == ""
                  then '\n'
                  else ' '
       in go (accX :< sep) (y :: rest)

||| Apply folding and chomping to folded block scalar lines
applyFolded : Chomping -> SnocList String -> String
applyFolded chomp lines =
  let (stripped, trailingCount) = stripTrailingEmpty lines
      content = foldLines (stripped <>> [])
   in finalizeContent chomp trailingCount content

mutual
  ||| Block scalar content collection - structural recursion on input list
  ||| State: folded?, chomping, content indent, current line spaces, current line content, completed lines
  blockContent :
       (folded : Bool)
    -> Chomping
    -> (contentIndent : Nat)
    -> (lineSpaces : Nat)
    -> (currentLine : SnocList Char)
    -> (lines : SnocList String)
    -> AutoTok e String
  -- End of input
  blockContent folded chomp ci ls cl lines [] =
    -- Only add current line if there's content, or we have valid indentation with content
    let finalLines = if cl /= [<]
                       then lines :< (replicate (minus ls ci) ' ' ++ cast cl)
                       else lines
        result = if folded then applyFolded chomp finalLines else applyChomping chomp finalLines
     in Succ result []
  -- Counting leading spaces at start of line
  blockContent folded chomp ci ls [<] lines (' ' :: xs) =
    blockContent folded chomp ci (S ls) [<] lines xs
  -- Newline while counting spaces (blank line)
  blockContent folded chomp ci ls [<] lines ('\n' :: xs) =
    blockContent folded chomp ci 0 [<] (lines :< "") xs
  blockContent folded chomp ci ls [<] lines ('\r' :: '\n' :: xs) =
    blockContent folded chomp ci 0 [<] (lines :< "") xs
  -- First non-space char - check indentation (sufficient)
  blockContent folded chomp ci ls [<] lines (c :: xs) =
    if ls >= ci
      then blockContent folded chomp ci ls [< c] lines xs  -- Continue reading line
      else -- Dedent: end of block scalar, return with char unconsumed
        let result = if folded then applyFolded chomp lines else applyChomping chomp lines
         in Succ result (c :: xs)
  -- Reading line content - newline ends the line
  blockContent folded chomp ci ls cl lines ('\n' :: xs) =
    blockContent folded chomp ci 0 [<] (lines :< (replicate (minus ls ci) ' ' ++ cast cl)) xs
  blockContent folded chomp ci ls cl lines ('\r' :: '\n' :: xs) =
    blockContent folded chomp ci 0 [<] (lines :< (replicate (minus ls ci) ' ' ++ cast cl)) xs
  -- Regular character in line content
  blockContent folded chomp ci ls cl lines (c :: xs) =
    blockContent folded chomp ci ls (cl :< c) lines xs

  ||| Auto-detect content indentation from first non-empty line
  ||| Block scalar content must have at least 1 space of indentation
  blockDetectIndent : (folded : Bool) -> Chomping -> (spaces : Nat) -> AutoTok e String
  blockDetectIndent folded chomp n (' ' :: xs) = blockDetectIndent folded chomp (S n) xs
  blockDetectIndent folded chomp n ('\n' :: xs) = blockDetectIndent folded chomp 0 xs
  blockDetectIndent folded chomp n ('\r' :: '\n' :: xs) = blockDetectIndent folded chomp 0 xs
  blockDetectIndent folded chomp n [] = Succ "" []  -- Empty block scalar
  blockDetectIndent folded chomp Z (c :: xs) =
    -- Zero indentation means end of block scalar (content must be indented)
    let result = if folded then applyFolded chomp [<] else applyChomping chomp [<]
     in Succ result (c :: xs)
  blockDetectIndent folded chomp n@(S _) (c :: xs) =
    -- n > 0, this is the content indent, start reading content
    blockContent folded chomp n n [< c] [<] xs

  ||| Skip rest of header line (after indicators)
  skipHeader : (folded : Bool) -> Chomping -> (explicitIndent : Maybe Nat) -> AutoTok e String
  -- Newline - start content with auto-detect or explicit indent
  skipHeader folded chomp (Just ci) ('\n' :: xs) =
    blockContent folded chomp ci 0 [<] [<] xs
  skipHeader folded chomp Nothing ('\n' :: xs) =
    blockDetectIndent folded chomp 0 xs
  skipHeader folded chomp mi ('\r' :: '\n' :: xs) =
    skipHeader folded chomp mi ('\n' :: xs)
  -- Skip spaces and comments until newline
  skipHeader folded chomp mi (' ' :: xs) = skipHeader folded chomp mi xs
  skipHeader folded chomp mi ('\t' :: xs) = skipHeader folded chomp mi xs
  skipHeader folded chomp mi ('#' :: xs) = skipHeaderComment folded chomp mi xs
  skipHeader folded chomp mi (_ :: xs) = skipHeader folded chomp mi xs
  skipHeader folded chomp _ [] =
    let result = if folded then applyFolded chomp [<] else applyChomping chomp [<]
     in Succ result []

  ||| Skip comment in header line
  skipHeaderComment : (folded : Bool) -> Chomping -> Maybe Nat -> AutoTok e String
  skipHeaderComment folded chomp mi ('\n' :: xs) = skipHeader folded chomp mi ('\n' :: xs)
  skipHeaderComment folded chomp mi ('\r' :: '\n' :: xs) = skipHeader folded chomp mi ('\r' :: '\n' :: xs)
  skipHeaderComment folded chomp mi (_ :: xs) = skipHeaderComment folded chomp mi xs
  skipHeaderComment folded chomp _ [] =
    let result = if folded then applyFolded chomp [<] else applyChomping chomp [<]
     in Succ result []

  ||| Continue after optional indentation indicator
  blockScalarWithChompIndent : (folded : Bool) -> Chomping -> Maybe Nat -> AutoTok e String
  blockScalarWithChompIndent folded Clip mi ('-' :: xs) = skipHeader folded Strip mi xs
  blockScalarWithChompIndent folded Clip mi ('+' :: xs) = skipHeader folded Keep mi xs
  blockScalarWithChompIndent folded chomp mi xs = skipHeader folded chomp mi xs

  ||| Continue parsing after chomping indicator
  blockScalarWithChomp : (folded : Bool) -> Chomping -> AutoTok e String
  blockScalarWithChomp folded chomp (c :: xs) =
    if c >= '1' && c <= '9'
      then let indent = cast {to=Nat} (ord c - ord '0')
            in blockScalarWithChompIndent folded chomp (Just indent) xs
      else blockScalarWithChompIndent folded chomp Nothing (c :: xs)
  blockScalarWithChomp folded chomp [] =
    blockScalarWithChompIndent folded chomp Nothing []

  ||| Parse block scalar header and start content collection
  ||| folded: True for '>', False for '|'
  blockScalar : (folded : Bool) -> AutoTok e String
  blockScalar folded ('-' :: xs) = blockScalarWithChomp folded Strip xs
  blockScalar folded ('+' :: xs) = blockScalarWithChomp folded Keep xs
  blockScalar folded xs = blockScalarWithChomp folded Clip xs

--------------------------------------------------------------------------------
--          Scalar Value Interpretation
--------------------------------------------------------------------------------

||| Try to parse YAML-specific integer formats (hex, octal)
||| Standard decimal integers are handled by `tryNumber`
export
tryYamlInteger : String -> Maybe Integer
tryYamlInteger s = case unpack s of
  '0' :: 'x' :: rest => case tok (hex {e=()}) rest of
    Succ n [] => Just (cast n)
    _         => Nothing
  '0' :: 'o' :: rest => case tok (oct {e=()}) rest of
    Succ n [] => Just (cast n)
    _         => Nothing
  _                  => Nothing

||| Try to parse an ISO 8601 timestamp
tryTimestamp : String -> Maybe AnyTime
tryTimestamp s =
  let cs : List Char = unpack s
  in case anyTime {e=()} {orig=cs} cs @{Same} of
    Succ v [] => Just v
    _         => Nothing

||| Try to parse a standard numeric value using the `number` shifter.
||| Returns Just if the entire string is a valid number, Nothing otherwise.
export
tryNumber : String -> Maybe YAMLValue
tryNumber s =
  let cs = unpack s
   in case number [<] cs of
        Succ [] => -- Consumed all characters, it's a valid number
          if any (\c => c == '.' || c == 'e' || c == 'E') cs
            then Just (YFloat (cast s))
            else Just (YInt (cast s))
        _ => Nothing -- Either failed or didn't consume all

||| Interpret a plain scalar string as a YAML value
interpretScalar : String -> YAMLValue
-- Null values
interpretScalar "" = YNull
interpretScalar "~" = YNull
interpretScalar "null" = YNull
interpretScalar "Null" = YNull
interpretScalar "NULL" = YNull
-- Boolean values
interpretScalar "true" = YBool True
interpretScalar "True" = YBool True
interpretScalar "TRUE" = YBool True
interpretScalar "false" = YBool False
interpretScalar "False" = YBool False
interpretScalar "FALSE" = YBool False
-- Special float values (YAML-specific)
interpretScalar ".nan" = YFloat (0.0 / 0.0)
interpretScalar ".NaN" = YFloat (0.0 / 0.0)
interpretScalar ".NAN" = YFloat (0.0 / 0.0)
interpretScalar ".inf" = YFloat (1.0 / 0.0)
interpretScalar ".Inf" = YFloat (1.0 / 0.0)
interpretScalar ".INF" = YFloat (1.0 / 0.0)
interpretScalar "+.inf" = YFloat (1.0 / 0.0)
interpretScalar "+.Inf" = YFloat (1.0 / 0.0)
interpretScalar "+.INF" = YFloat (1.0 / 0.0)
interpretScalar "-.inf" = YFloat (negate $ 1.0 / 0.0)
interpretScalar "-.Inf" = YFloat (negate $ 1.0 / 0.0)
interpretScalar "-.INF" = YFloat (negate $ 1.0 / 0.0)
-- Numeric values and timestamps
interpretScalar s = case tryYamlInteger s of
  Just i  => YInt i
  Nothing => case tryNumber s of
    Just v  => v
    Nothing => case tryTimestamp s of
      Just t  => YTime t
      Nothing => YStr s

--------------------------------------------------------------------------------
--          Tags
--------------------------------------------------------------------------------

||| Valid characters in a tag name (simplified - alphanumeric, -, _)
isTagChar : Char -> Bool
isTagChar c = isAlphaNum c || c == '-' || c == '_' || c == '.'

||| Read tag characters
tagChars : SnocList Char -> AutoTok e String
tagChars sc (c :: xs) =
  if isTagChar c
    then tagChars (sc :< c) xs
    else Succ (cast sc) (c :: xs)
tagChars sc [] = Succ (cast sc) []

||| Lex a verbatim tag: !<uri>
||| Read until closing >
verbatimTag : SnocList Char -> AutoTok e String
verbatimTag sc ('>' :: xs) = Succ (cast sc) xs
verbatimTag sc (c :: xs) = verbatimTag (sc :< c) xs
verbatimTag sc [] = eoiAt p  -- Unclosed verbatim tag

||| Lex a tag token
||| Formats: !name, !!name, !<uri>
lexTag : AutoTok e YAMLToken
-- Verbatim tag: !<uri>
lexTag ('<' :: xs) = TTag <$> verbatimTag [<] xs
-- Core schema tag: !!name
lexTag ('!' :: xs) = TTag . ("!" ++) <$> tagChars [<] xs
-- Local tag: !name
lexTag xs = TTag <$> tagChars [<] xs

--------------------------------------------------------------------------------
--          Directives
--------------------------------------------------------------------------------

||| Read directive name (alphanumeric)
directiveName : SnocList Char -> AutoTok e String
directiveName sc (c :: xs) =
  if isAlpha c || isDigit c
    then directiveName (sc :< c) xs
    else Succ (cast sc) (c :: xs)
directiveName sc [] = Succ (cast sc) []

||| Read directive value (rest of line, trimmed)
directiveValue : SnocList Char -> AutoTok e String
directiveValue sc ('\n' :: xs) = Succ (cast $ rtrimLine sc) ('\n' :: xs)
directiveValue sc ('\r' :: '\n' :: xs) = Succ (cast $ rtrimLine sc) ('\r' :: '\n' :: xs)
directiveValue sc (c :: xs) = directiveValue (sc :< c) xs
directiveValue sc [] = Succ (cast $ rtrimLine sc) []

||| Lex a directive: %NAME value
lexDirective : AutoTok e YAMLToken
lexDirective xs = case directiveName [<] xs of
  Succ name (' ' :: rest) => TDirective name <$> directiveValue [<] rest
  Succ name rest          => Succ (TDirective name "") rest
  Fail s e err            => Fail s e err

--------------------------------------------------------------------------------
--          Token Lexing
--------------------------------------------------------------------------------

||| Lex a single token in block context
||| Takes the current block indentation level for multi-line plain scalar handling
blockTok : (blockIndent : Nat) -> Tok True e YAMLToken
-- Document markers (must come before dash handling)
blockTok bi ('-' :: '-' :: '-' :: ' ' :: xs)  = Succ TDocStart (' ' :: xs)
blockTok bi ('-' :: '-' :: '-' :: '\n' :: xs) = Succ TDocStart ('\n' :: xs)
blockTok bi ('-' :: '-' :: '-' :: '\r' :: xs) = Succ TDocStart ('\r' :: xs)
blockTok bi ('-' :: '-' :: '-' :: [])         = Succ TDocStart []
blockTok bi ('.' :: '.' :: '.' :: ' ' :: xs)  = Succ TDocEnd (' ' :: xs)
blockTok bi ('.' :: '.' :: '.' :: '\n' :: xs) = Succ TDocEnd ('\n' :: xs)
blockTok bi ('.' :: '.' :: '.' :: '\r' :: xs) = Succ TDocEnd ('\r' :: xs)
blockTok bi ('.' :: '.' :: '.' :: [])         = Succ TDocEnd []
-- Directive (must be at start of document, before ---)
blockTok bi ('%' :: xs)              = lexDirective xs
-- Sequence item indicator
blockTok bi ('-' :: ' ' :: xs)       = Succ TDash (' ' :: xs)
blockTok bi ('-' :: '\n' :: xs)      = Succ TDash ('\n' :: xs)
blockTok bi ('-' :: '\r' :: xs)      = Succ TDash ('\r' :: xs)
blockTok bi ('-' :: '\t' :: xs)      = Succ TDash ('\t' :: xs)
blockTok bi (':' :: ' ' :: xs)       = Succ TColon (' ' :: xs)
blockTok bi (':' :: '\n' :: xs)      = Succ TColon ('\n' :: xs)
blockTok bi (':' :: '\r' :: xs)      = Succ TColon ('\r' :: xs)
blockTok bi (':' :: '\t' :: xs)      = Succ TColon ('\t' :: xs)
-- Complex key indicator
blockTok bi ('?' :: ' ' :: xs)       = Succ TQuestion (' ' :: xs)
blockTok bi ('?' :: '\n' :: xs)      = Succ TQuestion ('\n' :: xs)
blockTok bi ('?' :: '\r' :: xs)      = Succ TQuestion ('\r' :: xs)
blockTok bi ('?' :: '\t' :: xs)      = Succ TQuestion ('\t' :: xs)
blockTok bi ('[' :: xs)              = Succ TLBracket xs
blockTok bi ('{' :: xs)              = Succ TLBrace xs
blockTok bi ('|' :: xs)              = TScalar . YStr <$> blockScalar False xs
blockTok bi ('>' :: xs)              = TScalar . YStr <$> blockScalar True xs
blockTok bi ('"' :: xs)              = TScalar . YStr <$> dqString [<] xs
blockTok bi ('\'' :: xs)             = TScalar . YStr <$> sqString [<] xs
blockTok bi ('!' :: xs)              = lexTag xs
blockTok bi ('\n' :: xs)             = Succ TNewline xs
blockTok bi ('\r' :: '\n' :: xs)     = Succ TNewline xs
blockTok bi (c :: xs)                = TScalar . interpretScalar <$> plainScalarBlockMulti bi [< c] xs
blockTok bi []                       = eoiAt Same

||| Lex a single token in flow context
flowTok : Tok True e YAMLToken
flowTok (',' :: xs)  = Succ TComma xs
flowTok (':' :: xs)  = Succ TColon xs
flowTok ('?' :: xs)  = Succ TQuestion xs
flowTok ('[' :: xs)  = Succ TLBracket xs
flowTok (']' :: xs)  = Succ TRBracket xs
flowTok ('{' :: xs)  = Succ TLBrace xs
flowTok ('}' :: xs)  = Succ TRBrace xs
flowTok ('"' :: xs)  = TScalar . YStr <$> dqString [<] xs
flowTok ('\'' :: xs) = TScalar . YStr <$> sqString [<] xs
flowTok ('!' :: xs)  = lexTag xs
flowTok (c :: xs)    = TScalar . interpretScalar <$> plainScalarFlow [< c] xs
flowTok []           = eoiAt Same

--------------------------------------------------------------------------------
--          State Management
--------------------------------------------------------------------------------

||| Adjust flow context based on token
adjFlow : FlowCtxt -> YAMLToken -> FlowCtxt
adjFlow NoFlow     TLBracket      = InFlow 1
adjFlow NoFlow     TLBrace        = InFlow 1
adjFlow (InFlow n) TLBracket      = InFlow (S n)
adjFlow (InFlow n) TLBrace        = InFlow (S n)
adjFlow (InFlow (S Z)) TRBracket  = NoFlow
adjFlow (InFlow (S Z)) TRBrace    = NoFlow
adjFlow (InFlow (S (S n))) TRBracket = InFlow (S n)
adjFlow (InFlow (S (S n))) TRBrace   = InFlow (S n)
adjFlow ctx        _              = ctx

%inline
inFlow : FlowCtxt -> Bool
inFlow NoFlow    = False
inFlow (InFlow _) = True

--------------------------------------------------------------------------------
--          Main Lexer
--------------------------------------------------------------------------------

||| Get the current indentation level from the stack
currentIndent : List Nat -> Nat
currentIndent []        = 0
currentIndent (x :: _)  = x

||| Emit TDedent tokens for each level we're popping off the stack
||| Returns the new stack and the tokens to emit
popIndents :
     Position
  -> SnocList (Bounded YAMLToken)
  -> (spaces : Nat)
  -> List Nat
  -> (List Nat, SnocList (Bounded YAMLToken))
popIndents pos sx spaces [] = ([], sx)
popIndents pos sx spaces (lvl :: rest) =
  if spaces < lvl
    then popIndents pos (sx :< bounded TDedent pos pos) spaces rest
    else (lvl :: rest, sx)

mutual
  ||| After newline: count spaces, check indentation, emit TIndent/TDedent as needed
  lexAfterNewline :
       FlowCtxt
    -> (indStack : List Nat)
    -> Position
    -> SnocList (Bounded YAMLToken)
    -> (spaces : Nat)
    -> (cs : List Char)
    -> (0 acc : SuffixAcc cs)
    -> Either (Bounded YAMLErr) (List $ Bounded YAMLToken)
  lexAfterNewline ctx stack pos sx spaces (' ' :: xs) (SA r) =
    lexAfterNewline ctx stack (incCol pos) sx (S spaces) xs r
  lexAfterNewline ctx stack pos sx spaces ('\t' :: xs) _ =
    Left $ bounded (Custom TabIndent) pos (incCol pos)
  -- Blank line or comment-only line: skip without changing indent state
  lexAfterNewline ctx stack pos sx spaces ('\n' :: xs) (SA r) =
    let pos2 = incLine pos
     in lexAfterNewline ctx stack pos2 (sx :< bounded TNewline pos pos2) 0 xs r
  lexAfterNewline ctx stack pos sx spaces ('\r' :: '\n' :: xs) (SA r) =
    let pos2 = incLine pos
     in lexAfterNewline ctx stack pos2 (sx :< bounded TNewline pos pos2) 0 xs r
  lexAfterNewline ctx stack pos sx spaces xs acc =
    let curIndent = currentIndent stack
     in if spaces > curIndent
          -- Indentation increased: push new level, emit TIndent
          then let stack2 = spaces :: stack
                   sx2    = sx :< bounded TIndent pos pos
                in lex ctx stack2 pos sx2 xs acc
          else if spaces < curIndent
            -- Indentation decreased: pop levels, emit TDedent for each
            then let (stack2, sx2) = popIndents pos sx spaces stack
                  in lex ctx stack2 pos sx2 xs acc
            -- Same indentation: continue
            else lex ctx stack pos sx xs acc

  ||| Main lexer loop
  lex :
       FlowCtxt
    -> (indStack : List Nat)
    -> Position
    -> SnocList (Bounded YAMLToken)
    -> (cs : List Char)
    -> (0 acc : SuffixAcc cs)
    -> Either (Bounded YAMLErr) (List $ Bounded YAMLToken)
  lex ctx stack pos sx [] _ = Right $ sx <>> [bounded TEOI pos pos]
  lex ctx stack pos sx (' ' :: xs) (SA r)  = lex ctx stack (incCol pos) sx xs r
  lex ctx stack pos sx ('\t' :: xs) (SA r) = lex ctx stack (incCol pos) sx xs r
  lex ctx stack pos sx ('\n' :: xs) (SA r) =
    if inFlow ctx
      then lex ctx stack (incLine pos) sx xs r
      else let pos2 = incLine pos
               sx2  = sx :< bounded TNewline pos pos2
            in lexAfterNewline ctx stack pos2 sx2 0 xs r
  lex ctx stack pos sx ('\r' :: '\n' :: xs) (SA r) =
    if inFlow ctx
      then lex ctx stack (incLine pos) sx xs r
      else let pos2 = incLine pos
               sx2  = sx :< bounded TNewline pos pos2
            in lexAfterNewline ctx stack pos2 sx2 0 xs r
  lex ctx stack pos sx ('#' :: xs) (SA r) = skipComment xs r
    where
      skipComment :
           (cs : List Char)
        -> (0 acc : SuffixAcc cs)
        -> Either (Bounded YAMLErr) (List $ Bounded YAMLToken)
      skipComment ('\n' :: ys) (SA r') =
        if inFlow ctx
          then lex ctx stack (incLine pos) sx ys r'
          else let pos2 = incLine pos
                in lexAfterNewline ctx stack pos2 (sx :< bounded TNewline pos pos2) 0 ys r'
      skipComment ('\r' :: '\n' :: ys) (SA r') =
        if inFlow ctx
          then lex ctx stack (incLine pos) sx ys r'
          else let pos2 = incLine pos
                in lexAfterNewline ctx stack pos2 (sx :< bounded TNewline pos pos2) 0 ys r'
      skipComment (_ :: ys) (SA r') = skipComment ys r'
      skipComment [] _ = Right $ sx <>> [bounded TEOI pos pos]
  lex ctx stack pos sx cs (SA r) =
    if inFlow ctx
      then case flowTok cs of
             Succ val ys @{p'} =>
               let pos2 = endPos pos p'
                   ctx2 = adjFlow ctx val
                   sx2 = sx :< bounded val pos pos2
                in lex ctx2 stack pos2 sx2 ys r
             Fail start errEnd e => Left $ boundedErr pos start errEnd e
      else case blockTok (currentIndent stack) cs of
             Succ val ys @{p'} =>
               let pos2 = endPos pos p'
                   ctx2 = adjFlow ctx val
                   sx2 = sx :< bounded val pos pos2
                in lex ctx2 stack pos2 sx2 ys r
             Fail start errEnd e => Left $ boundedErr pos start errEnd e

||| Lex a YAML string into a list of tokens
export
lexYAML : String -> Either (Bounded YAMLErr) (List $ Bounded YAMLToken)
lexYAML s = lex NoFlow [0] begin [<] (unpack s) suffixAcc

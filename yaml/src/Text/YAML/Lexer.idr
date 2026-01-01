module Text.YAML.Lexer

import Data.List1
import Data.SnocList
import Text.Parse.Manual
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

--------------------------------------------------------------------------------
--          String Literals
--------------------------------------------------------------------------------

||| Valid YAML control characters that need escaping
yamlControl : Char -> Bool
yamlControl '\n' = True
yamlControl '\r' = True
yamlControl '\t' = True
yamlControl x    = x < ' '

||| Read a double-quoted string with escape sequences
dqString : SnocList Char -> AutoTok e String
dqString sc ('\\' :: c :: xs) = case c of
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
  'x'  => case xs of
    a :: b :: t =>
      if isHexDigit a && isHexDigit b
        then let c' = cast (hexDigit a * 16 + hexDigit b)
              in dqString (sc :< c') t
        else invalidEscape p t
    _ => invalidEscape p xs
  'u'  => case xs of
    a :: b :: c' :: d :: t =>
      if isHexDigit a && isHexDigit b && isHexDigit c' && isHexDigit d
        then let v = hexDigit a * 0x1000 + hexDigit b * 0x100 +
                     hexDigit c' * 0x10 + hexDigit d
              in dqString (sc :< cast v) t
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

trimSpaces : SnocList Char -> SnocList Char
trimSpaces [<]          = [<]
trimSpaces (sx :< ' ')  = trimSpaces sx
trimSpaces (sx :< '\t') = trimSpaces sx
trimSpaces sx           = sx

||| Characters that terminate a plain scalar in block context
isPlainEndBlock : Char -> Bool
isPlainEndBlock ':' = True
isPlainEndBlock '#' = True
isPlainEndBlock '\n' = True
isPlainEndBlock '\r' = True
isPlainEndBlock _   = False

||| Characters that terminate a plain scalar in flow context
isPlainEndFlow : Char -> Bool
isPlainEndFlow ','  = True
isPlainEndFlow '['  = True
isPlainEndFlow ']'  = True
isPlainEndFlow '{'  = True
isPlainEndFlow '}'  = True
isPlainEndFlow c    = isPlainEndBlock c

||| Read a plain (unquoted) scalar in block context
plainScalarBlock : SnocList Char -> AutoTok e String
plainScalarBlock sc (c :: xs) =
  if isPlainEndBlock c
    then Succ (cast $ trimSpaces sc) (c :: xs)
    else plainScalarBlock (sc :< c) xs
plainScalarBlock sc [] = Succ (cast $ trimSpaces sc) []

||| Read a plain (unquoted) scalar in flow context
plainScalarFlow : SnocList Char -> AutoTok e String
plainScalarFlow sc (c :: xs) =
  if isPlainEndFlow c
    then Succ (cast $ trimSpaces sc) (c :: xs)
    else plainScalarFlow (sc :< c) xs
plainScalarFlow sc [] = Succ (cast $ trimSpaces sc) []

--------------------------------------------------------------------------------
--          Scalar Value Interpretation
--------------------------------------------------------------------------------

||| Try to parse YAML-specific integer formats (hex, octal)
||| Standard decimal integers are handled by `tryNumber`
tryYamlInteger : String -> Maybe Integer
tryYamlInteger s = case unpack s of
  '0' :: 'x' :: rest => parseHex rest
  '0' :: 'o' :: rest => parseOct rest
  _                  => Nothing
  where
    parseHex : List Char -> Maybe Integer
    parseHex [] = Nothing
    parseHex cs =
      if all isHexDigit cs
        then Just $ foldl (\acc, c => acc * 16 + cast (hexDigit c)) 0 cs
        else Nothing

    parseOct : List Char -> Maybe Integer
    parseOct [] = Nothing
    parseOct cs =
      if all (\c => c >= '0' && c <= '7') cs
        then Just $ foldl (\acc, c => acc * 8 + cast (ord c - ord '0')) 0 cs
        else Nothing

||| Try to parse a standard numeric value using the `number` shifter.
||| Returns Just if the entire string is a valid number, Nothing otherwise.
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
-- Numeric values
interpretScalar s = case tryYamlInteger s of
  Just i  => YInt i
  Nothing => case tryNumber s of
    Just v  => v
    Nothing => YStr s

--------------------------------------------------------------------------------
--          Token Lexing
--------------------------------------------------------------------------------

||| Lex a single token in block context
blockTok : Tok True e YAMLToken
blockTok ('-' :: ' ' :: xs)       = Succ TDash (' ' :: xs)
blockTok ('-' :: '\n' :: xs)      = Succ TDash ('\n' :: xs)
blockTok ('-' :: '\r' :: xs)      = Succ TDash ('\r' :: xs)
blockTok ('-' :: '\t' :: xs)      = Succ TDash ('\t' :: xs)
blockTok (':' :: ' ' :: xs)       = Succ TColon (' ' :: xs)
blockTok (':' :: '\n' :: xs)      = Succ TColon ('\n' :: xs)
blockTok (':' :: '\r' :: xs)      = Succ TColon ('\r' :: xs)
blockTok (':' :: '\t' :: xs)      = Succ TColon ('\t' :: xs)
blockTok ('[' :: xs)              = Succ TLBracket xs
blockTok ('{' :: xs)              = Succ TLBrace xs
blockTok ('"' :: xs)              = TScalar . YStr <$> dqString [<] xs
blockTok ('\'' :: xs)             = TScalar . YStr <$> sqString [<] xs
blockTok ('\n' :: xs)             = Succ TNewline xs
blockTok ('\r' :: '\n' :: xs)     = Succ TNewline xs
blockTok (c :: xs)                = TScalar . interpretScalar <$> plainScalarBlock [< c] xs
blockTok []                       = eoiAt Same

||| Lex a single token in flow context
flowTok : Tok True e YAMLToken
flowTok (',' :: xs)  = Succ TComma xs
flowTok (':' :: xs)  = Succ TColon xs
flowTok ('[' :: xs)  = Succ TLBracket xs
flowTok (']' :: xs)  = Succ TRBracket xs
flowTok ('{' :: xs)  = Succ TLBrace xs
flowTok ('}' :: xs)  = Succ TRBrace xs
flowTok ('"' :: xs)  = TScalar . YStr <$> dqString [<] xs
flowTok ('\'' :: xs) = TScalar . YStr <$> sqString [<] xs
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
    let tok = if inFlow ctx then flowTok else blockTok
     in case tok cs of
          Succ val ys @{p'} =>
            let pos2 = endPos pos p'
                ctx2 = adjFlow ctx val
             in lex ctx2 stack pos2 (sx :< bounded val pos pos2) ys r
          Fail start errEnd e => Left $ boundedErr pos start errEnd e

||| Lex a YAML string into a list of tokens
export
lexYAML : String -> Either (Bounded YAMLErr) (List $ Bounded YAMLToken)
lexYAML s = lex NoFlow [0] begin [<] (unpack s) suffixAcc

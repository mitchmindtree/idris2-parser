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
--          Flow Collection Parsers
--------------------------------------------------------------------------------

mutual
  flowSeq : Bounds -> SnocList YAMLValue -> Rule True YAMLValue

  flowMap : Bounds -> SnocList (YAMLValue, YAMLValue) -> Rule True YAMLValue

  value : Rule True YAMLValue
  -- Block sequence: single item (multi-item requires complex suffix proof threading)
  value (B TDash _ :: xs) (SA r) =
    case succT $ value xs r of
      Succ0 v ys => Succ0 (YSeq [v]) ys
      Fail0 err  => Fail0 err
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

export
parseYAML : Origin -> String -> Either (ParseError YAMLParseError) YAMLValue
parseYAML o str = case lexYAML str of
  Right ts => case value ts suffixAcc of
    Fail0 x           => Left (toParseError o str x)
    Succ0 v []        => Right v
    Succ0 v [B TEOI _] => Right v
    Succ0 v (x :: xs) => leftErr o str $ unexpected x
  Left err => Left (toParseError o str err)

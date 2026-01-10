module Props.DateTime

import Gen.DateTime
import Data.List.Suffix
import Text.Time.Lexer
import Text.Lex.Manual

%default total

--------------------------------------------------------------------------------
--          Helpers
--------------------------------------------------------------------------------

||| Run a strict tokenizer on a string and check for successful parse
runTok : StrictTok e a -> String -> Maybe a
runTok tok str =
  let cs : List Char = unpack str
  in case tok {orig = cs} cs @{Same} of
    Succ v [] => Just v
    _         => Nothing

||| Property: tokenizing an encoded value should return the original value
lexProp : Show a => Eq a => StrictTok () a -> Gen (Encoded a) -> Property
lexProp tok gen = property $ do
  enc <- forAll gen
  runTok tok enc.code === Just enc.value

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

prop_date : Property
prop_date = lexProp date dateEnc

prop_localTime : Property
prop_localTime = lexProp localTime localTimeEnc

prop_offsetTime : Property
prop_offsetTime = lexProp offsetTime $ do
  lt <- localTime
  o <- offset
  ostr <- offsetStr o
  pure $ Enc "\{lt}\{ostr}" (OT lt o)

prop_anyTime : Property
prop_anyTime = lexProp anyTime anyTime

--------------------------------------------------------------------------------
--          Export
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup
    "Text.Time.Lexer"
    [ ("prop_date", prop_date)
    , ("prop_localTime", prop_localTime)
    , ("prop_offsetTime", prop_offsetTime)
    , ("prop_anyTime", prop_anyTime)
    ]

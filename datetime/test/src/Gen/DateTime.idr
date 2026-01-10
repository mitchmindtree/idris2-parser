module Gen.DateTime

import public Data.String
import public Data.Time.Date
import public Data.Time.Time
import public Data.Vect
import public Hedgehog

%default total

--------------------------------------------------------------------------------
--          Encoded
--------------------------------------------------------------------------------

||| A value paired with its string encoding
public export
record Encoded a where
  constructor Enc
  code  : String
  value : a

public export
Functor Encoded where
  map f (Enc c v) = Enc c $ f v

export
Show a => Show (Encoded a) where
  show (Enc c v) = "Enc " ++ show c ++ " " ++ show v

export
Eq a => Eq (Encoded a) where
  Enc c1 v1 == Enc c2 v2 = c1 == c2 && v1 == v2

||| Create an encoded value using an interpolation function
export
encoded : (a -> String) -> Gen a -> Gen (Encoded a)
encoded f = map $ \v => Enc (f v) v

--------------------------------------------------------------------------------
--          Date Components
--------------------------------------------------------------------------------

export
year : Gen Year
year = fromMaybe 0 . refineYear <$> integer (exponential 0 9999)

export
month : Gen Month
month = fromMaybe JAN . intToMonth <$> integer (linear 1 12)

export
date : Gen Date
date = [| toDate year month (integer $ linear 1 31) |]

  where
    toDate : Year -> Month -> Integer -> Date
    toDate y m i = case refineDay {m} i of
      Just d  => MkDate y m d
      Nothing => MkDate y JAN 1

--------------------------------------------------------------------------------
--          Time Components
--------------------------------------------------------------------------------

export
hour : Gen Hour
hour = fromMaybe 0 . refineHour <$> integer (linear 0 23)

export
minute : Gen Minute
minute = fromMaybe 0 . refineMinute <$> integer (linear 0 59)

export
second : Gen Second
second = fromMaybe 0 . refineSecond <$> integer (linear 0 60)

export
microsecond : Gen MicroSecond
microsecond = fromMaybe 0 . refineMicroSecond <$> integer (exponential 0 999_999)

export
localTime : Gen LocalTime
localTime = [| LT hour minute second (maybe microsecond) |]

export
sign : Gen Sign
sign = element [Minus, Plus]

export
offset : Gen Offset
offset = frequency
  [ (5, [| O sign hour minute |])
  , (1, constant Z)
  ]

export
offsetTime : Gen OffsetTime
offsetTime = [| OT localTime offset |]

--------------------------------------------------------------------------------
--          DateTime
--------------------------------------------------------------------------------

export
localDateTime : Gen LocalDateTime
localDateTime = [| LDT date localTime |]

export
offsetDateTime : Gen OffsetDateTime
offsetDateTime = [| ODT date offsetTime |]

--------------------------------------------------------------------------------
--          AnyTime with Encoding Variations
--------------------------------------------------------------------------------

||| Generate 'T' or 't' separator
export
tSep : Gen Char
tSep = element ['T', 't']

||| Generate offset with optional lowercase 'z'
export
offsetStr : Offset -> Gen String
offsetStr Z     = element ["Z", "z"]
offsetStr (O s h m) = pure "\{s}\{h}:\{m}"

||| Encode a date
export
dateEnc : Gen (Encoded Date)
dateEnc = encoded interpolate date

||| Encode local time
export
localTimeEnc : Gen (Encoded LocalTime)
localTimeEnc = encoded interpolate localTime

||| Encode local date-time with T/t separator
localDateTimeEnc : Gen (Encoded LocalDateTime)
localDateTimeEnc = do
  d <- date
  t <- localTime
  sep <- tSep
  pure $ Enc "\{d}\{pack [sep]}\{t}" (LDT d t)

||| Encode offset date-time with T/t separator
offsetDateTimeEnc : Gen (Encoded OffsetDateTime)
offsetDateTimeEnc = do
  d <- date
  lt <- localTime
  o <- offset
  sep <- tSep
  ostr <- offsetStr o
  pure $ Enc "\{d}\{pack [sep]}\{lt}\{ostr}" (ODT d (OT lt o))

||| Generate any time value with its encoding
export
anyTime : Gen (Encoded AnyTime)
anyTime = choice
  [ map ATDate <$> dateEnc
  , map ATLocalTime <$> localTimeEnc
  , map ATLocalDateTime <$> localDateTimeEnc
  , map ATOffsetDateTime <$> offsetDateTimeEnc
  ]

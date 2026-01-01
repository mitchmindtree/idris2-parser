module Main

import Hedgehog
import Text.YAML

%default total

--------------------------------------------------------------------------------
--          Helpers
--------------------------------------------------------------------------------

parseOk : String -> YAMLValue -> Property
parseOk s expected =
  property1 $ parseYAML Virtual s === Right expected

parseErr : String -> Property
parseErr s =
  property1 $ case parseYAML Virtual s of
    Left _  => True === True
    Right v => annotate ("Expected error but got: " ++ show v) >> failure

--------------------------------------------------------------------------------
--          Null Tests
--------------------------------------------------------------------------------

prop_null_tilde : Property
prop_null_tilde = parseOk "~" YNull

prop_null_word : Property
prop_null_word = parseOk "null" YNull

prop_null_Null : Property
prop_null_Null = parseOk "Null" YNull

prop_null_NULL : Property
prop_null_NULL = parseOk "NULL" YNull

--------------------------------------------------------------------------------
--          Boolean Tests
--------------------------------------------------------------------------------

prop_bool_true : Property
prop_bool_true = parseOk "true" (YBool True)

prop_bool_True : Property
prop_bool_True = parseOk "True" (YBool True)

prop_bool_TRUE : Property
prop_bool_TRUE = parseOk "TRUE" (YBool True)

prop_bool_false : Property
prop_bool_false = parseOk "false" (YBool False)

prop_bool_False : Property
prop_bool_False = parseOk "False" (YBool False)

prop_bool_FALSE : Property
prop_bool_FALSE = parseOk "FALSE" (YBool False)

--------------------------------------------------------------------------------
--          Integer Tests
--------------------------------------------------------------------------------

prop_int_zero : Property
prop_int_zero = parseOk "0" (YInt 0)

prop_int_positive : Property
prop_int_positive = parseOk "42" (YInt 42)

prop_int_negative : Property
prop_int_negative = parseOk "-17" (YInt (-17))

prop_int_hex : Property
prop_int_hex = parseOk "0x2a" (YInt 42)

prop_int_octal : Property
prop_int_octal = parseOk "0o52" (YInt 42)

--------------------------------------------------------------------------------
--          Float Tests
--------------------------------------------------------------------------------

prop_float_simple : Property
prop_float_simple = parseOk "3.14" (YFloat 3.14)

prop_float_exp : Property
prop_float_exp = parseOk "1e10" (YFloat 1.0e10)

--------------------------------------------------------------------------------
--          String Tests
--------------------------------------------------------------------------------

prop_string_plain : Property
prop_string_plain = parseOk "hello world" (YStr "hello world")

prop_string_double_quoted : Property
prop_string_double_quoted = parseOk "\"hello world\"" (YStr "hello world")

prop_string_single_quoted : Property
prop_string_single_quoted = parseOk "'hello world'" (YStr "hello world")

prop_string_escape_newline : Property
prop_string_escape_newline = parseOk "\"hello\\nworld\"" (YStr "hello\nworld")

prop_string_escape_tab : Property
prop_string_escape_tab = parseOk "\"hello\\tworld\"" (YStr "hello\tworld")

--------------------------------------------------------------------------------
--          Flow Sequence Tests
--------------------------------------------------------------------------------

prop_seq_empty : Property
prop_seq_empty = parseOk "[]" (YSeq [])

prop_seq_single : Property
prop_seq_single = parseOk "[1]" (YSeq [YInt 1])

prop_seq_multiple : Property
prop_seq_multiple = parseOk "[1, 2, 3]" (YSeq [YInt 1, YInt 2, YInt 3])

prop_seq_mixed : Property
prop_seq_mixed = parseOk "[1, true, \"hello\"]" (YSeq [YInt 1, YBool True, YStr "hello"])

prop_seq_nested : Property
prop_seq_nested = parseOk "[[1, 2], [3, 4]]" (YSeq [YSeq [YInt 1, YInt 2], YSeq [YInt 3, YInt 4]])

--------------------------------------------------------------------------------
--          Flow Mapping Tests
--------------------------------------------------------------------------------

prop_map_empty : Property
prop_map_empty = parseOk "{}" (YMap [])

prop_map_single : Property
prop_map_single = parseOk "{a: 1}" (YMap [(YStr "a", YInt 1)])

prop_map_multiple : Property
prop_map_multiple = parseOk "{a: 1, b: 2}" (YMap [(YStr "a", YInt 1), (YStr "b", YInt 2)])

prop_map_nested : Property
prop_map_nested = parseOk "{outer: {inner: 42}}"
  (YMap [(YStr "outer", YMap [(YStr "inner", YInt 42)])])

--------------------------------------------------------------------------------
--          Block Sequence Tests
--------------------------------------------------------------------------------

prop_block_seq_single : Property
prop_block_seq_single = parseOk "- 1" (YSeq [YInt 1])

prop_block_seq_single_string : Property
prop_block_seq_single_string = parseOk "- hello" (YSeq [YStr "hello"])

--------------------------------------------------------------------------------
--          Whitespace and Comments
--------------------------------------------------------------------------------

prop_trailing_whitespace : Property
prop_trailing_whitespace = parseOk "42  " (YInt 42)

prop_leading_whitespace : Property
prop_leading_whitespace = parseOk "  42" (YInt 42)

prop_comment_inline : Property
prop_comment_inline = parseOk "42 # this is a comment" (YInt 42)

prop_comment_line : Property
prop_comment_line = parseOk "# comment\n42" (YInt 42)

--------------------------------------------------------------------------------
--          Main Function
--------------------------------------------------------------------------------

properties : Group
properties =
  MkGroup
    "YAML.Parser"
    [ ("prop_null_tilde", prop_null_tilde)
    , ("prop_null_word", prop_null_word)
    , ("prop_null_Null", prop_null_Null)
    , ("prop_null_NULL", prop_null_NULL)
    , ("prop_bool_true", prop_bool_true)
    , ("prop_bool_True", prop_bool_True)
    , ("prop_bool_TRUE", prop_bool_TRUE)
    , ("prop_bool_false", prop_bool_false)
    , ("prop_bool_False", prop_bool_False)
    , ("prop_bool_FALSE", prop_bool_FALSE)
    , ("prop_int_zero", prop_int_zero)
    , ("prop_int_positive", prop_int_positive)
    , ("prop_int_negative", prop_int_negative)
    , ("prop_int_hex", prop_int_hex)
    , ("prop_int_octal", prop_int_octal)
    , ("prop_float_simple", prop_float_simple)
    , ("prop_float_exp", prop_float_exp)
    , ("prop_string_plain", prop_string_plain)
    , ("prop_string_double_quoted", prop_string_double_quoted)
    , ("prop_string_single_quoted", prop_string_single_quoted)
    , ("prop_string_escape_newline", prop_string_escape_newline)
    , ("prop_string_escape_tab", prop_string_escape_tab)
    , ("prop_seq_empty", prop_seq_empty)
    , ("prop_seq_single", prop_seq_single)
    , ("prop_seq_multiple", prop_seq_multiple)
    , ("prop_seq_mixed", prop_seq_mixed)
    , ("prop_seq_nested", prop_seq_nested)
    , ("prop_map_empty", prop_map_empty)
    , ("prop_map_single", prop_map_single)
    , ("prop_map_multiple", prop_map_multiple)
    , ("prop_map_nested", prop_map_nested)
    , ("prop_block_seq_single", prop_block_seq_single)
    , ("prop_block_seq_single_string", prop_block_seq_single_string)
    , ("prop_trailing_whitespace", prop_trailing_whitespace)
    , ("prop_leading_whitespace", prop_leading_whitespace)
    , ("prop_comment_inline", prop_comment_inline)
    , ("prop_comment_line", prop_comment_line)
    ]

main : IO ()
main = test [properties]

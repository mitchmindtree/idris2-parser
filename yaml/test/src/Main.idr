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

prop_block_seq_two_items : Property
prop_block_seq_two_items = parseOk
  """
  - 1
  - 2
  """
  (YSeq [YInt 1, YInt 2])

prop_block_seq_three_items : Property
prop_block_seq_three_items = parseOk
  """
  - 1
  - 2
  - 3
  """
  (YSeq [YInt 1, YInt 2, YInt 3])

prop_block_seq_mixed_types : Property
prop_block_seq_mixed_types = parseOk
  """
  - 1
  - true
  - hello
  """
  (YSeq [YInt 1, YBool True, YStr "hello"])

prop_block_seq_nested_flow : Property
prop_block_seq_nested_flow = parseOk
  """
  - [1, 2]
  - [3, 4]
  """
  (YSeq [YSeq [YInt 1, YInt 2], YSeq [YInt 3, YInt 4]])

--------------------------------------------------------------------------------
--          Block Mapping Tests
--------------------------------------------------------------------------------

prop_block_map_single : Property
prop_block_map_single = parseOk "name: Alice"
  (YMap [(YStr "name", YStr "Alice")])

prop_block_map_two : Property
prop_block_map_two = parseOk
  """
  name: Alice
  age: 30
  """
  (YMap [(YStr "name", YStr "Alice"), (YStr "age", YInt 30)])

prop_block_map_three : Property
prop_block_map_three = parseOk
  """
  a: 1
  b: 2
  c: 3
  """
  (YMap [(YStr "a", YInt 1), (YStr "b", YInt 2), (YStr "c", YInt 3)])

prop_block_map_mixed_values : Property
prop_block_map_mixed_values = parseOk
  """
  str: hello
  num: 42
  bool: true
  """
  (YMap [(YStr "str", YStr "hello"), (YStr "num", YInt 42), (YStr "bool", YBool True)])

prop_block_map_flow_value : Property
prop_block_map_flow_value = parseOk "items: [1, 2, 3]"
  (YMap [(YStr "items", YSeq [YInt 1, YInt 2, YInt 3])])

prop_block_map_empty_value : Property
prop_block_map_empty_value = parseOk
  """
  empty:
  next: 1
  """
  (YMap [(YStr "empty", YNull), (YStr "next", YInt 1)])

prop_block_map_empty_value_end : Property
prop_block_map_empty_value_end = parseOk "key:\n"
  (YMap [(YStr "key", YNull)])

--------------------------------------------------------------------------------
--          Nested Block Structure Tests
--------------------------------------------------------------------------------

-- Simple nested mapping: parent with one nested child
prop_nested_map_simple : Property
prop_nested_map_simple = parseOk
  """
  parent:
    child: value
  """
  (YMap [(YStr "parent", YMap [(YStr "child", YStr "value")])])

-- Nested mapping with sibling at parent level
prop_nested_map_with_sibling : Property
prop_nested_map_with_sibling = parseOk
  """
  parent:
    child: 1
  sibling: 2
  """
  (YMap [(YStr "parent", YMap [(YStr "child", YInt 1)]),
         (YStr "sibling", YInt 2)])

-- Nested mapping with multiple children, then sibling at parent level
-- This tests TDedent handling after nested block ends
prop_nested_map_children_then_sibling : Property
prop_nested_map_children_then_sibling = parseOk
  """
  parent:
    a: 1
    b: 2
  sibling: 3
  """
  (YMap [(YStr "parent", YMap [(YStr "a", YInt 1), (YStr "b", YInt 2)]),
         (YStr "sibling", YInt 3)])

-- Nested mapping with multiple children
prop_nested_map_multiple_children : Property
prop_nested_map_multiple_children = parseOk
  """
  parent:
    a: 1
    b: 2
  """
  (YMap [(YStr "parent", YMap [(YStr "a", YInt 1), (YStr "b", YInt 2)])])

-- Nested mapping with multiple children
prop_nested_nested_map_simple : Property
prop_nested_nested_map_simple = parseOk
  """
  grandparent:
    a: 1
    parent:
      b: 2
  """
  (YMap [(YStr "grandparent", YMap [(YStr "a", YInt 1), (YStr "parent", YMap [(YStr "b", YInt 2)])])])

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
prop_comment_line = parseOk
  """
  # comment
  42
  """
  (YInt 42)

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
    , ("prop_block_seq_two_items", prop_block_seq_two_items)
    , ("prop_block_seq_three_items", prop_block_seq_three_items)
    , ("prop_block_seq_mixed_types", prop_block_seq_mixed_types)
    , ("prop_block_seq_nested_flow", prop_block_seq_nested_flow)
    , ("prop_block_map_single", prop_block_map_single)
    , ("prop_block_map_two", prop_block_map_two)
    , ("prop_block_map_three", prop_block_map_three)
    , ("prop_block_map_mixed_values", prop_block_map_mixed_values)
    , ("prop_block_map_flow_value", prop_block_map_flow_value)
    , ("prop_block_map_empty_value", prop_block_map_empty_value)
    , ("prop_block_map_empty_value_end", prop_block_map_empty_value_end)
    , ("prop_nested_map_simple", prop_nested_map_simple)
    , ("prop_nested_map_with_sibling", prop_nested_map_with_sibling)
    , ("prop_nested_map_children_then_sibling", prop_nested_map_children_then_sibling)
    , ("prop_nested_map_multiple_children", prop_nested_map_multiple_children)
    , ("prop_nested_nested_map_simple", prop_nested_nested_map_simple)
    , ("prop_trailing_whitespace", prop_trailing_whitespace)
    , ("prop_leading_whitespace", prop_leading_whitespace)
    , ("prop_comment_inline", prop_comment_inline)
    , ("prop_comment_line", prop_comment_line)
    ]

main : IO ()
main = test [properties]

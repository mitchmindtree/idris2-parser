module Main

import Data.SnocList
import Hedgehog
import Text.YAML

%default total

--------------------------------------------------------------------------------
--          Helpers
--------------------------------------------------------------------------------

-- Test single-document parsing (most common case)
parseOk : String -> YAMLValue -> Property
parseOk s expected =
  property1 $ parseYAML Virtual s === Right [< expected]

-- Test multi-document parsing
parseDocsOk : String -> SnocList YAMLValue -> Property
parseDocsOk s expected =
  property1 $ parseYAML Virtual s === Right expected

parseErr : String -> Property
parseErr s =
  property1 $ case parseYAML Virtual s of
    Left _  => True === True
    Right v => annotate ("Expected error but got: " ++ show (v <>> [])) >> failure

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

prop_string_escape_bell : Property
prop_string_escape_bell = parseOk "\"\\a\"" (YStr "\x07")

prop_string_escape_vtab : Property
prop_string_escape_vtab = parseOk "\"\\v\"" (YStr "\x0B")

prop_string_escape_esc : Property
prop_string_escape_esc = parseOk "\"\\e\"" (YStr "\x1B")

prop_string_escape_nbsp : Property
prop_string_escape_nbsp = parseOk "\"\\_\"" (YStr "\xA0")

prop_string_escape_next_line : Property
prop_string_escape_next_line = parseOk "\"\\N\"" (YStr "\x85")

prop_string_escape_line_sep : Property
prop_string_escape_line_sep = parseOk "\"\\L\"" (YStr "\x2028")

prop_string_escape_para_sep : Property
prop_string_escape_para_sep = parseOk "\"\\P\"" (YStr "\x2029")

prop_string_escape_unicode32 : Property
prop_string_escape_unicode32 = parseOk "\"\\U0001F600\"" (YStr "\x1F600")

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
--          Recursive Nesting Tests
--------------------------------------------------------------------------------

-- Inline nested sequences
prop_nested_seq_inline : Property
prop_nested_seq_inline = parseOk "- - a" (YSeq [YSeq [YStr "a"]])

prop_nested_seq_triple : Property
prop_nested_seq_triple = parseOk "- - - a" (YSeq [YSeq [YSeq [YStr "a"]]])

-- Nested sequence with continuation
prop_nested_seq_multi : Property
prop_nested_seq_multi = parseOk
  """
  - - a
    - b
  """
  (YSeq [YSeq [YStr "a", YStr "b"]])

prop_nested_seq_with_outer : Property
prop_nested_seq_with_outer = parseOk
  """
  - - a
    - b
  - c
  """
  (YSeq [YSeq [YStr "a", YStr "b"], YStr "c"])

-- Compact notation (sequence item is a multi-key mapping)
prop_compact_single : Property
prop_compact_single = parseOk
  """
  - name: foo
    value: 1
  """
  (YSeq [YMap [(YStr "name", YStr "foo"), (YStr "value", YInt 1)]])

prop_compact_multi : Property
prop_compact_multi = parseOk
  """
  - a: 1
    b: 2
  - c: 3
  """
  (YSeq [YMap [(YStr "a", YInt 1), (YStr "b", YInt 2)],
         YMap [(YStr "c", YInt 3)]])

-- Dash-newline-indent patterns
prop_dash_newline_seq : Property
prop_dash_newline_seq = parseOk
  """
  -
    - a
  """
  (YSeq [YSeq [YStr "a"]])

prop_dash_newline_map : Property
prop_dash_newline_map = parseOk
  """
  -
    name: foo
  """
  (YSeq [YMap [(YStr "name", YStr "foo")]])

-- Real-world pattern: list of objects
prop_list_of_objects : Property
prop_list_of_objects = parseOk
  """
  - name: alice
    age: 30
  - name: bob
    age: 25
  """
  (YSeq [YMap [(YStr "name", YStr "alice"), (YStr "age", YInt 30)],
         YMap [(YStr "name", YStr "bob"), (YStr "age", YInt 25)]])

-- Deep mixed nesting
prop_deep_mixed_nesting : Property
prop_deep_mixed_nesting = parseOk
  """
  - config:
      items:
        - a
        - b
      name: test
  """
  (YSeq [YMap [(YStr "config", YMap [
    (YStr "items", YSeq [YStr "a", YStr "b"]),
    (YStr "name", YStr "test")])]])

-- Map containing sequence of compact maps
prop_map_with_seq_of_maps : Property
prop_map_with_seq_of_maps = parseOk
  """
  users:
    - name: alice
      role: admin
    - name: bob
      role: user
  """
  (YMap [(YStr "users", YSeq [
    YMap [(YStr "name", YStr "alice"), (YStr "role", YStr "admin")],
    YMap [(YStr "name", YStr "bob"), (YStr "role", YStr "user")]])])

--------------------------------------------------------------------------------
--          Block Scalar Tests
--------------------------------------------------------------------------------

-- Basic literal block scalar
prop_block_literal_simple : Property
prop_block_literal_simple = parseOk "key: |\n  line1\n  line2\n"
  (YMap [(YStr "key", YStr "line1\nline2\n")])

-- Basic folded block scalar
prop_block_folded_simple : Property
prop_block_folded_simple = parseOk "key: >\n  line1\n  line2\n"
  (YMap [(YStr "key", YStr "line1 line2\n")])

-- Literal with strip chomping
prop_block_literal_strip : Property
prop_block_literal_strip = parseOk "key: |-\n  text\n"
  (YMap [(YStr "key", YStr "text")])

-- Literal with keep chomping
prop_block_literal_keep : Property
prop_block_literal_keep = parseOk "key: |+\n  text\n\n"
  (YMap [(YStr "key", YStr "text\n\n")])

-- Folded with strip chomping
prop_block_folded_strip : Property
prop_block_folded_strip = parseOk "key: >-\n  text\n"
  (YMap [(YStr "key", YStr "text")])

-- Folded with blank line preserved
prop_block_folded_blank : Property
prop_block_folded_blank = parseOk "key: >\n  para1\n\n  para2\n"
  (YMap [(YStr "key", YStr "para1\n\npara2\n")])

-- Block scalar with explicit indentation
prop_block_explicit_indent : Property
prop_block_explicit_indent = parseOk "key: |2\n  text\n"
  (YMap [(YStr "key", YStr "text\n")])

-- More-indented lines in folded (preserve newlines)
prop_block_folded_more_indent : Property
prop_block_folded_more_indent = parseOk "key: >\n  text\n    code\n  more\n"
  (YMap [(YStr "key", YStr "text\n  code\nmore\n")])

-- Block scalar in sequence
prop_block_scalar_in_seq : Property
prop_block_scalar_in_seq = parseOk "- |\n  hello\n"
  (YSeq [YStr "hello\n"])

-- Empty block scalar (no content)
prop_block_empty : Property
prop_block_empty = parseOk "key: |\nnext: value\n"
  (YMap [(YStr "key", YStr ""), (YStr "next", YStr "value")])

-- Block scalar followed by sibling key
prop_block_then_sibling : Property
prop_block_then_sibling = parseOk "first: |\n  content\nsecond: value\n"
  (YMap [(YStr "first", YStr "content\n"), (YStr "second", YStr "value")])

-- Comment in block scalar header
prop_block_header_comment : Property
prop_block_header_comment = parseOk "key: | # this is a comment\n  text\n"
  (YMap [(YStr "key", YStr "text\n")])

-- Multiple block scalars in document
prop_block_multiple : Property
prop_block_multiple = parseOk "a: |\n  first\nb: >\n  second\n"
  (YMap [(YStr "a", YStr "first\n"), (YStr "b", YStr "second\n")])

-- Indicator order: indent then chomping
prop_block_indent_then_chomp : Property
prop_block_indent_then_chomp = parseOk "key: |2-\n  text\n"
  (YMap [(YStr "key", YStr "text")])

-- Folded with multiple consecutive blank lines
prop_block_folded_multi_blank : Property
prop_block_folded_multi_blank = parseOk "key: >\n  para1\n\n\n  para2\n"
  (YMap [(YStr "key", YStr "para1\n\n\npara2\n")])

-- Block scalar at EOF without trailing newline
prop_block_eof_no_newline : Property
prop_block_eof_no_newline = parseOk "key: |\n  text"
  (YMap [(YStr "key", YStr "text\n")])

-- Block scalar in nested map
prop_block_nested : Property
prop_block_nested = parseOk
  """
  outer:
    inner: |
      nested content
  """
  (YMap [(YStr "outer", YMap [(YStr "inner", YStr "nested content\n")])])

-- Deeply indented block scalar (4 spaces)
prop_block_deep_indent : Property
prop_block_deep_indent = parseOk "key: |\n    four spaces\n"
  (YMap [(YStr "key", YStr "four spaces\n")])

-- Block scalar preserves internal indentation
prop_block_preserve_indent : Property
prop_block_preserve_indent = parseOk "key: |\n  line1\n    indented\n  line2\n"
  (YMap [(YStr "key", YStr "line1\n  indented\nline2\n")])

--------------------------------------------------------------------------------
--          Document Marker Tests
--------------------------------------------------------------------------------

-- Single document with explicit start marker
prop_doc_explicit_start : Property
prop_doc_explicit_start = parseOk
  """
  ---
  value: 1
  """
  (YMap [(YStr "value", YInt 1)])

-- Document start with space after
prop_doc_start_space : Property
prop_doc_start_space = parseOk "--- \nvalue: 1\n"
  (YMap [(YStr "value", YInt 1)])

-- Document end marker (single doc)
prop_doc_end : Property
prop_doc_end = parseOk
  """
  value: 1
  ...
  """
  (YMap [(YStr "value", YInt 1)])

-- Document with both start and end markers
prop_doc_start_and_end : Property
prop_doc_start_and_end = parseOk
  """
  ---
  value: 1
  ...
  """
  (YMap [(YStr "value", YInt 1)])

-- Multiple documents
prop_multi_doc_two : Property
prop_multi_doc_two = parseDocsOk
  """
  ---
  a: 1
  ---
  b: 2
  """
  [< YMap [(YStr "a", YInt 1)], YMap [(YStr "b", YInt 2)]]

-- Multiple documents with end marker
prop_multi_doc_with_end : Property
prop_multi_doc_with_end = parseDocsOk
  """
  ---
  a: 1
  ...
  ---
  b: 2
  """
  [< YMap [(YStr "a", YInt 1)], YMap [(YStr "b", YInt 2)]]

-- Three documents
prop_multi_doc_three : Property
prop_multi_doc_three = parseDocsOk
  """
  ---
  1
  ---
  2
  ---
  3
  """
  [< YInt 1, YInt 2, YInt 3]

-- First doc without marker (implicit start)
prop_multi_doc_first_implicit : Property
prop_multi_doc_first_implicit = parseDocsOk
  """
  a: 1
  ---
  b: 2
  """
  [< YMap [(YStr "a", YInt 1)], YMap [(YStr "b", YInt 2)]]

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
    , ("prop_string_escape_bell", prop_string_escape_bell)
    , ("prop_string_escape_vtab", prop_string_escape_vtab)
    , ("prop_string_escape_esc", prop_string_escape_esc)
    , ("prop_string_escape_nbsp", prop_string_escape_nbsp)
    , ("prop_string_escape_next_line", prop_string_escape_next_line)
    , ("prop_string_escape_line_sep", prop_string_escape_line_sep)
    , ("prop_string_escape_para_sep", prop_string_escape_para_sep)
    , ("prop_string_escape_unicode32", prop_string_escape_unicode32)
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
    , ("prop_nested_seq_inline", prop_nested_seq_inline)
    , ("prop_nested_seq_triple", prop_nested_seq_triple)
    , ("prop_nested_seq_multi", prop_nested_seq_multi)
    , ("prop_nested_seq_with_outer", prop_nested_seq_with_outer)
    , ("prop_compact_single", prop_compact_single)
    , ("prop_compact_multi", prop_compact_multi)
    , ("prop_dash_newline_seq", prop_dash_newline_seq)
    , ("prop_dash_newline_map", prop_dash_newline_map)
    , ("prop_list_of_objects", prop_list_of_objects)
    , ("prop_deep_mixed_nesting", prop_deep_mixed_nesting)
    , ("prop_map_with_seq_of_maps", prop_map_with_seq_of_maps)
    , ("prop_block_literal_simple", prop_block_literal_simple)
    , ("prop_block_folded_simple", prop_block_folded_simple)
    , ("prop_block_literal_strip", prop_block_literal_strip)
    , ("prop_block_literal_keep", prop_block_literal_keep)
    , ("prop_block_folded_strip", prop_block_folded_strip)
    , ("prop_block_folded_blank", prop_block_folded_blank)
    , ("prop_block_explicit_indent", prop_block_explicit_indent)
    , ("prop_block_folded_more_indent", prop_block_folded_more_indent)
    , ("prop_block_scalar_in_seq", prop_block_scalar_in_seq)
    , ("prop_block_empty", prop_block_empty)
    , ("prop_block_then_sibling", prop_block_then_sibling)
    , ("prop_block_header_comment", prop_block_header_comment)
    , ("prop_block_multiple", prop_block_multiple)
    , ("prop_block_indent_then_chomp", prop_block_indent_then_chomp)
    , ("prop_block_folded_multi_blank", prop_block_folded_multi_blank)
    , ("prop_block_eof_no_newline", prop_block_eof_no_newline)
    , ("prop_block_nested", prop_block_nested)
    , ("prop_block_deep_indent", prop_block_deep_indent)
    , ("prop_block_preserve_indent", prop_block_preserve_indent)
    , ("prop_doc_explicit_start", prop_doc_explicit_start)
    , ("prop_doc_start_space", prop_doc_start_space)
    , ("prop_doc_end", prop_doc_end)
    , ("prop_doc_start_and_end", prop_doc_start_and_end)
    , ("prop_multi_doc_two", prop_multi_doc_two)
    , ("prop_multi_doc_with_end", prop_multi_doc_with_end)
    , ("prop_multi_doc_three", prop_multi_doc_three)
    , ("prop_multi_doc_first_implicit", prop_multi_doc_first_implicit)
    ]

main : IO ()
main = test [properties]

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

prop_float_inf : Property
prop_float_inf = parseOk ".inf" (YFloat (1.0 / 0.0))

prop_float_neg_inf : Property
prop_float_neg_inf = parseOk "-.inf" (YFloat (negate $ 1.0 / 0.0))

prop_float_plus_inf : Property
prop_float_plus_inf = parseOk "+.inf" (YFloat (1.0 / 0.0))

-- NaN requires special handling since NaN != NaN (x /= x only for NaN)
prop_float_nan : Property
prop_float_nan = property1 $ case parseYAML Virtual ".nan" of
  Right [< YFloat x] => (x /= x) === True
  other => annotate ("Expected NaN but got: " ++ show other) >> failure

prop_float_Inf : Property
prop_float_Inf = parseOk ".Inf" (YFloat (1.0 / 0.0))

prop_float_NaN : Property
prop_float_NaN = property1 $ case parseYAML Virtual ".NaN" of
  Right [< YFloat x] => (x /= x) === True
  other => annotate ("Expected NaN but got: " ++ show other) >> failure

--------------------------------------------------------------------------------
--          Timestamp Tests
--------------------------------------------------------------------------------

prop_time_date : Property
prop_time_date = parseOk "2024-01-15" (YTime $ ATDate $ MkDate 2024 JAN 15)

prop_time_datetime : Property
prop_time_datetime =
  parseOk "2024-01-15T10:30:00"
    (YTime $ ATLocalDateTime $ LDT (MkDate 2024 JAN 15) (LT 10 30 0 Nothing))

prop_time_datetime_lower : Property
prop_time_datetime_lower =
  parseOk "2024-01-15t10:30:00"
    (YTime $ ATLocalDateTime $ LDT (MkDate 2024 JAN 15) (LT 10 30 0 Nothing))

prop_time_datetime_z : Property
prop_time_datetime_z =
  parseOk "2024-01-15T10:30:00Z"
    (YTime $ ATOffsetDateTime $ ODT (MkDate 2024 JAN 15) (OT (LT 10 30 0 Nothing) Z))

prop_time_datetime_offset : Property
prop_time_datetime_offset =
  parseOk "2024-01-15T10:30:00+05:30"
    (YTime $ ATOffsetDateTime $ ODT (MkDate 2024 JAN 15) (OT (LT 10 30 0 Nothing) (O Plus 5 30)))

prop_time_in_map : Property
prop_time_in_map =
  parseOk "date: 2024-01-15"
    (YMap [(YStr "date", YTime $ ATDate $ MkDate 2024 JAN 15)])

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
  (YMap [(YStr "age", YInt 30), (YStr "name", YStr "Alice")])

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
  (YMap [(YStr "bool", YBool True), (YStr "num", YInt 42), (YStr "str", YStr "hello")])

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
  (YSeq [YMap [(YStr "age", YInt 30), (YStr "name", YStr "alice")],
         YMap [(YStr "age", YInt 25), (YStr "name", YStr "bob")]])

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
--          Multi-line Plain Scalar Tests
--------------------------------------------------------------------------------

-- Simple two-line continuation: newline folds to space
prop_multiline_plain_simple : Property
prop_multiline_plain_simple = parseOk
  """
  key: line one
    line two
  """
  (YMap [(YStr "key", YStr "line one line two")])

-- Three-line continuation
prop_multiline_plain_three_lines : Property
prop_multiline_plain_three_lines = parseOk
  """
  key: line one
    line two
    line three
  """
  (YMap [(YStr "key", YStr "line one line two line three")])

-- Blank line preserved as newline
prop_multiline_plain_blank_line : Property
prop_multiline_plain_blank_line = parseOk
  """
  key: line one

    line two
  """
  (YMap [(YStr "key", YStr "line one\nline two")])

-- New key detected (mapping indicator ": " on continuation line)
-- This tests the YAML 1.2.2 spec disambiguation rule
prop_multiline_plain_new_key : Property
prop_multiline_plain_new_key = parseOk
  """
  - name: alice
    age: 30
  """
  (YSeq [YMap [(YStr "age", YInt 30), (YStr "name", YStr "alice")]])

-- Colon in content without space (port number style) - NOT a mapping indicator
prop_multiline_plain_colon_nospace : Property
prop_multiline_plain_colon_nospace = parseOk "server: localhost:8080"
  (YMap [(YStr "server", YStr "localhost:8080")])

-- URL with colon - colon followed by '/' is NOT a mapping indicator
prop_multiline_plain_url : Property
prop_multiline_plain_url = parseOk "url: http://example.com"
  (YMap [(YStr "url", YStr "http://example.com")])

-- Multi-line with subsequent key at same indent (ends scalar)
prop_multiline_plain_then_sibling : Property
prop_multiline_plain_then_sibling = parseOk
  """
  first: line one
    continued
  second: value
  """
  (YMap [(YStr "first", YStr "line one continued"),
         (YStr "second", YStr "value")])

-- Deep indentation continuation
prop_multiline_plain_deep_indent : Property
prop_multiline_plain_deep_indent = parseOk
  """
  outer:
    inner: start
      more content
  """
  (YMap [(YStr "outer", YMap [(YStr "inner", YStr "start more content")])])

--------------------------------------------------------------------------------
--          Tags
--------------------------------------------------------------------------------

-- !!str forces value to string (number becomes string)
prop_tag_str_number : Property
prop_tag_str_number = parseOk "value: !!str 123"
  (YMap [(YStr "value", YStr "123")])

-- !!str on boolean
prop_tag_str_bool : Property
prop_tag_str_bool = parseOk "value: !!str true"
  (YMap [(YStr "value", YStr "true")])

-- !!int forces string to integer
prop_tag_int_string : Property
prop_tag_int_string = parseOk "value: !!int \"42\""
  (YMap [(YStr "value", YInt 42)])

-- !!int on float truncates
prop_tag_int_float : Property
prop_tag_int_float = parseOk "value: !!int 3.7"
  (YMap [(YStr "value", YInt 3)])

-- !!float forces int to float
prop_tag_float_int : Property
prop_tag_float_int = parseOk "value: !!float 42"
  (YMap [(YStr "value", YFloat 42.0)])

-- !!bool forces string to boolean
prop_tag_bool_string : Property
prop_tag_bool_string = parseOk "value: !!bool \"true\""
  (YMap [(YStr "value", YBool True)])

-- !!null forces to null
prop_tag_null : Property
prop_tag_null = parseOk "value: !!null anything"
  (YMap [(YStr "value", YNull)])

-- Local tag (! prefix) - kept as-is since we don't know how to interpret
prop_tag_local : Property
prop_tag_local = parseOk "value: !custom data"
  (YMap [(YStr "value", YStr "data")])

-- Tag on sequence
prop_tag_on_seq : Property
prop_tag_on_seq = parseOk "value: !!seq [1, 2]"
  (YMap [(YStr "value", YSeq [YInt 1, YInt 2])])

-- Tag on mapping
prop_tag_on_map : Property
prop_tag_on_map = parseOk "value: !!map {a: 1}"
  (YMap [(YStr "value", YMap [(YStr "a", YInt 1)])])

-- Verbatim tag syntax !<uri>
prop_tag_verbatim : Property
prop_tag_verbatim = parseOk "value: !<tag:yaml.org,2002:str> 123"
  (YMap [(YStr "value", YStr "123")])

-- Tag in flow context
prop_tag_in_flow : Property
prop_tag_in_flow = parseOk "[!!str 1, !!int \"2\"]"
  (YSeq [YStr "1", YInt 2])

--------------------------------------------------------------------------------
--          Directives
--------------------------------------------------------------------------------

-- %YAML directive is skipped, content still parses
prop_directive_yaml : Property
prop_directive_yaml = parseOk
  """
  %YAML 1.2
  ---
  key: value
  """
  (YMap [(YStr "key", YStr "value")])

-- %TAG directive is skipped
prop_directive_tag : Property
prop_directive_tag = parseOk
  """
  %TAG !custom! tag:example.com,2024:
  ---
  key: value
  """
  (YMap [(YStr "key", YStr "value")])

-- Multiple directives
prop_directive_multiple : Property
prop_directive_multiple = parseOk
  """
  %YAML 1.2
  %TAG ! tag:example.com,2024:
  ---
  data: 123
  """
  (YMap [(YStr "data", YInt 123)])

-- Directive without document marker still works
prop_directive_no_doc_start : Property
prop_directive_no_doc_start = parseOk
  """
  %YAML 1.2
  key: value
  """
  (YMap [(YStr "key", YStr "value")])

--------------------------------------------------------------------------------
--          Complex Key Tests
--------------------------------------------------------------------------------

-- Simple scalar with explicit ? indicator
prop_complex_key_scalar : Property
prop_complex_key_scalar = parseOk
  """
  ? key
  : value
  """
  (YMap [(YStr "key", YStr "value")])

-- Flow sequence as key
prop_complex_key_flow_seq : Property
prop_complex_key_flow_seq = parseOk
  """
  ? [a, b]
  : value
  """
  (YMap [(YSeq [YStr "a", YStr "b"], YStr "value")])

-- Flow map as key
prop_complex_key_flow_map : Property
prop_complex_key_flow_map = parseOk
  """
  ? {x: 1}
  : value
  """
  (YMap [(YMap [(YStr "x", YInt 1)], YStr "value")])

-- Multiple complex keys
prop_complex_key_multiple : Property
prop_complex_key_multiple = parseOk
  """
  ? [a]
  : 1
  ? [b]
  : 2
  """
  (YMap [(YSeq [YStr "a"], YInt 1), (YSeq [YStr "b"], YInt 2)])

-- Complex key with colon on same line
prop_complex_key_inline_colon : Property
prop_complex_key_inline_colon = parseOk
  "? [x, y]: value"
  (YMap [(YSeq [YStr "x", YStr "y"], YStr "value")])

-- Complex key in flow context
prop_complex_key_in_flow : Property
prop_complex_key_in_flow = parseOk
  "{? [a]: 1, ? [b]: 2}"
  (YMap [(YSeq [YStr "a"], YInt 1), (YSeq [YStr "b"], YInt 2)])

-- Nested map as complex key
prop_complex_key_nested_map : Property
prop_complex_key_nested_map = parseOk
  """
  ? {name: alice, age: 30}
  : person1
  """
  (YMap [(YMap [(YStr "age", YInt 30), (YStr "name", YStr "alice")], YStr "person1")])

-- Mixed scalar and complex keys
prop_complex_key_mixed : Property
prop_complex_key_mixed = parseOk
  """
  simple: value
  ? [complex]
  : other
  """
  (YMap [(YStr "simple", YStr "value"), (YSeq [YStr "complex"], YStr "other")])

--------------------------------------------------------------------------------
--          Anchor and Alias Tests
--------------------------------------------------------------------------------

-- Simple anchor and alias on scalar
prop_anchor_simple : Property
prop_anchor_simple = parseOk
  """
  anchor: &a 42
  alias: *a
  """
  (YMap [(YStr "alias", YInt 42), (YStr "anchor", YInt 42)])

-- Anchor on flow sequence (on same line)
prop_anchor_seq : Property
prop_anchor_seq = parseOk
  """
  list: &items [a, b]
  copy: *items
  """
  (YMap [(YStr "copy", YSeq [YStr "a", YStr "b"]),
         (YStr "list", YSeq [YStr "a", YStr "b"])])

-- Anchor on flow mapping (on same line)
prop_anchor_map : Property
prop_anchor_map = parseOk
  """
  defaults: &def {x: 1}
  config: *def
  """
  (YMap [(YStr "config", YMap [(YStr "x", YInt 1)]),
         (YStr "defaults", YMap [(YStr "x", YInt 1)])])

-- Multiple aliases to same anchor
prop_anchor_multi_alias : Property
prop_anchor_multi_alias = parseOk
  """
  - &val 100
  - *val
  - *val
  """
  (YSeq [YInt 100, YInt 100, YInt 100])

-- Anchor reuse (later overwrites)
prop_anchor_reuse : Property
prop_anchor_reuse = parseOk
  """
  - &a 1
  - *a
  - &a 2
  - *a
  """
  (YSeq [YInt 1, YInt 1, YInt 2, YInt 2])

-- Anchor in flow context
prop_anchor_flow : Property
prop_anchor_flow = parseOk "{x: &a 1, y: *a}"
  (YMap [(YStr "x", YInt 1), (YStr "y", YInt 1)])

-- Anchor in flow sequence
prop_anchor_flow_seq : Property
prop_anchor_flow_seq = parseOk "[&a 1, *a, *a]"
  (YSeq [YInt 1, YInt 1, YInt 1])

-- Anchor with tag
prop_anchor_with_tag : Property
prop_anchor_with_tag = parseOk
  """
  val: &a !!str 123
  ref: *a
  """
  (YMap [(YStr "ref", YStr "123"), (YStr "val", YStr "123")])

-- Undefined alias (error)
prop_alias_undefined : Property
prop_alias_undefined = parseErr "*undefined"

-- Alias before anchor (error)
prop_alias_before_anchor : Property
prop_alias_before_anchor = parseErr
  """
  ref: *later
  val: &later 42
  """

-- Document scope (anchors reset at ---)
prop_anchor_doc_scope : Property
prop_anchor_doc_scope = parseErr
  """
  ---
  val: &a 1
  ---
  ref: *a
  """

-- Anchor with hyphen in name
prop_anchor_hyphen_name : Property
prop_anchor_hyphen_name = parseOk
  """
  val: &my-anchor 42
  ref: *my-anchor
  """
  (YMap [(YStr "ref", YInt 42), (YStr "val", YInt 42)])

-- Unused anchor is valid
prop_anchor_unused : Property
prop_anchor_unused = parseOk "&unused 42" (YInt 42)

-- Anchor on nested structure (using flow syntax)
prop_anchor_nested : Property
prop_anchor_nested = parseOk
  """
  outer: &ref {inner: {value: 1}}
  copy: *ref
  """
  (YMap [(YStr "copy", YMap [(YStr "inner", YMap [(YStr "value", YInt 1)])]),
         (YStr "outer", YMap [(YStr "inner", YMap [(YStr "value", YInt 1)])])])

-- Anchor on block-style nested map
prop_anchor_block_nested : Property
prop_anchor_block_nested = parseOk
  """
  defaults: &def
    timeout: 30
  ref: *def
  """
  (YMap [(YStr "defaults", YMap [(YStr "timeout", YInt 30)]),
         (YStr "ref", YMap [(YStr "timeout", YInt 30)])])

-- Anchor on block-style nested sequence
prop_anchor_block_seq : Property
prop_anchor_block_seq = parseOk
  """
  items: &list
    - a
    - b
  copy: *list
  """
  (YMap [(YStr "copy", YSeq [YStr "a", YStr "b"]),
         (YStr "items", YSeq [YStr "a", YStr "b"])])

-- YAML 1.2 spec Example 2.10: Node for Sammy Sosa appears twice
prop_spec_2_10 : Property
prop_spec_2_10 = parseOk
  """
  hr:
    - Mark McGwire
    - &SS Sammy Sosa
  rbi:
    - *SS
    - Ken Griffey
  """
  (YMap [(YStr "hr", YSeq [YStr "Mark McGwire", YStr "Sammy Sosa"]),
         (YStr "rbi", YSeq [YStr "Sammy Sosa", YStr "Ken Griffey"])])

-- YAML 1.2 spec Example 2.27 (simplified): Repeated billing info
prop_spec_2_27 : Property
prop_spec_2_27 = parseOk
  """
  bill-to: &id001
    given: Chris
    family: Dumars
  ship-to: *id001
  """
  (YMap [(YStr "bill-to", YMap [(YStr "family", YStr "Dumars"),
                                 (YStr "given", YStr "Chris")]),
         (YStr "ship-to", YMap [(YStr "family", YStr "Dumars"),
                                 (YStr "given", YStr "Chris")])])

-- YAML 1.2 spec Example 6.29: Node Anchors
prop_spec_6_29 : Property
prop_spec_6_29 = parseOk
  """
  First occurrence: &anchor Value
  Second occurrence: *anchor
  """
  (YMap [(YStr "First occurrence", YStr "Value"),
         (YStr "Second occurrence", YStr "Value")])

-- YAML 1.2 spec Example 7.1: Alias Nodes (anchor override)
prop_spec_7_1 : Property
prop_spec_7_1 = parseOk
  """
  First occurrence: &anchor Foo
  Second occurrence: *anchor
  Override anchor: &anchor Bar
  Reuse anchor: *anchor
  """
  (YMap [(YStr "First occurrence", YStr "Foo"),
         (YStr "Override anchor", YStr "Bar"),
         (YStr "Reuse anchor", YStr "Bar"),
         (YStr "Second occurrence", YStr "Foo")])

-- Anchor in nested sequence item
prop_anchor_in_nested_seq : Property
prop_anchor_in_nested_seq = parseOk
  """
  - &first
    - nested
    - items
  - *first
  """
  (YSeq [YSeq [YStr "nested", YStr "items"],
         YSeq [YStr "nested", YStr "items"]])

-- Multiple anchors at different nesting levels
prop_anchor_multi_level : Property
prop_anchor_multi_level = parseOk
  """
  outer: &outer
    inner: &inner value
    ref: *inner
  copy: *outer
  """
  (YMap [(YStr "copy", YMap [(YStr "inner", YStr "value"),
                              (YStr "ref", YStr "value")]),
         (YStr "outer", YMap [(YStr "inner", YStr "value"),
                               (YStr "ref", YStr "value")])])

-- Anchor on deeply nested structure
prop_anchor_deep_nested : Property
prop_anchor_deep_nested = parseOk
  """
  root:
    level1:
      level2: &deep
        level3: value
      ref: *deep
  """
  (YMap [(YStr "root", YMap [(YStr "level1", YMap [
    (YStr "level2", YMap [(YStr "level3", YStr "value")]),
    (YStr "ref", YMap [(YStr "level3", YStr "value")])])])])

-- Anchor in sequence, alias in sibling map
prop_anchor_seq_to_map : Property
prop_anchor_seq_to_map = parseOk
  """
  seq:
    - &item one
    - two
  map:
    first: *item
  """
  (YMap [(YStr "map", YMap [(YStr "first", YStr "one")]),
         (YStr "seq", YSeq [YStr "one", YStr "two"])])

-- Anchor on empty map
prop_anchor_empty_map : Property
prop_anchor_empty_map = parseOk
  """
  empty: &e {}
  copy: *e
  """
  (YMap [(YStr "copy", YMap []),
         (YStr "empty", YMap [])])

-- Anchor on empty sequence
prop_anchor_empty_seq : Property
prop_anchor_empty_seq = parseOk
  """
  empty: &e []
  copy: *e
  """
  (YMap [(YStr "copy", YSeq []),
         (YStr "empty", YSeq [])])

--------------------------------------------------------------------------------
--          Implicit Flow Key Tests
--------------------------------------------------------------------------------

-- Simple implicit key in flow sequence
prop_implicit_key_simple : Property
prop_implicit_key_simple = parseOk "[name: alice]"
  (YSeq [YMap [(YStr "name", YStr "alice")]])

-- Multiple implicit keys
prop_implicit_key_multiple : Property
prop_implicit_key_multiple = parseOk "[a: 1, b: 2]"
  (YSeq [YMap [(YStr "a", YInt 1)], YMap [(YStr "b", YInt 2)]])

-- Mixed: plain values and implicit keys
prop_implicit_key_mixed : Property
prop_implicit_key_mixed = parseOk "[plain, key: value, 42]"
  (YSeq [YStr "plain", YMap [(YStr "key", YStr "value")], YInt 42])

-- Implicit key with nested flow value
prop_implicit_key_nested : Property
prop_implicit_key_nested = parseOk "[items: [1, 2]]"
  (YSeq [YMap [(YStr "items", YSeq [YInt 1, YInt 2])]])

-- Colon in key (no space after internal colons)
prop_implicit_key_colon_in_key : Property
prop_implicit_key_colon_in_key = parseOk "[key:foo: bar]"
  (YSeq [YMap [(YStr "key:foo", YStr "bar")]])

-- Plain scalar with colons (no space after any colon)
prop_implicit_key_colon_no_space : Property
prop_implicit_key_colon_no_space = parseOk "[foo:bar:baz]"
  (YSeq [YStr "foo:bar:baz"])

--------------------------------------------------------------------------------
--          Merge Key Tests
--------------------------------------------------------------------------------

-- Simple merge: << inserts pairs from anchored map
prop_merge_simple : Property
prop_merge_simple = parseOk
  """
  base: &base
    a: 1
    b: 2
  extended:
    <<: *base
    c: 3
  """
  (YMap [(YStr "base", YMap [(YStr "a", YInt 1), (YStr "b", YInt 2)]),
         (YStr "extended", YMap [(YStr "a", YInt 1), (YStr "b", YInt 2), (YStr "c", YInt 3)])])

-- Merge with explicit key after (explicit key wins due to deduplication)
prop_merge_with_override : Property
prop_merge_with_override = parseOk
  """
  base: &base
    x: 1
  child:
    <<: *base
    x: 2
  """
  (YMap [(YStr "base", YMap [(YStr "x", YInt 1)]),
         (YStr "child", YMap [(YStr "x", YInt 2)])])

-- Merge sequence of maps
prop_merge_sequence : Property
prop_merge_sequence = parseOk
  """
  a: &a {x: 1}
  b: &b {y: 2}
  merged:
    <<: [*a, *b]
    z: 3
  """
  (YMap [(YStr "a", YMap [(YStr "x", YInt 1)]),
         (YStr "b", YMap [(YStr "y", YInt 2)]),
         (YStr "merged", YMap [(YStr "x", YInt 1), (YStr "y", YInt 2), (YStr "z", YInt 3)])])

-- Merge in flow mapping
prop_merge_flow : Property
prop_merge_flow = parseOk
  "base: &b {a: 1}\nchild: {<<: *b, b: 2}"
  (YMap [(YStr "base", YMap [(YStr "a", YInt 1)]),
         (YStr "child", YMap [(YStr "a", YInt 1), (YStr "b", YInt 2)])])

-- Multiple merge keys in same mapping
prop_merge_multiple : Property
prop_merge_multiple = parseOk
  """
  a: &a {x: 1}
  b: &b {y: 2}
  c:
    <<: *a
    <<: *b
    z: 3
  """
  (YMap [(YStr "a", YMap [(YStr "x", YInt 1)]),
         (YStr "b", YMap [(YStr "y", YInt 2)]),
         (YStr "c", YMap [(YStr "x", YInt 1), (YStr "y", YInt 2), (YStr "z", YInt 3)])])

-- Merge non-mapping (keeps as regular key-value pair)
prop_merge_non_map : Property
prop_merge_non_map = parseOk
  "x:\n  <<: not a map"
  (YMap [(YStr "x", YMap [(YStr "<<", YStr "not a map")])])

-- Quoted << is not a merge key (regular string key)
prop_merge_quoted_not_merge : Property
prop_merge_quoted_not_merge = parseOk
  "\"<<\": value"
  (YMap [(YStr "<<", YStr "value")])

-- Merge key with null value (no-op)
prop_merge_null : Property
prop_merge_null = parseOk
  """
  x:
    <<:
    a: 1
  """
  (YMap [(YStr "x", YMap [(YStr "a", YInt 1)])])

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
    , ("prop_float_inf", prop_float_inf)
    , ("prop_float_neg_inf", prop_float_neg_inf)
    , ("prop_float_plus_inf", prop_float_plus_inf)
    , ("prop_float_nan", prop_float_nan)
    , ("prop_float_Inf", prop_float_Inf)
    , ("prop_float_NaN", prop_float_NaN)
    , ("prop_time_date", prop_time_date)
    , ("prop_time_datetime", prop_time_datetime)
    , ("prop_time_datetime_lower", prop_time_datetime_lower)
    , ("prop_time_datetime_z", prop_time_datetime_z)
    , ("prop_time_datetime_offset", prop_time_datetime_offset)
    , ("prop_time_in_map", prop_time_in_map)
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
    , ("prop_multiline_plain_simple", prop_multiline_plain_simple)
    , ("prop_multiline_plain_three_lines", prop_multiline_plain_three_lines)
    , ("prop_multiline_plain_blank_line", prop_multiline_plain_blank_line)
    , ("prop_multiline_plain_new_key", prop_multiline_plain_new_key)
    , ("prop_multiline_plain_colon_nospace", prop_multiline_plain_colon_nospace)
    , ("prop_multiline_plain_url", prop_multiline_plain_url)
    , ("prop_multiline_plain_then_sibling", prop_multiline_plain_then_sibling)
    , ("prop_multiline_plain_deep_indent", prop_multiline_plain_deep_indent)
    , ("prop_tag_str_number", prop_tag_str_number)
    , ("prop_tag_str_bool", prop_tag_str_bool)
    , ("prop_tag_int_string", prop_tag_int_string)
    , ("prop_tag_int_float", prop_tag_int_float)
    , ("prop_tag_float_int", prop_tag_float_int)
    , ("prop_tag_bool_string", prop_tag_bool_string)
    , ("prop_tag_null", prop_tag_null)
    , ("prop_tag_local", prop_tag_local)
    , ("prop_tag_on_seq", prop_tag_on_seq)
    , ("prop_tag_on_map", prop_tag_on_map)
    , ("prop_tag_verbatim", prop_tag_verbatim)
    , ("prop_tag_in_flow", prop_tag_in_flow)
    , ("prop_directive_yaml", prop_directive_yaml)
    , ("prop_directive_tag", prop_directive_tag)
    , ("prop_directive_multiple", prop_directive_multiple)
    , ("prop_directive_no_doc_start", prop_directive_no_doc_start)
    , ("prop_complex_key_scalar", prop_complex_key_scalar)
    , ("prop_complex_key_flow_seq", prop_complex_key_flow_seq)
    , ("prop_complex_key_flow_map", prop_complex_key_flow_map)
    , ("prop_complex_key_multiple", prop_complex_key_multiple)
    , ("prop_complex_key_inline_colon", prop_complex_key_inline_colon)
    , ("prop_complex_key_in_flow", prop_complex_key_in_flow)
    , ("prop_complex_key_nested_map", prop_complex_key_nested_map)
    , ("prop_complex_key_mixed", prop_complex_key_mixed)
    , ("prop_anchor_simple", prop_anchor_simple)
    , ("prop_anchor_seq", prop_anchor_seq)
    , ("prop_anchor_map", prop_anchor_map)
    , ("prop_anchor_multi_alias", prop_anchor_multi_alias)
    , ("prop_anchor_reuse", prop_anchor_reuse)
    , ("prop_anchor_flow", prop_anchor_flow)
    , ("prop_anchor_flow_seq", prop_anchor_flow_seq)
    , ("prop_anchor_with_tag", prop_anchor_with_tag)
    , ("prop_alias_undefined", prop_alias_undefined)
    , ("prop_alias_before_anchor", prop_alias_before_anchor)
    , ("prop_anchor_doc_scope", prop_anchor_doc_scope)
    , ("prop_anchor_hyphen_name", prop_anchor_hyphen_name)
    , ("prop_anchor_unused", prop_anchor_unused)
    , ("prop_anchor_nested", prop_anchor_nested)
    , ("prop_anchor_block_nested", prop_anchor_block_nested)
    , ("prop_anchor_block_seq", prop_anchor_block_seq)
    , ("prop_spec_2_10", prop_spec_2_10)
    , ("prop_spec_2_27", prop_spec_2_27)
    , ("prop_spec_6_29", prop_spec_6_29)
    , ("prop_spec_7_1", prop_spec_7_1)
    , ("prop_anchor_in_nested_seq", prop_anchor_in_nested_seq)
    , ("prop_anchor_multi_level", prop_anchor_multi_level)
    , ("prop_anchor_deep_nested", prop_anchor_deep_nested)
    , ("prop_anchor_seq_to_map", prop_anchor_seq_to_map)
    , ("prop_anchor_empty_map", prop_anchor_empty_map)
    , ("prop_anchor_empty_seq", prop_anchor_empty_seq)
    , ("prop_implicit_key_simple", prop_implicit_key_simple)
    , ("prop_implicit_key_multiple", prop_implicit_key_multiple)
    , ("prop_implicit_key_mixed", prop_implicit_key_mixed)
    , ("prop_implicit_key_nested", prop_implicit_key_nested)
    , ("prop_implicit_key_colon_in_key", prop_implicit_key_colon_in_key)
    , ("prop_implicit_key_colon_no_space", prop_implicit_key_colon_no_space)
    , ("prop_merge_simple", prop_merge_simple)
    , ("prop_merge_with_override", prop_merge_with_override)
    , ("prop_merge_sequence", prop_merge_sequence)
    , ("prop_merge_flow", prop_merge_flow)
    , ("prop_merge_multiple", prop_merge_multiple)
    , ("prop_merge_non_map", prop_merge_non_map)
    , ("prop_merge_quoted_not_merge", prop_merge_quoted_not_merge)
    , ("prop_merge_null", prop_merge_null)
    ]

main : IO ()
main = test [properties]

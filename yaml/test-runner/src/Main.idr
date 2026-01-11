module Main

import Data.String
import System
import System.Directory
import System.File
import Text.YAML

-- Check if a file exists
fileExists : String -> IO Bool
fileExists path = do
  Right _ <- readFile path
    | Left _ => pure False
  pure True

-- Run a single test case
runTest : String -> String -> IO (String, Bool, String)
runTest testId content = do
  case parseYAML Virtual content of
    Left err => pure (testId, False, "Parse error: \{show err}")
    Right docs => pure (testId, True, show (docs <>> []))

-- Process a single test directory
processTest : String -> String -> IO (String, Bool, String)
processTest baseDir testId = do
  let inFile = baseDir ++ "/" ++ testId ++ "/in.yaml"
  let errorFile = baseDir ++ "/" ++ testId ++ "/error"
  hasError <- fileExists errorFile
  Right content <- readFile inFile
    | Left err => pure (testId, False, "Cannot read: \{show err}")
  case parseYAML Virtual content of
    Left err =>
      if hasError
        then pure (testId, True, "Expected error, got error")
        else pure (testId, False, "Unexpected parse error: \{show err}")
    Right docs =>
      if hasError
        then pure (testId, False, "Expected error but parsed successfully: \{show (docs <>> [])}")
        else pure (testId, True, show (docs <>> []))

-- List directories (test IDs)
listTests : String -> IO (List String)
listTests baseDir = do
  Right entries <- listDir baseDir
    | Left _ => pure []
  -- Filter to 4-character alphanumeric test IDs
  pure $ filter (\s => length s == 4) entries

main : IO ()
main = do
  args <- getArgs
  case args of
    -- Single file mode
    [_, path] => do
      Right content <- readFile path
        | Left err => putStrLn "Error reading file: \{show err}"
      case parseYAML Virtual content of
        Left err => putStrLn "Parse error:\n\{show err}"
        Right docs => do
          putStrLn "Parsed successfully:"
          for_ (docs <>> []) $ \doc => putStrLn (show doc)

    -- Test suite mode: yaml-test-runner --suite <dir>
    [_, "--suite", baseDir] => do
      tests <- listTests baseDir
      putStrLn "Found \{show (length tests)} tests"
      results <- for tests $ \testId => processTest baseDir testId
      let passed = filter (\(_, ok, _) => ok) results
      let failed = filter (\(_, ok, _) => not ok) results
      putStrLn "\n=== RESULTS ==="
      putStrLn "Passed: \{show (length passed)} / \{show (length results)}"
      putStrLn "\n=== FAILURES ==="
      for_ failed $ \(testId, _, msg) => putStrLn "\{testId}: \{msg}"

    _ => putStrLn "Usage:\n  yaml-test-runner <file.yaml>\n  yaml-test-runner --suite <test-suite-dir>"

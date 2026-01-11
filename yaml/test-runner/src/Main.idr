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

-- Result of processing a test: Success, Failure, or Skipped (empty test dir)
data TestResult = Pass String | Fail String String | Skip String

isPass : TestResult -> Bool
isPass (Pass _) = True
isPass _ = False

isFail : TestResult -> Bool
isFail (Fail _ _) = True
isFail _ = False

-- Process a single test directory
processTest : String -> String -> IO TestResult
processTest baseDir testId = do
  let inFile = baseDir ++ "/" ++ testId ++ "/in.yaml"
  let errorFile = baseDir ++ "/" ++ testId ++ "/error"
  -- First check if in.yaml exists (skip empty test directories)
  hasInput <- fileExists inFile
  if not hasInput
    then pure (Skip testId)
    else do
      hasError <- fileExists errorFile
      Right content <- readFile inFile
        | Left err => pure (Fail testId "Cannot read: \{show err}")
      case parseYAML Virtual content of
        Left err =>
          if hasError
            then pure (Pass testId)
            else pure (Fail testId "Unexpected parse error: \{show err}")
        Right docs =>
          if hasError
            then pure (Fail testId "Expected error but parsed successfully: \{show (docs <>> [])}")
            else pure (Pass testId)

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
      let passed = filter isPass results
      let failed = filter isFail results
      let skipped = length results `minus` (length passed + length failed)
      putStrLn "\n=== RESULTS ==="
      putStrLn "Passed: \{show (length passed)} / \{show (length passed + length failed)}"
      when (skipped > 0) $ putStrLn "Skipped: \{show skipped} (empty test directories)"
      putStrLn "\n=== FAILURES ==="
      for_ failed $ \r => case r of
        Fail testId msg => putStrLn "\{testId}: \{msg}"
        _ => pure ()

    _ => putStrLn "Usage:\n  yaml-test-runner <file.yaml>\n  yaml-test-runner --suite <test-suite-dir>"

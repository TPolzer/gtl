{-| Used for the parsing of program options of the GTL executable. -}
module Misc.ProgramOptions (
  TranslationMode(..),
  Options(..),
  getOptions,
  usage
) where

import System.Console.GetOpt
import System.Environment
import Control.Exception
import Prelude hiding (catch)
import Data.List (unfoldr)
import System.Directory (findExecutable)
import System.FilePath
import Data.Graph.Inductive.Query.Monad (mapSnd)
import Data.Set as Set (Set(..), empty, insert)

-- | Provides the operation mode for the GTL executable
data TranslationMode
     = NativeC -- ^ Generate a promela file which includes the generated C-functions of the synchronous components
     | Local -- ^ Check the validity of the specified contracts using backend-specific verifications
     | PromelaBuddy -- ^ Use a BDD abstraction to verify the GALS model
--      | Tikz
     | Pretty -- ^ Pretty print the resulting GALS model
     | Native -- ^ Translate the system to promela using the contracts as specifications for the component behaviour
     | UPPAAL -- ^ Generate a UPPAAL model to check the GALS model
     | SMTBMC -- ^ Use a SMT solver to check the GALS model
     | SMTInduction
     deriving (Show,Eq)

-- | Options that the user can pass to the GTL executable
data Options = Options
               { gtlFile :: FilePath -- ^ The file which contains the GTL specification
               , mode :: TranslationMode -- ^ The operation mode
               , traceFile :: Maybe FilePath -- ^ A generated trace-file to be used in the verification
               , outputPath :: String -- ^ Where to store generated files
               , showHelp :: Bool -- ^ Display the help information to the user?
               , showVersion :: Bool -- ^ Show the version of the executable to the user?
               , ccBinary :: String -- ^ Location of the C-compiler
               , ccFlags :: [String] -- ^ Flags to pass to the C-compiler
               , ldFlags :: [String] -- ^ Flags to pass to the linker
               , includes :: [String] -- ^ Extra header files to include
               , scadeRoot :: Maybe FilePath -- ^ Location of the SCADE suite
               , smtBinary :: Maybe FilePath
               , verbosity :: Int -- ^ Verbosity level
               , dryRun :: Bool
               , debug :: Set String
               , bmcCompleteness :: Bool
               , bmcBound :: Maybe Integer
               , useSonolar :: Bool
               , scheduling :: String
               }
               deriving Show

defaultOptions = Options
  { gtlFile = ""
  , mode = Native
  , traceFile = Nothing
  , outputPath = "."
  , showHelp = False
  , showVersion = False
  , ccBinary = "gcc"
  , ccFlags = []
  , ldFlags = []
  , includes = []
  , scadeRoot = Nothing
  , smtBinary = Nothing
  , verbosity = 0
  , dryRun = False
  , debug = Set.empty
  , bmcCompleteness = False
  , bmcBound = Nothing
  , useSonolar = False
  , scheduling = "none"
  }

modes :: [(String,TranslationMode)]
modes = [("native-c",NativeC),("local",Local),("promela-buddy",PromelaBuddy),{-("tikz",Tikz),-}("pretty",Pretty),("native",Native),("uppaal",UPPAAL),("smt_bmc",SMTBMC),("smt_ind",SMTInduction)]

scheduler :: [String]
scheduler = ["none","sync","fair","timed"]

modeString1 :: (Show a,Eq a) => a -> [a] -> String
modeString1 def names = buildOr [ show name ++ (if name==def
                                                then "(default)"
                                                else "") | name <- names ]

modeString2 :: (Show a,Eq b) => b -> [(a,b)] -> String
modeString2 def names = buildOr [ show name ++ (if md==def 
                                                then "(default)"
                                                else "") | (name,md) <- names ]

buildOr :: [String] -> String
buildOr [] = ""
buildOr [opt] = opt
buildOr (x:xs) = x++buildOr' xs
  where
    buildOr' [x] = " or "++x
    buildOr' (x:xs) = ", "++x++buildOr' xs

options :: [OptDescr (Options -> Options)]
options = [Option ['m'] ["mode"] (ReqArg (\str opt -> case lookup str modes of
                                             Just rmode -> opt { mode = rmode }
                                             Nothing -> error $ "Unknown mode "++show str
                                         ) "mode"
                                 ) ("The tranlation mode ("++modeString2 (mode defaultOptions) modes++")")
          ,Option ['t'] ["trace-file"] (ReqArg (\str opt -> opt { traceFile = Just str }) "file") "Use a trace file to restrict a simulation"
          ,Option ['o'] ["output-directory"] (ReqArg (\path opts -> opts { outputPath = path }) "path") "Path into which the output should be generated"
          ,Option ['h'] ["help"] (NoArg (\opt -> opt { showHelp = True })) "Show this help information"
          ,Option ['v'] ["version"] (NoArg (\opt -> opt { showVersion = True })) "Show version information"
          ,Option ['V'] ["verbosity"] (OptArg (\str opt -> opt { verbosity = maybe 1 read str }) "verbosity level") "How much additional information is printed? (default 1)"
          ,Option ['n'] ["dry-run"] (NoArg (\opt -> opt { dryRun = True })) "Perform a dry run only generating files and not executing anything."
          ,Option ['d'] ["debug"] (ReqArg (\str opt -> opt { debug = Set.insert str $ debug opt }) "option") "Give debugging options (e.g. -ddump-buchi)"
          ,Option ['c'] ["complete"] (NoArg (\opt -> opt { bmcCompleteness = True })) "Makes the bounded model checking procedure complete (WARNING: can increase runtime by a lot)"
          ,Option ['b'] ["bound"] (ReqArg (\str opt -> opt { bmcBound = Just $ read str }) "num") "Gives an explicit bound where to stop the bounded model checking"
          ,Option ['s'] ["scheduling"] (ReqArg (\str opt -> opt { scheduling = if elem str scheduler
                                                                               then str
                                                                               else error ("Unknown scheduling: "++str) }) "scheduler")
           ("The scheduling algorithm to use ("++modeString1 (scheduling defaultOptions) scheduler++")")
          ,Option [] ["sonolar"] (NoArg (\opt -> opt { useSonolar = True })) "Restricts the SMT code generator to a tiny subset of SMTLib2 to enable the use of the sonolar solver"
          ]

header :: String
header = unlines $ [
    "Usage: gtl [OPTION...] gtl-file"
    , "Used environment variables:"
    , " * CC - Path to compiler"
    , " * CFLAGS - Additional flags to be passed to compiler"
    , " * LDFLAGS - Additional flags to be passed to linker"
    , " * INCLUDES - Additional header files to include in generated code"
    , " * SCADE_ROOT - Path to the Scade root directory (e.g. C:\\Program Files\\Esterel Technologies\\SCADE 6.1.2)"
    , " * SMT_BINARY - Path to the SMT solver binary"
    , " All environment variables may be passed in the form <Variable>=<Value> as option."
  ]

-- | Information on how to use the executable.
usage :: String
usage = usageInfo header options

-- | Returns the user-supplied options by parsing the environment.
getOptions :: IO Options
getOptions = do
  args <- getArgs
  gcc <- catch (getEnv "CC") (\e -> const (return "gcc") (e::SomeException))
  cflags <- catch (fmap splitOptions $ getEnv "CFLAGS") (\e -> const (return []) (e::SomeException))
  ldflags <- catch (fmap splitOptions $ getEnv "LDFLAGS") (\e -> const (return []) (e::SomeException))
  smtbin <- catch (fmap Just $ getEnv "SMT_BINARY") (\e -> const (return Nothing) (e::SomeException))
  scadeRoot <- guessScadeRoot
  let start_opts = defaultOptions { ccBinary = gcc
                                  , ccFlags = cflags
                                  , ldFlags = ldflags
                                  , smtBinary = smtbin
                                  , scadeRoot = scadeRoot
                                  }
  case getOpt (ReturnInOrder parseFreeOptions) options args of
    (o, [], []) -> return $ foldl (flip id) start_opts o
    (_, opts, []) -> ioError . userError $ "Unparsed options: " ++ show opts
    (_,_,errs) -> ioError (userError $ concat errs ++ usageInfo header options)

-- | Parses the options which do not start with "-" or "--" but
-- are just assignments (as in CFLAGS="...") or the name of the
-- GTL file.
parseFreeOptions :: String -> (Options -> Options)
parseFreeOptions o =
  let (optName, value) = mapSnd (drop 1) $ span (/= '=') o
  in case optName of
    "CC" -> \opts -> opts { ccBinary = value }
    "CFLAGS" -> \opts -> opts { ccFlags = ccFlags opts ++ (splitOptions $ value) }
    "LDFLAGS" -> \opts -> opts { ldFlags = ldFlags opts ++ (splitOptions $ value) }
    "SCADE_ROOT" -> \opts -> opts { scadeRoot = Just value }
    "SMT_BINARY" -> \opts -> opts { smtBinary = Just value }
    otherwise -> if null value
      then (\opts -> if null $ gtlFile opts then opts { gtlFile = optName } else error "Only one file allowed")
      else error $ "Unknown option " ++ optName

-- | Splits program options by " -" into a list usable for
-- running processes with these options. Splitting by " " only is
-- not suitable as it would split path names which contain spaces.
splitOptions :: String -> [String]
splitOptions = map (prependIfNecessary '-') . (split (" -"))
  where
    prependIfNecessary :: Eq a => a -> [a] -> [a]
    prependIfNecessary s l@(x:xs) = if s == x then l else s:l

-- | Split list into tokens where the first list matches
split :: Eq a => [a] -> [a] -> [[a]]
split p = unfoldr (split' p)
  where
    split' :: Eq a => [a] -> [a] -> Maybe ([a], [a])
    split' _ [] = Nothing
    split' p l = Just (pre, drop (length p) post)
      where
        (pre, post) = span p l

        span :: Eq a => [a] -> [a] -> ([a], [a])
        span _ [] = ([], [])
        span s l@(x:xs)
          = if match s l then
            ([], l)
          else
            (x:m, r)
          where
            (m, r) = span s xs

        match [] _ = True
        match _ [] = False
        match (t:ts) (s:ss) = if t == s then match ts ss else False

guessScadeRoot :: IO (Maybe FilePath)
guessScadeRoot = do
  scadeRootEnv <- catch (getEnv "SCADE_ROOT") (\e -> const (return "") (e::SomeException))
  if null scadeRootEnv then do
      scadeExePath <- findExecutable "scade"
      case scadeExePath of
        Nothing -> return Nothing
        Just p -> return $ Just $ joinPath $ (filter isPartOfRoot) $ splitPath $ takeDirectory p
    else
      return $ Just scadeRootEnv
  where
    isPartOfRoot :: FilePath -> Bool
    isPartOfRoot "SCADE Suite" = False
    isPartOfRoot "bin" = False
    isPartOfRoot _ = True

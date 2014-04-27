{-# LANGUAGE TypeFamilies, RankNTypes #-}
module Language.GTL.Backend.NuSMV (NuSMV(..)) where

import Control.Arrow
import Control.Concurrent
import Control.Monad.State
import Control.Monad.Supply
import Data.Fix
import Data.Functor
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Language.GTL.Backend
import Language.GTL.DFA
import Language.GTL.Expression as G
import Language.GTL.LTL as L
import Language.GTL.Parser
import Language.GTL.Parser.Monad
import Language.GTL.Parser.Syntax
import Language.GTL.Translation
import Language.GTL.Types
import Language.NuSMV.Lexer
import Language.NuSMV.Misc
import Language.NuSMV.Parser
import Language.NuSMV.Pretty
import Language.NuSMV.Syntax as N
import Misc.ProgramOptions
import System.Directory
import System.Exit
import System.IO
import System.Process
import Text.ParserCombinators.ReadP as P
import Text.PrettyPrint

data NuSMV = NuSMV deriving (Show)

instance GTLBackend NuSMV where
  data GTLBackendModel NuSMV = NuSMVData {
    nuSMVFileName :: String,
    nuSMVName :: String
  } deriving (Show)
  backendName NuSMV = "NuSMV"
  initBackend NuSMV opts [file,name] = return NuSMVData { nuSMVFileName = file, nuSMVName = name }
  typeCheckInterface NuSMV nuSMVData modelInterface = return modelInterface
  cInterface NuSMV = error "NuSMV is not C-compatible!"
  backendGetAliases _ _ = M.empty
  backendVerify NuSMV nuSMVData cy exprs locals init constVars opts gtlName = do

    -- The gtl file is parsed a second time here, because we do not get type
    -- information for local/input/output variables from the caller.
    Right decls <- runGTLParser gtl <$> readFile (gtlFile opts)
    let isMod (Model m) = modelName m == nuSMVName nuSMVData
        isMod _ = False
        inputs = modelInputs $ (\(Model m) -> m) $ head $ filter isMod decls
        outputs = modelOutputs $ (\(Model m) -> m) $ head $ filter isMod decls
        locals = modelLocals $ (\(Model m) -> m) $ head $ filter isMod decls
        vars = M.unions [inputs, outputs, locals]
        enums = S.fromList $ map enum2str $ filter isEnum $ concatMap subtypes $ M.elems vars
        isEnum :: UnResolvedType -> Bool
        isEnum (Fix (UnResolvedType' (Right (GTLEnum _)))) = True
        isEnum _ = False
        enum2str (Fix (UnResolvedType' (Right (GTLEnum s)))) = s
        subtypes (Fix (UnResolvedType' (Right (GTLArray _ t)))) = subtypes t
        subtypes x = return x

    -- parse the implementation
    let file = nuSMVFileName nuSMVData
        component = nuSMVName nuSMVData
    (impl,depends) <- do
        content <- nusmv . alexScanTokens <$> readFile file
        let Just impl = findModule component
            findModule m = find ( (==m) . moduleName ) content
            gatherModules = S.toList . S.unions . map getDeps . mapMaybe findModule

            --fixpoint iteration of module dependencies
            depList = iterate gatherModules [component]
            Just (needed,_) = find (uncurry (==)) $ zip depList $ tail depList
            deps = mapMaybe findModule $ delete component needed
        return (impl, deps)

    let contracts = gtlToLTL (Just cy) <$> exprs
        isLTL (LTLAutomaton _) = False
        isLTL _ = True
        (ltls,automata) = partition isLTL contracts
        nusmvContracts = concat $ flip evalSupply [0..] $ do
          let l = map ltl2smv ltls
              -- map initial values to ltl constraints
              i = map (ltlinit . second (constantToExpr enums . fromJust)) $ M.toList init
          dfas <- forM automata (\(LTLAutomaton a) -> do
            let dfa = case determinizeBA a of
                  Just d -> d
                  _ -> error "Automata contracts with non-final states are not allowed"
            dfa2smv $ renameDFAStates $ minimizeDFA dfa
            )
          return (l:i:dfas)
        implContracted = impl {moduleBody = moduleBody impl ++ nusmvContracts}
        (ids,types) = unzip $ M.toList inputs
        inids = map (\x -> "__in" ++ show x) [1..length ids]
        intypes = map type2smv types
        id2expr = IdExpr . ComplexId Nothing . return . Left
        testProg = (++"\n") $ render $ prettyProgram $ [
          implContracted,
          Module {
              moduleName = "main",
              moduleParameter = [],
              moduleBody = [
                  VarDeclaration $
                  zip inids intypes ++ 
                  [
                      (moduleName impl ,ModuleType (moduleName impl) $ map id2expr inids)
                  ]
              ]
          }] ++ depends
    (path, h) <- openTempFile "." "nusmvBackend.smv"
    hPutStr h testProg
    hClose h
    (hin,hout,herr,pid) <- runInteractiveCommand $ "NuSMV -ctt " ++ path
    output <- hGetContents hout
    forkIO $ hGetContents herr >>= hPutStr stderr
    hClose hin
    let results = readP_to_S parseNuSMV output    
    r <- case results of
        [] -> putStr ("could not parse NuSMV output:\n" ++ output) >> return Nothing
        (((valid,err),""):_) -> do
            unless valid $ putStrLn err
            exitCode <- waitForProcess pid
            return $ if exitCode == ExitSuccess then Just valid else Nothing
    removeFile path
    return r

type ModuleProd a = StateT [ModuleElement] (Supply Int) a

parseNuSMV :: ReadP (Bool,String)
parseNuSMV = do
    let ctt = count 58 (P.char '#') >> P.char '\n'
        skip = void P.get
    manyTill skip ctt
    string "The transition relation is "
    t <- string "total:" <++ string "not total. "
    let total = t == "total:"
    terr <- manyTill P.get ctt
    specs <- many $ do
        string "-- specification "
        spec <- manyTill P.get $ string "IN "
        manyTill skip $ string "is "
        v <- string "true\n" <++ string "false\n"
        let valid = v == "true\n"
        err <- if valid then return [] else do
            string "-- as demonstrated by the following execution sequence\n"
            many $ do
                line <- manyTill P.get $ P.char '\n'
                when ("-- specification" `isPrefixOf` line) pfail
                return line
        return $ if valid then "" else
            "Specification " ++ spec ++ " is false. Counterexample:\n" ++ unlines err
    let res = total && all (=="") specs
    let err = ["The transition relation is not total:\n" ++ terr | not total] ++ filter (/="") specs
    eof
    return (res, concat err)

-- | returns all directly referenced ModuleType names in the input module
getDeps :: Module -> S.Set String
getDeps m = moduleName m `S.insert` S.unions (map getVarDeps $ moduleBody m)
    where
    getVarDeps (VarDeclaration ds) = S.unions $ map (getTypeDeps . snd) ds
    getVarDeps _ = S.empty
    getTypeDeps (ModuleType s _) = S.singleton s
    getTypeDeps _ = S.empty

-- | 'ltlinit (s, v)' = LTLSpec s = v
ltlinit :: (String, TypedExpr String) -> ModuleElement
ltlinit (id, expr) = LTLSpec $ expr2smv $ Fix $ Typed (Fix GTLBool) $
    BinRelExpr BinEq (Fix $ Typed (getType $ unfix expr) $ Var id 0 Input) expr

type2smv :: UnResolvedType -> TypeSpecifier
type2smv x = case unfix x of
  UnResolvedType' (Left s) -> error $ "unresolved type " ++ s
  UnResolvedType' (Right t) -> SimpleType $ type2smv' t
    where
      type2smv' x = case x of
        GTLInt -> TypeWord (Just True) $ ConstExpr $ ConstInteger 64
        GTLByte -> TypeWord (Just False) $ ConstExpr $ ConstInteger 8
        GTLBool -> TypeBool
        GTLFloat -> error "nusmv does not support floats"
        GTLEnum l -> TypeEnum $ map Left l
        GTLArray s t -> TypeArray (ConstExpr $ ConstInteger 0) (ConstExpr $ ConstInteger (s-1)) $
          (\(SimpleType t)->t) $ type2smv t
        GTLTuple _ -> error "nusmv does not support tuples"
        GTLNamed _ _ -> error "type aliases not implemented"


ltl2smv :: LTL (TypedExpr String) -> ModuleElement
ltl2smv = LTLSpec . convertL
    where
        convertL (Ground b) = ConstExpr $ ConstBool b
        convertL (Atom a) = expr2smv a
        convertL (Bin op a b) = BinExpr (binOp2smv op) (convertL a) (convertL b)
        convertL (Un op a) = UnExpr (convertOu op) $ convertL a
        convertOu = fromJust . flip lookup [(L.Not,OpNot),(L.Next,LTLX)]

-- | Translates a dfa to a nusmv implementation with an added fail-state if no
-- transition can be taken and specifies in LTL that the fail-state is never
-- reached. The supply is used for naming variables uniquely.
dfa2smv :: DFA [TypedExpr String] Integer -> Supply Int [ModuleElement]
dfa2smv dfa = do
  cid <- supply
  let n_state = "__contract" ++ show cid ++ "_state"
      i_state = ComplexId { idBase = Nothing, idNavigation = [Left n_state] }
      n_fail = n_state ++ "_fail"
      n_func x = n_state ++ "_"++show x
      trans = unTotal $ dfaTransitions dfa :: Map Integer [([TypedExpr String],Integer)]
  table <- concat <$> forM (M.toList trans) (\(from,tos) ->
    forM tos (\(guard,to) ->
        let exprs = foldl (BinExpr OpAnd) (BinExpr OpEq (IdExpr i_state) (ConstExpr $ ConstId $ n_func from)) $
                map expr2smv guard in
        return (exprs, ConstExpr $ ConstId $ n_func to)
      )
    )
  return [
    VarDeclaration [
      (n_state, SimpleType $ TypeEnum $ map Left $ (n_fail:) $ map n_func $ M.keys trans)
      ],
    AssignConstraint [
      (InitAssign, i_state,
        ConstExpr $ ConstId $ n_func $ dfaInit dfa),
      (NextAssign, i_state,
        CaseExpr $ table ++ [(ConstExpr $ ConstBool True, ConstExpr $ ConstId n_fail)])
      ],
    LTLSpec $ UnExpr LTLG $ UnExpr OpNot $ BinExpr OpEq (IdExpr i_state) $ ConstExpr $ ConstId n_fail
    ]

expr2smv :: TypedExpr String -> BasicExpr
expr2smv expr = case getValue $ unfix expr of
    Var name _ Input -> ConstExpr $ ConstId name
    Var name _ _ -> IdExpr ComplexId {idBase = Nothing, idNavigation = [Left name]}
    BinBoolExpr op a b -> binExpr2smv op a b
    BinRelExpr op a b -> case getType $ unfix a of
        Fix (GTLArray l te) -> case op of
            BinNEq -> UnExpr OpNot $ expr2smv $ Fix $ Typed t $ BinRelExpr BinEq a b
            BinEq -> foldl (BinExpr OpAnd) (ConstExpr $ ConstBool True) $ map (expr2smv . Fix . Typed t) $
                zipWith (BinRelExpr BinEq) (idx a) (idx b)
                where idx x = zipWith ((Fix.) . (Typed t .) . IndexExpr) (repeat x) [0..l-1]
        _ -> binExpr2smv op a b
    BinIntExpr op a b -> binExpr2smv op a b
    UnBoolExpr G.Not a -> UnExpr OpNot $ expr2smv a
    IndexExpr (Fix (Typed _ (Value (GTLArrayVal a)))) i -> expr2smv $ a !! fromInteger i
    IndexExpr a i -> flip IdxExpr (ConstExpr $ ConstInteger i) $ expr2smv a
    Value v -> ConstExpr $ case v of
        GTLIntVal i ->
            ConstWord WordConstant {wcSigned = Just True, wcBits = Just 64, wcValue = toInteger i}
        GTLByteVal b -> 
            ConstWord WordConstant {wcSigned = Just False, wcBits = Just 8, wcValue = toInteger b}
        GTLBoolVal b -> ConstBool b
        GTLFloatVal _ -> error "The NuSMV backend does not support floats."
        GTLEnumVal s -> ConstId s
        GTLArrayVal l -> error "Arrays can only be indexed or compared for equality."
        GTLTupleVal _ -> error "The NuSMV backend does not support tuples"
    x -> error $ "expr not implemented in expr2smv: " ++ show2 x
    where
        t = getType $ unfix expr
        binExpr2smv :: forall o . (BOp o, Eq o) =>
            o -> TypedExpr String -> TypedExpr String -> BasicExpr
        binExpr2smv op a b = let [ea,eb] = map expr2smv [a,b] in
                    BinExpr (binOp2smv op) ea eb

-- | type class to unify the different binary operators of gtl
class BOp o where
    binOp2smv :: Eq o => o -> N.BinOp
    binOp2smv = fromJust . flip lookup opLlist
    opLlist :: Eq o => [(o,N.BinOp)]

instance BOp BoolOp where
    opLlist = [(G.And,OpAnd),(G.Or,OpOr)]
instance BOp Relation where
    opLlist = [(BinLT,OpLT),(BinLTEq,OpLTE),(BinGT,OpGT),(BinGTEq,OpGTE),(BinEq,OpEq),(BinNEq,OpNeq),(BinAssign,error "assignment may not occur in this context")]
instance BOp IntOp where
    opLlist = [(G.OpPlus,N.OpPlus),(G.OpMinus,N.OpMinus),(G.OpMult,N.OpMult),(G.OpDiv,N.OpDiv)]
instance BOp L.BinOp where
    opLlist = [(L.And,OpAnd),(L.Or,OpOr),(L.Until,LTLU),(L.UntilOp,LTLV)]

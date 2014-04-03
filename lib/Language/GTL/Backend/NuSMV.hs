{-# LANGUAGE TypeFamilies, RankNTypes #-}
module Language.GTL.Backend.NuSMV (NuSMV(..)) where

import Control.Monad.State
import Control.Monad.Supply
import Data.Fix
import Data.Functor
import Data.Int
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
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
import Text.ParserCombinators.ReadP as ReadP
import Text.PrettyPrint

data NuSMV = NuSMV deriving (Show)

instance GTLBackend NuSMV where
  data GTLBackendModel NuSMV = NuSMVData {
    nuSMVFileName :: String,
    nuSMVName :: String
  } deriving (Show)
  backendName NuSMV = "NuSMV"
  initBackend NuSMV opts [file,name] = do
    return NuSMVData { nuSMVFileName = file, nuSMVName = name }
  typeCheckInterface NuSMV nuSMVData modelInterface = return modelInterface
  cInterface NuSMV = error "NuSMV is not C-compatible!"
  backendGetAliases _ _ = M.empty
  backendVerify NuSMV nuSMVData cy exprs locals init constVars opts gtlName = do
    -- THIS IS AN UGLY HACK
    Right decls <- runGTLParser gtl <$> (readFile $ gtlFile opts)
    let isMod (Model m) = modelName m == nuSMVName nuSMVData
        isMod _ = False
        inputs = modelInputs $ (\(Model m) -> m) $ head $ filter isMod decls
    --
    let file = nuSMVFileName nuSMVData
        component = nuSMVName nuSMVData
    impl <- do
        content <- nusmv . alexScanTokens <$> readFile file
        let Just impl = find ( (==component) . moduleName ) content
        return impl
    let contracts = gtlToLTL (Just cy) <$> exprs
        isLTL (LTLAutomaton _) = False
        isLTL _ = True
        (ltls,automata) = partition isLTL contracts
        nusmvContracts = concat $ flip evalSupply [0..] $ do
          l <- sequence $ map ltl2smv ltls
          dfas <- forM automata (\(LTLAutomaton a) -> do
            let dfa = case determinizeBA a of
                  Just d -> d
                  _ -> error "Automata contracts with non-final states are not allowed"
            dfa2smv $ renameDFAStates $ minimizeDFA $ dfa
            )
          return (l++dfas)
        implContracted = impl {moduleBody = moduleBody impl ++ nusmvContracts}
        (ids,types) = unzip $ M.toList inputs
        inids = map (\x -> "__in" ++ show x) [1..length ids]
        intypes = map type2smv types
        id2expr = IdExpr . ComplexId Nothing . return . Left
        testProg = (++"\n") $ render $ prettyProgram [
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
          }]
    (path, h) <- openTempFile "." "nusmvBackend.smv"
    hPutStr h testProg
    hClose h
    (hin,hout,herr,pid) <- runInteractiveCommand $ "NuSMV " ++ path
    output <- lines <$> hGetContents hout
    mapM hClose [hin,herr]
    let results = filter (not . null) $ map (readP_to_S parseNuSMVLine) output
    exitCode <- waitForProcess pid
    removeFile path
    return $! if exitCode == ExitSuccess then Just $ not $ [(" is false","")] `elem` results else Nothing

type ModuleProd a = StateT [ModuleElement] (Supply Int) a

parseNuSMVLine :: ReadP String 
parseNuSMVLine = do
    string "--"
    many ReadP.get
    res <- string " is true" +++ string " is false"
    eof
    return res

type2smv :: UnResolvedType -> TypeSpecifier
type2smv x = case unfix x of
  UnResolvedType' (Left s) -> error $ "unresolved type " ++ s
  UnResolvedType' (Right t) -> SimpleType $ type2smv' t
    where
      type2smv' x = case x of
        GTLInt -> TypeRange
          (ConstExpr $ ConstInteger $ fromIntegral (minBound :: Int64))
          (ConstExpr $ ConstInteger $ fromIntegral (maxBound :: Int64))
        GTLByte -> TypeWord Nothing $ ConstExpr $ ConstInteger 8
        GTLBool -> TypeBool
        GTLFloat -> error "nusmv does not support floats"
        GTLEnum l -> TypeEnum $ map Left l
        GTLArray s t -> TypeArray (ConstExpr $ ConstInteger 0) (ConstExpr $ ConstInteger (s-1)) $
          (\(SimpleType t)->t) $ type2smv t
        GTLTuple _ -> error "nusmv does not support tuples"
        GTLNamed _ _ -> error "type aliases not implemented"


ltl2smv :: LTL (TypedExpr String) -> Supply Int [ModuleElement]
ltl2smv = unwrapDef . convertL
    where
        convertL (Ground b) = return $ ConstExpr $ ConstBool b
        convertL (Atom a) = expr2smv a
        convertL (Bin op a b) = do
            ca <- convertL a
            cb <- convertL b
            return $ BinExpr (binOp2smv op) ca cb
        convertL (Un op a) = UnExpr (convertOu op) <$> convertL a
        convertOu = fromJust . flip lookup [(L.Not,OpNot),(L.Next,LTLX)]
        unwrapDef act = do
            (ltl,defs) <- runStateT act []
            return $ LTLSpec ltl : defs

dfa2smv :: DFA [TypedExpr String] Integer -> Supply Int [ModuleElement]
dfa2smv dfa = uncurry (++) <$> (flip runStateT [] $ do
  cid <- supply
  let n_state = "__contract" ++ show cid ++ "_state"
      i_state = ComplexId { idBase = Nothing, idNavigation = [Left n_state] }
      n_fail = n_state ++ "_fail"
      n_func x = n_state ++ "_"++show x
      trans = unTotal $ dfaTransitions dfa :: Map Integer [([TypedExpr String],Integer)]
  table <- concat <$> forM (M.toList trans) (\(from,tos) ->
    forM tos (\(guard,to) -> do
        exprs <- foldl (BinExpr OpAnd) (BinExpr OpEq (IdExpr i_state) (ConstExpr $ ConstId $ n_func from)) <$> mapM expr2smv guard
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
    ])

expr2smv :: TypedExpr String -> ModuleProd BasicExpr
expr2smv expr = case getValue $ unfix expr of
    Var name _ Input -> return $ ConstExpr $ ConstId name
    Var name _ _ -> return $ IdExpr $ ComplexId {idBase = Nothing, idNavigation = [Left name]}
    Value v -> ConstExpr <$> case v of
        GTLIntVal i -> return $ ConstInteger i
        GTLByteVal b -> return $ 
            ConstWord $ WordConstant {wcSigned = Just False, wcBits = Just 8, wcValue = toInteger b}
        GTLBoolVal b -> return $ ConstBool b
        GTLFloatVal _ -> error "floats are not handled by NuSMV"
        GTLEnumVal s -> return $ ConstId s
        GTLArrayVal l -> do 
            num <- lift $ supply
            let ident = "__array_define_" ++ show num
            content <- mapM expr2smv l
            modify ((ArrayDefine ident (ArrayContents content)):)
            return $ ConstId ident
        GTLTupleVal _ -> error "NuSMV does not handle tuples"
    BinBoolExpr op a b -> binExpr2smv op a b
    BinRelExpr op a b -> binExpr2smv op a b
    BinIntExpr op a b -> binExpr2smv op a b
    UnBoolExpr G.Not a -> UnExpr OpNot <$> expr2smv a
    IndexExpr a i -> flip IdxExpr (ConstExpr $ ConstInteger i) <$> expr2smv a
    x -> error $ "expr not implemented in expr2smv: " ++ show2 x
    where
        binExpr2smv :: forall o . (BOp o, Eq o) =>
            o -> TypedExpr String -> TypedExpr String -> ModuleProd BasicExpr
        binExpr2smv op a b = do
            ea <- expr2smv a
            eb <- expr2smv b
            return $ BinExpr (binOp2smv op) ea eb

class BOp o where
    binOp2smv :: Eq o => o -> N.BinOp
    binOp2smv = fromJust . flip lookup opLlist
    opLlist :: Eq o => [(o,N.BinOp)]

instance BOp BoolOp where
    opLlist = [(G.And,OpAnd),(G.Or,OpOr)]
instance BOp Relation where
    opLlist = [(BinLT,OpLT),(BinLTEq,OpLTE),(BinGT,OpGT),(BinGTEq,OpGTE),(BinEq,OpEq),(BinNEq,OpNeq),(BinAssign,error "assignment may not occur in this context")]
-- TODO implement mult, div in language-nusmv
instance BOp IntOp where
    opLlist = [(G.OpPlus,N.OpPlus),(G.OpMinus,N.OpMinus),(G.OpMult,error "mult not implemented"),(G.OpDiv,error "div not implemented")]
instance BOp L.BinOp where
    opLlist = [(L.And,OpAnd),(L.Or,OpOr),(L.Until,LTLU),(L.UntilOp,LTLV)]

{-# LANGUAGE TypeFamilies, RankNTypes #-}
module Language.GTL.Backend.NuSMV (NuSMV(..)) where

import Language.GTL.Backend
import qualified Data.Map as M
import Data.Map (Map)
import Data.Functor
import Data.List
import Language.NuSMV.Parser
import Language.NuSMV.Lexer
import Language.NuSMV.Syntax as N
import Language.GTL.Expression as G
import Language.GTL.Translation
import Language.GTL.LTL as L
import Language.GTL.Types
import Language.GTL.DFA
import Language.NuSMV.Misc
import Language.NuSMV.Pretty
import Data.Maybe
import Data.Fix
import Text.PrettyPrint
import Control.Monad.Supply
import Control.Monad.State

data NuSMV = NuSMV deriving (Show)

instance GTLBackend NuSMV where
  data GTLBackendModel NuSMV = NuSMVData {
    nuSMVFileName :: String,
    nuSMVName :: String
  }
  backendName NuSMV = "NuSMV"
  initBackend NuSMV opts [file,name] = do
    return NuSMVData { nuSMVFileName = file, nuSMVName = name }
  typeCheckInterface NuSMV nuSMVData modelInterface = return modelInterface
  cInterface NuSMV = error "NuSMV is not C-compatible!"
  backendGetAliases _ _ = M.empty
  backendVerify NuSMV nuSMVData cy exprs locals init constVars opts gtlName = do
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
    writeFile "test.smv" $ render $ prettyProgram [
        implContracted,
        Module {
            moduleName = "main",
            moduleParameter = [],
            moduleBody = [
                VarDeclaration [
                    ("in1",SimpleType TypeBool),
                    ("client",ModuleType "client" [IdExpr $ ComplexId Nothing [Left "in1"]])
                ]
            ]
        }
      ]
    return Nothing

type ModuleProd a = StateT [ModuleElement] (Supply Int) a

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
        exprs <- foldl (BinExpr OpAnd) (ConstExpr $ ConstBool True) <$> mapM expr2smv guard
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

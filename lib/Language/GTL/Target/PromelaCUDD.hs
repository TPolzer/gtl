{- Lascia ch'io pianga
   mia cruda sorte,
   e che sospiri la libertà.
   Il duolo infranga queste ritorte
   de' miei martiri sol per pietà.

                       -- G.F. Händel
-}
{-# LANGUAGE GADTs #-}
{-| Implements a verification mechanism that abstracts components by using their
    contract to build a state machine that acts on BDD.
 -}
module Language.GTL.Target.PromelaCUDD where

import Language.GTL.Translation
import Language.Promela.Syntax as Pr
import Language.GTL.LTL
import Language.GTL.Expression as GTL
import Language.GTL.Model
import Language.GTL.Types

import Data.Map as Map
import Data.Set as Set
import Control.Monad.Identity
import Control.Monad.State
import Prelude hiding (foldl,concat,catch)
import Data.Foldable
import Data.List (intersperse)

import System.IO.Error (isDoesNotExistError)
import Language.GTL.ErrorRefiner
import Control.Exception.Extensible
import System.Directory

import Misc.ProgramOptions as Opts
import Misc.VerificationEnvironment

-- | An internal representation of a translated GTL model.
data TransModel = TransModel
                  { varsInit :: Map String String
                  , varsIn :: Map String Integer
                  , varsOut :: Map String (Map (Maybe (String,String)) (Set Integer))
                  , stateMachine :: Buchi ([Integer],[Integer],[TypedExpr String])
                  , checkFunctions :: [String]
                  } deriving Show

-- | An internal representation of a translated GTL program.
data TransProgram = TransProgram
                    { transModels :: Map String TransModel
                    , transClaims :: Buchi [Integer]
                    , claimChecks :: [String]
                    } deriving Show

-- | Helper function to securely delete temporary files.
--   Deletes a file if it exists, if not, ignore it.
deleteTmp :: FilePath -> IO ()
deleteTmp fp = catchJust (\e -> if isDoesNotExistError e
                                then Just ()
                                else Nothing) (removeFile fp) (const $ return ())

-- | Do a complete verification of a given GTL file
verifyModel :: Opts.Options
               -> String -- ^ Name of the GTL file without extension
               -> GTLSpec String -- ^ The GTL file contents
               -> IO ()
verifyModel opts name decls = do
  let prog = buildTransProgram decls
      pr = translateContracts prog
  traceFiles <- runVerification opts name pr
  parseTraces opts name traceFiles (traceToAtoms prog)

-- | Given a list of transitions, give a list of atoms that have to hold for each transition.
traceToAtoms :: TransProgram -- ^ The program to work on
                -> [(String,Integer)] -- ^ The transitions, given in the form (model,transition-number)
                -> Trace
traceToAtoms prog trace = fmap (\(mdl,st) -> let tmdl = (transModels prog)!mdl
                                                 entr = (stateMachine tmdl)!st
                                                 (_,_,atoms) = vars entr
                                             in fmap (mapGTLVars (\n -> (mdl,n))) atoms) trace

-- | Helper function to convert the name of a GTL variable into the
--   translated C-representation.
varName :: Bool -> String -> String -> Integer -> String
varName nvr mdl var lvl = (if nvr
                           then "never_"
                           else "conn_")++mdl++"_"++var++(if lvl==0
                                                          then ""
                                                          else "_"++show lvl)

-- | Convert a translated GTL program into a PROMELA module.
translateContracts :: TransProgram -> [Pr.Module]
translateContracts prog
  = let include = Pr.CDecl $ unlines ["\\#include <cudd/cudd.h>"
                                     ,"\\#include <cudd_arith.h>"
                                     ,"\\#include <assert.h>"
                                     ,"DdManager* manager;"]
        states = [ Pr.CState ("DdNode* "++varName False name var n) "Global" (Just "NULL")
                 | (name,mdl) <- Map.toList $ transModels prog
                 , (var,hist) <- Map.toList (varsIn mdl)
                 , n <- [0..hist] ] ++
                 [ Pr.CState ("DdNode* "++varName True name var lvl) "Global" (Just "NULL")
                 | (name,mdl) <- Map.toList $ transModels prog
                 , (var,set) <- Map.toList (varsOut mdl)
                 , lvl <- case Map.lookup Nothing set of
                   Nothing -> []
                   Just lvls -> [0..(Set.findMax lvls)]
                 ]
        procs = fmap (\(name,mdl) -> let steps = translateModel name mdl
                                         proc = Pr.ProcType { Pr.proctypeActive = Nothing
                                                            , Pr.proctypeName = name
                                                            , Pr.proctypeArguments = []
                                                            , Pr.proctypePriority = Nothing
                                                            , Pr.proctypeProvided = Nothing
                                                            , Pr.proctypeSteps = steps
                                                            }
                                     in (name,proc)) (Map.toList (transModels prog))
        check_funcs = Pr.CCode $ unlines $
                      [ impl | mdl <- Map.elems (transModels prog), impl <- checkFunctions mdl ] ++
                      claimChecks prog ++
                      [ unlines $ ["void reset_"++name++"(State* now) {"] ++
                        ["  "++vname lvl++" = "++(if lvl==0
                                                  then "DD_ONE(manager)"
                                                  else vname (lvl-1))++";"
                        | (from,tos) <- Map.toList (varsOut mdl), (to,lvls) <- Map.toList tos,
                          let hist = case to of
                                Nothing -> Set.findMax lvls
                                Just (q,n) -> (varsIn ((transModels prog)!q))!n,
                          let vname l = case to of
                                Just (q,n) -> "now->"++varName False q n l
                                Nothing -> "now->"++varName True name from l,
                          lvl <- reverse [0..hist] ]++
                        ["}"]
                      | (name,mdl) <- Map.toList (transModels prog) ]
        init = prInit [ prAtomic $ [ StmtCCode $ unlines $
                                     [ "manager = Cudd_Init(32,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);"] ++
                                     [ "now."++varName False name var clvl++" = Cudd_ReadOne(manager);"
                                     | (name,mdl) <- Map.toList $ transModels prog,
                                       (var,lvl) <- Map.toList $ varsIn mdl,
                                       clvl <- [0..lvl]
                                     ] ++
                                     [ "now."++varName True name var lvl++" = Cudd_ReadOne(manager);"
                                     | (name,mdl) <- Map.toList $ transModels prog,
                                       (var,outs) <- Map.toList $ varsOut mdl,
                                       lvl <- case Map.lookup Nothing outs of
                                         Nothing -> []
                                         Just lvls -> [0..(Set.findMax lvls)]
                                     ] ++
                                     concat [ let trgs = if Map.member var (varsIn mdl)
                                                         then ["now.conn_"++name++"_"++var]
                                                         else [ case outp of
                                                                   Nothing -> "now.never_"++name++"_"++var
                                                                   Just (q,n) -> "now.conn_"++q++"_"++n
                                                              | outp <- Map.keys ((varsOut mdl)!var) ]
                                              in [ head trgs++" = "++e++";"
                                                 , "Cudd_Ref("++head trgs++");"] ++
                                                 [ trg++" = "++head trgs | trg <- tail trgs ]
                                            | (name,mdl) <- Map.toList (transModels prog),
                                              (var,e) <- Map.toList (varsInit mdl) ]
                                   ]
                        ++ [ StmtRun name [] | (name,_) <- procs ]
                      ]
        nevers = [ prNever $ translateNever (transClaims prog)]
    in [include]++states++[check_funcs]++[ pr | (_,pr) <- procs]++[init]++nevers

-- | Convert a translated GTL model into a PROMELA process body.
translateModel :: String -- ^ The name of the model
                  -> TransModel -- ^ The actual model
                  -> [Pr.Step]
translateModel name mdl
  = let states = fmap (\(st,entr)
                       -> Pr.StmtLabel ("st"++show st) $
                          prAtomic [ Pr.StmtPrintf ("ENTER "++show st++"\n") [],
                                     Pr.StmtCCode $ unlines $ ["reset_"++name++"(&now);" ] ++ [ "assign_"++name++show n++"(&now);" | n <- (\(_,y,_) -> y) $ vars entr ],
                                     prIf [ (if not $ Prelude.null $ (\(x,_,_) -> x) $ vars nentr
                                             then [ Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                                    [ "cond_"++name++show n++"(&now)" | n <- (\(x,_,_) -> x) $ vars nentr ] ]
                                             else []) ++ [Pr.StmtGoto $ "st"++show succ ]
                                          | succ <- Set.toList $ successors entr, let nentr = (stateMachine mdl)!succ ]
                                   ]
                      ) (Map.toList $ stateMachine mdl)
        inits = prIf [ [prAtomic $ (if not $ Prelude.null $ (\(x,_,_) -> x) $ vars entr
                                    then [ Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                           [ "cond_"++name++show n++"(&now)" | n <- (\(x,_,_) -> x) $ vars entr ] ]
                                    else []) ++ [Pr.StmtGoto $ "st"++show st ] ]
                     | (st,entr) <- Map.toList $ stateMachine mdl, isStart entr ]
    in fmap toStep $ inits:states

-- | Translate a buchi automaton representing a verify expression into a never claim.
translateNever :: Buchi [Integer] -> [Pr.Step]
translateNever buchi
  = let rbuchi = translateGBA buchi
        showSt (i,j) = show i++"_"++show j
        states = fmap (\(st,entr)
                        -> let body = prAtomic [ prIf [ (if Prelude.null (vars nentr)
                                                        then []
                                                        else [Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                                              [ "cond__never"++show n++"(&now)" | n <- vars nentr ]]) ++
                                                        [Pr.StmtGoto $ "st"++showSt succ]
                                                      | succ <- Set.toList $ successors entr,
                                                        let nentr = rbuchi!succ ]
                                               ]
                           in Pr.StmtLabel ("st"++showSt st) $ if finalSets entr
                                                               then Pr.StmtLabel ("accept"++showSt st) body
                                                               else body
                      ) (Map.toList rbuchi)
        inits = prIf [ (if Prelude.null (vars entr)
                        then []
                        else [Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                              [ "cond__never"++show n++"(&now)" | n <- vars entr ]]) ++
                       [Pr.StmtGoto $ "st"++showSt st]
                     | (st,entr) <- Map.toList rbuchi,
                       isStart entr
                     ]
    in fmap toStep $ StmtSkip:inits:states

-- | A cache that maps atoms to C-functions that represent them.
--   The C-functions are encoded by a unique number, whether they are a test- or
--   assignment-function and their source code representation.
type AtomCache = Map (TypedExpr (Maybe String,String)) (Integer,Bool,String)

-- | A map from component names to output variable informations.
type OutputMapping = Map String (Map (Maybe (String,String)) (Set Integer))

-- | Parse a GTL expression to a C-function.
--   Returns the unique number of the function and whether its a test- or assignment-function.
parseGTLExpr :: AtomCache -- ^ A cache of already parsed atoms
                -> Maybe (String,OutputMapping) -- ^ Informations about the containing component
                -> TypedExpr (Maybe String,String) -- ^ The atom to parse
                -> ((Integer,Bool),AtomCache)
parseGTLExpr cache arg expr = let (idx,isinp,res) = case getValue expr of
                                    Var name lvl -> parseGTLRelation cache arg BinEq (GTL.var GTLBool name lvl) (GTL.constant True)
                                    UnBoolExpr GTL.Not nexpr -> case getValue (unfix nexpr) of 
                                      Var name lvl -> parseGTLRelation cache arg BinEq (GTL.var GTLBool name lvl) (GTL.constant False)
                                    BinRelExpr rel l r -> parseGTLRelation cache arg rel (unfix l) (unfix r)
                              in ((idx,isinp),Map.insert expr (idx,isinp,res) cache)

{-
parseGTLAtom :: AtomCache -- ^ A cache of already parsed atoms
                -> Maybe (String,OutputMapping) -- ^ Informations about the containing component
                -> TypedExpr (Maybe String,String) -- ^ The atom to parse
                -> ((Integer,Bool),AtomCache)
parseGTLAtom mp arg at
  = case Map.lookup at mp of
    Just (i,isinp,_) -> ((i,isinp),mp)
    Nothing -> let (idx,isinp,res) = case at of
                     GTLBoolExpr expr p -> parseGTLBoolExpr mp arg expr p
               in ((idx,isinp),Map.insert at (idx,isinp,res) mp)

parseGTLBoolExpr :: AtomCache
                    -> Maybe (String,OutputMapping)
                    -> BoolExpr (Maybe String,String)
                    -> Bool
                    -> (Integer,Bool,String)
parseGTLBoolExpr mp arg (RelExpr rel l r) p = parseGTLRelation mp arg (if p then rel else relNot rel) l r
parseGTLBoolExpr mp arg (BoolVar var) p = parseGTLRelation mp arg BinEq (VarExpr var) (GTL.ConstExpr (Constant (GTLBoolVal p) GTLBool))
-}
-- | Parse a GTL relation into a C-Function.
--   Returns a unique number for the resulting function, whether its a test- or assignment function and
--   its source-code representation.
parseGTLRelation :: AtomCache -- ^ A cache of parsed atoms
                    -> Maybe (String,OutputMapping) -- ^ Informations about the containing component
                    -> Relation -- ^ The relation type to parse
                    -> GTL.TypedExpr (Maybe String,String) -- ^ Left hand side of the relation
                    -> GTL.TypedExpr (Maybe String,String) -- ^ Right hand side of the relation
                    -> (Integer,Bool,String)
parseGTLRelation mp arg rel lhs rhs
  = let lvars = [ (v,lvl) | ((Nothing,v),_,lvl,_) <- getVars lhs, Map.member v outps ]
        rvars = [ (v,lvl) | ((Nothing,v),_,lvl,_) <- getVars rhs, Map.member v outps ]
        idx = fromIntegral $ Map.size mp
        name = case arg of
          Nothing -> Nothing
          Just (n,_) -> Just n
        rname = case name of
          Nothing -> error "Invalid use of unqualified variable"
          Just n -> n
        outps = case arg of
          Nothing -> Map.empty
          Just (_,s) -> s
        (res,isinp) = (case lvars of
                          [] -> case getValue rhs of
                            Var (Nothing,n) lvl -> if Map.member n outps
                                                    then (createBDDAssign idx rname n (outps!n) (relTurn rel) lhs,False)
                                                    else error "No output variable in relation"
                            _ -> case rvars of
                              [] -> (createBDDCompare idx name rel lhs rhs,True)
                              _ -> error "Output variables must be alone"
                          _ -> case getValue lhs of
                            Var (Nothing,n) lvl -> (createBDDAssign idx rname n (outps!n) rel rhs,False)
                            _ -> case lvars of
                              [] -> (createBDDCompare idx name rel lhs rhs,True)
                              _ -> error "Output variables must be alone"
                      ) :: (String,Bool)
    in (idx,isinp,res)

-- | Create a BDD assignment
createBDDAssign :: Integer -- ^ How many temporary variables have been used so far?
                     -> String -- ^ The current component name
                     -> String -- ^ The name of the target variable
                     -> Map (Maybe (String,String)) (Set Integer) -- ^ A mapping of output variables
                     -> Relation -- ^ The relation used to assign the BDD
                     -> GTL.TypedExpr (Maybe String,String) -- ^ The expression to assign the BDD with
                     -> String
createBDDAssign count q n outs rel expr
  = let trgs = [ maybe ("now->"++varName True q n lvl) (\(q',n') -> "now->"++varName False q' n' lvl) var
               | (var,lvls) <- Map.toList outs
               , lvl <- Set.toList lvls]
        (cmd2,te) = case rel of
          BinEq -> ([],e)
          BinNEq -> ([],"Cudd_Not("++e++")")
          GTL.BinGT -> (["DdNode* extr = "++e++";",
                         "Cudd_Ref(extr);",
                         "CUDD_ARITH_TYPE min;",
                         "int min_found = Cudd_bddMinimum(manager,extr,0,&min);",
                         "assert(min_found);",
                         "Cudd_RecursiveDeref(manager,extr);"
                        ],"Cudd_Not(Cudd_bddLessThanEqual(manager,min,0))")
          BinGTEq -> (["DdNode* extr = "++e++";",
                       "Cudd_Ref(extr);",
                       "CUDD_ARITH_TYPE min;",
                       "int min_found = Cudd_bddMinimum(manager,extr,0,&min);",
                       "assert(min_found);",
                       "Cudd_RecursiveDeref(manager,extr);"
                      ],"Cudd_Not(Cudd_bddLessThan(manager,min,0))")
          GTL.BinLT -> (["DdNode* extr = "++e++";",
                         "Cudd_Ref(extr);",
                         "CUDD_ARITH_TYPE max;",
                         "int max_found = Cudd_bddMaximum(manager,extr,0,&max);",
                         "assert(max_found);",
                         "Cudd_RecursiveDeref(manager,extr);"
                        ],"Cudd_bddLessThan(manager,max,0)")
          BinLTEq -> (["DdNode* extr = "++e++";",
                       "Cudd_Ref(extr);",
                       "CUDD_ARITH_TYPE max;",
                       "int max_found = Cudd_bddMaximum(manager,extr,0,&max);",
                       "assert(max_found);",
                       "Cudd_RecursiveDeref(manager,extr);"
                      ],"Cudd_bddLessThanEqual(manager,max,0)")
        (cmd,de,_,e) = createBDDExpr 0 (Just q) expr
    in unlines ([ "void assign_"++q++show count++"(State* now) {"] ++
                fmap ("  "++) (cmd++cmd2) ++
                ["  "++head trgs++" = "++te++";"]++
                fmap (\trg -> "  "++trg++" = "++head trgs++";") (tail trgs)++
                ["  Cudd_Ref("++head trgs++");"
                ]++
                fmap ("  "++) de ++
                ["}"])

-- | Create a comparison operation between two BDD.
createBDDCompare :: Integer -- ^ How many temporary variables have been used?
                      -> Maybe String -- ^ If the comparision is part of a contract, give the name of the component, otherwise `Nothing'
                      -> Relation -- ^ The relation used to compare the BDDs
                      -> GTL.TypedExpr (Maybe String,String) -- ^ Expression representing BDD 1
                      -> GTL.TypedExpr (Maybe String,String) -- ^ Expression representing BDD 2
                      -> String
createBDDCompare count q rel expr1 expr2
  = let (cmd1,de1,v,e1) = createBDDExpr 0 q expr1
        (cmd2,de2,_,e2) = createBDDExpr v q expr2
    in unlines $ ["int cond_"++(maybe "_never" id q)++show count++"(State* now) {"]++
       fmap ("  "++) (cmd1++cmd2)++
       ["  DdNode* lhs = "++e1++";"
       ,"  Cudd_Ref(lhs);"
       ,"  DdNode* rhs = "++e2++";"
       ,"  Cudd_Ref(rhs);"
       ,"  int res;"
       ]++(case rel of
              GTL.BinEq -> ["  res = Cudd_bddAnd(manager,lhs,rhs)!=Cudd_Not(Cudd_ReadOne(manager));"]
              GTL.BinNEq -> ["  res = !((lhs==rhs) && Cudd_bddIsSingleton(manager,lhs,0));"]
              GTL.BinLT -> ["  CUDD_ARITH_TYPE lval,rval;",
                            "  int lval_found = Cudd_bddMinimum(manager,lhs,0,&lval);",
                            "  int rval_found = Cudd_bddMaximum(manager,rhs,0,&rval);",
                            "  res = lval_found && rval_found && (lval < rval);"]
              GTL.BinLTEq -> ["  CUDD_ARITH_TYPE lval,rval;",
                              "  int lval_found = Cudd_bddMinimum(manager,lhs,0,&lval);",
                              "  int rval_found = Cudd_bddMaximum(manager,rhs,0,&rval);",
                              "  res = lval_found && rval_found && (lval <= rval);"]
              GTL.BinGT -> ["  CUDD_ARITH_TYPE lval,rval;",
                            "  int lval_found = Cudd_bddMaximum(manager,lhs,0,&lval);",
                            "  int rval_found = Cudd_bddMinimum(manager,rhs,0,&rval);",
                            "  res = lval_found && rval_found && (lval > rval);"]
              GTL.BinGTEq -> ["  CUDD_ARITH_TYPE lval,rval;",
                              "  int lval_found = Cudd_bddMaximum(manager,lhs,0,&lval);",
                              "  int rval_found = Cudd_bddMinimum(manager,rhs,0,&rval);",
                              "  res = lval_found && rval_found && (lval >= rval);"]
          )++
       ["  Cudd_RecursiveDeref(manager,rhs);",
        "  Cudd_RecursiveDeref(manager,lhs);"]++
       fmap ("  "++) (de2++de1)++
       ["  return res;",
        "}"]

-- | A class of types that have a representation as a BDD.
class BDDConst t where
  -- | Convert a value to the BDD C-representation.
  bddConst :: t -> String

instance BDDConst Int where
  bddConst n = "Cudd_bddSingleton(manager,"++show n++",0)"

instance BDDConst Bool where
  bddConst v = let var = "Cudd_bddIthVar(manager,0)"
               in if v then var
                  else "Cudd_Not("++var++")"

constrBddConst :: GTLValue a -> String
constrBddConst (GTLIntVal x) = bddConst (fromIntegral x::Int)
constrBddConst (GTLBoolVal x) = bddConst x

-- | Convert a GTL expression into a C-expression.
--   Returns a list of statements that have to be executed before the expression,
--   one that has to be executed afterwards, a number of temporary variables used
--   and the resulting C-expression.
createBDDExpr :: Integer -- ^ The current number of temporary variables
                 -> Maybe String -- ^ The current component
                 -> GTL.TypedExpr (Maybe String,String) -- ^ The GTL expression
                 -> ([String],[String],Integer,String)
createBDDExpr v mdl expr = case getValue expr of
  Var (q,n) lvl -> case mdl of
    Nothing -> case q of
      Just rq -> ([],[],v,"now->"++varName True rq n lvl)
      Nothing -> error "verify claims must not contain qualified variables"
    Just rmdl -> ([],[],v,"now->"++varName False rmdl n lvl)
  Value x -> ([],[],v, constrBddConst x)
  BinIntExpr op lhs rhs -> let (cmd1,de1,v1,e1) = createBDDExpr v mdl (unfix lhs)
                               (cmd2,de2,v2,e2) = createBDDExpr v1 mdl (unfix rhs)
                           in (cmd1++cmd2++["DdNode* tmp"++show v2++" = "++e1++";",
                                            "Cudd_Ref(tmp"++show v2++");",
                                            "DdNode* tmp"++show (v2+1)++" = "++e2++";",
                                            "Cudd_Ref(tmp"++show (v2+1)++");"],
                               ["Cudd_RecursiveDeref(manager,tmp"++show (v2+1)++");"
                               ,"Cudd_RecursiveDeref(manager,tmp"++show v2++");"]++de2++de1,
                               v2+2,
                               (case op of
                                   OpPlus -> "Cudd_bddPlus"
                                   OpMinus -> "Cudd_bddMinus"
                                   OpMult -> "Cudd_bddTimes"
                                   OpDiv -> "Cudd_bddDivide"
                               )++"(manager,tmp"++show v2++",tmp"++show (v2+1)++",0)")

buildTransProgram :: GTLSpec String -> TransProgram
buildTransProgram gtl
  = let tmodels1 = Map.mapWithKey (\k m -> let outp_map = fmap (const Map.empty) (gtlModelOutput m)
                                               hist = maximumHistory (gtlModelContract m)
                                               inits = fmap (\i -> case i of
                                                                Nothing -> "Cudd_ReadOne(manager)"
                                                                Just d -> case unfix d of
                                                                  GTLIntVal i -> "Cudd_bddSingleton(manager,"++show i++",0)"
                                                                  _ -> error "Init expressions must be ints atm"

                                                            ) (gtlModelDefaults m)
                                           in TransModel { varsInit = inits
                                                         , varsIn = Map.mapWithKey (\k v -> hist!k) (gtlModelInput m)
                                                         , varsOut = outp_map
                                                         , stateMachine = undefined
                                                         , checkFunctions = undefined
                                                         }
                                  ) (gtlSpecModels gtl)
        (tclaims,fclaims) = runState
                            (gtlToBuchi (\ats -> do
                                            mp <- get
                                            let (c,nmp) = foldl (\(cs,cmp2) at -> let ((n,True),nmp) = parseGTLExpr cmp2 Nothing (mapGTLVars (\(q,n) -> (Just q,n)) at)
                                                                                  in (n:cs,nmp)
                                                                ) ([],mp) ats
                                            put nmp
                                            return c
                                        ) (GTL.gnot (gtlSpecVerify gtl)))
                            Map.empty
        tmodels2 = foldl (\cmdls (GTLConnPt f fv [],GTLConnPt t tv [])
                          -> Map.adjust (\mdl -> mdl { varsOut = Map.insertWith (Map.unionWith Set.union) fv
                                                                 (Map.singleton (Just (t,tv)) (Set.singleton 0))
                                                                 (varsOut mdl)
                                                     }) f cmdls) tmodels1 (gtlSpecConnections gtl)
        tmodels3 = foldl (\cmdls' ((q,n),_,lvl,_) ->
                           Map.adjust (\mdl -> mdl { varsOut = Map.insertWith (Map.unionWith Set.union)
                                                               n (Map.singleton Nothing (Set.singleton lvl))
                                                               (varsOut mdl)
                                                   }) q cmdls'
                         ) tmodels2 $ getVars (gtlSpecVerify gtl)
        tmodels4 = Map.foldrWithKey
                   (\k m cur -> Map.adjust
                                (\entr -> let (sm,fm) = runState (gtlToBuchi
                                                                  (\ats -> do
                                                                      mp <- get
                                                                      let (c,a,nmp) = foldl (\(chks,ass,cmp) at
                                                                                             -> let ((n,f),nmp) = parseGTLExpr cmp (Just (k,varsOut entr)) (mapGTLVars (\n -> (Nothing,n)) at)
                                                                                                in (if f then (n:chks,ass,nmp)
                                                                                                    else (chks,n:ass,nmp))
                                                                                            ) ([],[],mp) ats
                                                                      put nmp
                                                                      return (c,a,ats)
                                                                  ) (gtlModelContract m)) Map.empty
                                          in entr { stateMachine = sm
                                                  , checkFunctions = fmap (\(_,_,f) -> f) (Map.elems fm)
                                                  }
                                ) k cur
                   ) tmodels3 (gtlSpecModels gtl)
    in TransProgram { transModels = tmodels4
                    , transClaims = tclaims
                    , claimChecks = fmap (\(_,_,f) -> f) $ Map.elems fclaims
                    }

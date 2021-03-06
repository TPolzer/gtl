{-# LANGUAGE FlexibleContexts, TupleSections, DeriveDataTypeable #-}

{-| This module provides a data structure for type-checked GTL specifications.
 -}
module Language.GTL.Model (GTLSpec(..)
                          ,GTLModel(..)
                          ,GTLInstance(..)
                          ,GTLContract(..)
                          ,GTLConnectionPoint(..)
                          ,gtlParseSpec
                          ,gtlContractExpression
                          ,getInstanceVariableType
                          ,getEnums
                          ) where

import Language.GTL.Parser.Token (BinOp(GOpAnd))
import Language.GTL.Parser.Syntax
import Language.GTL.Parser.Monad
import Language.GTL.Backend.All
import Language.GTL.Expression
import Language.GTL.Types
import Data.Map as Map hiding (map,foldl,mapMaybe)
import Data.Set as Set hiding (map,foldl)
import Data.Either (partitionEithers)
import Prelude hiding (mapM)
import Data.Traversable (mapM)
import Misc.ProgramOptions
import Control.Monad.Error hiding (mapM)
import Data.Maybe (mapMaybe)
import Data.Typeable

type ErrorIO = ErrorT String IO

-- | A parsed and typechecked GTL model.
data GTLModel a = GTLModel
                  { gtlModelContract :: [GTLContract a] -- ^ The contract of the model as a boolean formula.
                  , gtlModelBackend :: AllBackend -- ^ An abstract model in a synchronous specification language.
                  , gtlModelInput :: Map a GTLType -- ^ The input variables with types of the model.
                  , gtlModelOutput :: Map a GTLType -- ^ The output variables with types of the model.
                  , gtlModelLocals :: Map a GTLType -- ^ The local variables with types of the model.
                  , gtlModelDefaults :: Map a (Maybe GTLConstant) -- ^ Default values for inputs. `Nothing' means any value.
                  , gtlModelCycleTime :: Integer -- ^ Cycle time in us
                  , gtlModelConstantInputs :: Map a (GTLType, GTLConstant)
                  } deriving (Eq,Ord,Typeable,Show)

-- | A contract is a formula together with the information whether or not the contract is guaranteed to be true.
--   If the contract is guaranteed to be true, it is not checked during local verification.
data GTLContract a = GTLContract
                     { gtlContractIsGuaranteed :: Bool
                     , gtlContractFormula :: TypedExpr a
                     } deriving (Eq,Ord,Typeable,Show)

-- | Generate a single expression from all non-guaranteed contracts in a list of contracts by conjunction.
gtlContractExpression :: [GTLContract a] -> TypedExpr a
gtlContractExpression cons = case mapMaybe (\con -> if gtlContractIsGuaranteed con
                                                    then Nothing
                                                    else Just $ gtlContractFormula con) cons of
  [] -> constant True
  xs -> foldl1 gand xs

-- | Represents the start or end of a connection, by specifying the instance
--   name, the variable name and a list of indices that refer to the right
--   component of the variable.
data GTLConnectionPoint a = GTLConnPt String a [Integer] deriving (Eq,Ord,Show)

-- | A GTL specification represents a type checked GTL file.
data GTLSpec a = GTLSpec
               { gtlSpecModels :: Map String (GTLModel a) -- ^ All models in the specification.
               , gtlSpecInstances :: Map String (GTLInstance a)
               , gtlSpecVerify :: TypedExpr (String,a) -- ^ A formula to verify.
               , gtlSpecConnections :: [(GTLConnectionPoint a,GTLConnectionPoint a)] -- ^ Connections between models.
               } deriving (Eq,Ord,Show)

-- | A GTL instance is a concrete manifestation of a model.
data GTLInstance a = GTLInstance
                     { gtlInstanceModel :: String -- ^ The model of which this is an instance
                     , gtlInstanceContract :: [GTLContract a] -- ^ Additional contract
                     , gtlInstanceDefaults :: Map a (Maybe GTLConstant) -- ^ Additional default values
                     } deriving (Eq,Ord,Show)

-- | Get the type of a variable which resides in an instance.
getInstanceVariableType :: (Ord a,Show a) => GTLSpec a -- ^ The GTL specification
                           -> Bool -- ^ Whether the variable is an input variable ('True') or an output variable ('False')
                           -> String -- ^ The name of the instance
                           -> a -- ^ The name of the variable
                           -> GTLType
getInstanceVariableType spec inp inst var = case Map.lookup inst (gtlSpecInstances spec) of
  Nothing -> error $ "Internal error: Instance "++show inst++" not found."
  Just rinst -> case Map.lookup (gtlInstanceModel rinst) (gtlSpecModels spec) of
    Nothing -> error $ "Internal error: Model "++show (gtlInstanceModel rinst)++" not found"
    Just mdl -> case Map.lookup var (if inp then gtlModelInput mdl else gtlModelOutput mdl) of
      Nothing -> error $ "Internal error: Variable "++show var++" not found."
      Just tp -> tp

-- | Parse a GTL model from a unchecked model declaration.
gtlParseModel :: AllBackend -> [(String, PExpr)] -> Map String GTLType ->  Map String UnResolvedType -> ModelDecl -> ErrorIO (String,GTLModel String,Set [String])
gtlParseModel back constDecls realiases aliases mdl = do
  inps <- mapM (resolveType realiases aliases) (modelInputs mdl)
  outps <- mapM (resolveType realiases aliases) (modelOutputs mdl)
  locs <- mapM (resolveType realiases aliases) (modelLocals mdl)
  (inp,outp) <- allTypecheck back (inps,outps)
  let allType = Map.unions [inp,outp,locs]
      enums = getEnums allType
  constInputs <- checkConstInputs allType enums constDecls
  expr <- mapM (gtlParseContract inp outp allType enums) (modelContract mdl)
  lst <- mapM (\(var,init) -> case init of
                  InitAll -> return (var,Nothing)
                  InitOne c -> do
                    ce <- makeTypedExpr (\q n _ -> throwError "Init expression may not contain variables"::ErrorIO (String,VarUsage)) allType enums c
                    case Map.lookup var allType of
                      Nothing -> throwError $ "Unknown variable: "++show var++" in model "++modelName mdl
                      Just tp -> if getType (unfix ce) `isSubtypeOf` tp
                                 then (case getConstant ce of
                                          Just p -> return $ (var,Just p)
                                          Nothing -> throwError $ "Init expression must be a constant"
                                      )
                                 else throwError $ show var ++ " has type "++show tp++", but is initialized with "++show (getType $ unfix ce)) (modelInits mdl)
  return (modelName mdl,GTLModel { gtlModelContract = expr
                                 , gtlModelBackend = back
                                 , gtlModelInput = inp
                                 , gtlModelOutput = outp
                                 , gtlModelLocals = locs
                                 , gtlModelDefaults = Map.fromList lst
                                 , gtlModelCycleTime = modelCycleTime mdl
                                 , gtlModelConstantInputs = constInputs
                                 },enums)

gtlParseContract :: Map String GTLType -> Map String GTLType -> Map String GTLType -> Set [String] -> Contract -> ErrorT String IO (GTLContract String)
gtlParseContract inp outp allTypes enums con = do
  con' <- makeTypedExpr
          (\q n inf -> case q of
              Nothing -> return (n,if Map.member n inp
                                   then Input
                                   else (if Map.member n outp
                                         then Output
                                         else (case inf of
                                                  Nothing -> StateIn
                                                  Just ContextIn -> StateIn
                                                  Just ContextOut -> StateOut
                                              )
                                        ))
              _ -> throwError "Contract may not contain qualified variables")
          allTypes enums (contractFormula con)
  return (GTLContract { gtlContractIsGuaranteed = contractIsGuaranteed con
                      , gtlContractFormula = con'})

-- | Get all possible enum types.
getEnums :: Map a GTLType -> Set [String]
getEnums mp = Set.unions $ fmap getEnums' (Map.elems mp)
  where
    getEnums' :: GTLType -> Set [String]
    getEnums' (Fix (GTLEnum xs)) = Set.singleton xs
    getEnums' (Fix (GTLArray sz tp)) = getEnums' tp
    getEnums' (Fix (GTLTuple xs)) = Set.unions (fmap getEnums' xs)
    getEnums' (Fix (GTLNamed name tp)) = getEnums' tp
    getEnums' _ = Set.empty

splitArgs :: [ModelArgs] -> ([String], [(String, PExpr)])
splitArgs = partitionEithers . map mArgsToEither
  where
    mArgsToEither :: ModelArgs -> Either String (String, PExpr)
    mArgsToEither (StrArg s) = Left s
    mArgsToEither (ConstantDecl var val) = Right (var, val)

checkConstInputs :: MonadError String m => Map String GTLType -> Set [String] -> [(String, PExpr)] -> m (Map String (GTLType, GTLConstant))
checkConstInputs allTypes enums = liftM Map.fromList . mapM (makeTypedConst allTypes enums)
  where
    makeTypedConst :: MonadError String m => Map String GTLType -> Set [String] -> (String, PExpr) -> m (String, (GTLType, GTLConstant))
    makeTypedConst allTypes enums (n, v) = do
      v' <- makeTypedExpr makeVar Map.empty enums v
      case getConstant v' of
        Just v'' -> case Map.lookup n allTypes of
          Just t -> return (n, (t, v''))
          Nothing -> throwError $ "Variable " ++ show n ++ " not declared in constant declaration"
        Nothing -> throwError $ "Expected constant expression in constant declaration for " ++ show n

    makeVar q n _ = case q of
      Nothing -> return (n, Input)
      Just _ -> throwError $ "Qualified names for constants not supported"

-- | Parse a GTL specification from an unchecked list of declarations.
gtlParseSpec :: Options -> [Declaration] -> ErrorIO (GTLSpec String)
gtlParseSpec opts decls = do
  let aliases = foldl (\mp decl -> case decl of
                          TypeAlias name tp -> Map.insert name tp mp
                          _ -> mp) Map.empty decls
  init_mdls <- sequence [ do
                             let (args, constDecls) = splitArgs (modelArgs mdl)
                             mback <- liftIO $ initAllBackend (modelType mdl) opts args
                             case mback of
                               Nothing -> throwError $ "Couldn't initialize backend "++(modelType mdl)
                               Just back -> return (mdl,back,constDecls)
                        | Model mdl <- decls
                        ]
  let all_aliases = Map.unions [ allAliases back | (_,back,_) <- init_mdls ]
  mdls <- sequence [ gtlParseModel back cd all_aliases aliases m | (m,back,cd) <- init_mdls ]
  let mdl_mp = Map.fromList [ (name,mdl) | (name,mdl,_) <- mdls ]
      enums = Set.unions [ enum | (_,_,enum) <- mdls ]
  insts <- sequence
           [ do
                mdl <- case Map.lookup (instanceModel i) mdl_mp of
                  Nothing -> throwError $ "Model "++(instanceModel i)++" not found."
                  Just m -> return m
                contr <- mapM (gtlParseContract (gtlModelInput mdl) (gtlModelOutput mdl) (Map.union (gtlModelInput mdl) (gtlModelOutput mdl)) enums) (instanceContract i)
                return (instanceName i,GTLInstance { gtlInstanceModel = instanceModel i
                                                   , gtlInstanceContract = contr
                                                   , gtlInstanceDefaults = Map.empty
                                                   })
           | Instance i <- decls ]
  let inst_mp = Map.fromList insts
      alltp = Map.fromList [ ((q,n),tp)
                           | (q,inst) <- insts
                           , let mdl = mdl_mp!(gtlInstanceModel inst)
                           , (n,tp) <- Map.toList $ Map.union (gtlModelInput mdl) (gtlModelOutput mdl)
                           ]
  vexpr <- makeTypedExpr (\q n inf -> case q of
                               Nothing -> throwError "No unqualified variables allowed in verify clause"
                               Just rq -> return ((rq,n),Input)
                           ) alltp enums (case concat [ v | Verify (VerifyDecl v) <- decls ] of
                                           [] -> (startPosn,GConstBool True)
                                           x -> foldl1 (\l@(p,_) r -> (p,GBin GOpAnd NoTime l r)) x)
  conns <- sequence [ do
                         finst <- case Map.lookup f inst_mp of
                           Nothing -> throwError $ "Instance "++f++" not found."
                           Just x -> return x
                         let fmdl = mdl_mp!(gtlInstanceModel finst)
                         tinst <- case Map.lookup t inst_mp of
                           Nothing -> throwError $ "Instance "++t++" not found."
                           Just x -> return x
                         let tmdl = mdl_mp!(gtlInstanceModel tinst)
                         fvar <- case Map.lookup fv (gtlModelOutput fmdl) of
                           Nothing -> throwError $ "Variable "++f++"."++fv++" not found or not an output variable."
                           Just x -> return x
                         tvar <- case Map.lookup tv (gtlModelInput tmdl) of
                           Nothing -> throwError $ "Variable "++t++"."++tv++" not found or not an input variable."
                           Just x -> return x
                         ftp <- resolveIndices fvar fi
                         ttp <- resolveIndices tvar ti
                         if ftp `isSubtypeOf` ttp then return (GTLConnPt f fv fi,GTLConnPt t tv ti)
                           else throwError $ "Type mismatch between "++f++"."++fv++show fi++"("++show ftp++") and "++t++"."++tv++show ti++"("++show ttp++")."
            |  Connect (ConnectDecl f fv fi t tv ti) <- decls ]
  return $ GTLSpec { gtlSpecModels = mdl_mp
                   , gtlSpecInstances = inst_mp
                   , gtlSpecVerify = vexpr
                   , gtlSpecConnections = conns
                   }

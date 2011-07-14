{-# LANGUAGE GADTs, ExistentialQuantification, StandaloneDeriving, ScopedTypeVariables,
    TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-| Translates GTL expressions into LTL formula.
 -}
module Language.GTL.Translation(
  gtlToBuchi,
  gtlToLTL
  ) where

import Language.GTL.Expression as GTL
import Language.GTL.Types as GTL
import Language.GTL.LTL as LTL
import Language.GTL.Buchi
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl,foldl1,concat,mapM)
import Data.List (genericLength)

import Data.Set as Set
import Data.Map as Map

-- | Translates a GTL expression into a buchi automaton.
--   Needs a user supplied function that converts a list of atoms that have to be
--   true into the variable type of the buchi automaton.
gtlToBuchi :: (Monad m,Show v,Ord v) => ([GTL.TypedExpr v] -> m a) -> GTL.TypedExpr v -> m (Buchi a)
gtlToBuchi f expr = mapM (\co -> do
                             nvars <- f (fmap (\(at,p) -> if p
                                                          then at
                                                          else distributeNot at
                                              ) $ Set.toList (vars co))
                             return $ co { vars = nvars }
                         ) $
                    ltlToBuchi GTL.distributeNot (gtlToLTL expr)

---- | Extract all variables with their history level from an atom.
--getAtomVars :: GTLAtom v -> [(v,Integer)]
--getAtomVars (GTLBoolExpr e _) = getVarsBoolExpr e

instance Ord v => AtomContainer [TypedExpr v] (TypedExpr v) where
  atomsTrue = []
  atomSingleton True x = [x]
  atomSingleton False x = [distributeNot x]
  compareAtoms x y = compareAtoms' EEQ x y
    where
      compareAtoms' p [] [] = p
      compareAtoms' p [] _  = case p of
        EEQ -> EGT
        EGT -> EGT
        _ -> EUNK
      compareAtoms' p (x:xs) ys = case compareAtoms'' p x ys of
        Nothing -> case p of
          EEQ -> compareAtoms' ELT xs ys
          ELT -> compareAtoms' ELT xs ys
          ENEQ -> ENEQ
          _ -> EUNK
      compareAtoms'' p x [] = Nothing
      compareAtoms'' p x (y:ys) = case compareExpr x y of
        EEQ -> Just (p,ys)
        ELT -> case p of
          EEQ -> Just (ELT,ys)
          ELT -> Just (ELT,ys)
          _ -> Just (EUNK,ys)
        EGT -> case p of
          EEQ -> Just (EGT,ys)
          EGT -> Just (EGT,ys)
          _ -> Just (EUNK,ys)
        ENEQ -> Just (ENEQ,ys)
        EUNK -> case compareAtoms'' p x ys of
          Nothing -> Nothing
          Just (p',ys') -> Just (p',y:ys')
  mergeAtoms [] ys = Just ys
  mergeAtoms (x:xs) ys = case mergeAtoms' x ys of
    Nothing -> Nothing
    Just ys' -> mergeAtoms xs ys'
    where
      mergeAtoms' x [] = Just [x]
      mergeAtoms' x (y:ys) = case compareExpr x y of
        EEQ -> Just (y:ys)
        ELT -> Just (x:ys)
        EGT -> Just (y:ys)
        EUNK -> case mergeAtoms' x ys of
          Nothing -> Nothing
          Just ys' -> Just (y:ys')
        ENEQ -> Nothing

-- | Translate a GTL expression into a LTL formula.
gtlToLTL :: Ord v => TypedExpr v -> LTL (TypedExpr v)
gtlToLTL expr
  | getType expr == GTLBool = case getValue expr of
    Var _ _ -> Atom expr
    Value (GTLBoolVal x) -> Ground x
    BinBoolExpr op l r -> case op of
      GTL.And -> LTL.Bin LTL.And (gtlToLTL (unfix l)) (gtlToLTL (unfix r))
      GTL.Or -> LTL.Bin LTL.Or (gtlToLTL (unfix l)) (gtlToLTL (unfix r))
      GTL.Implies -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL (unfix l))) (gtlToLTL (unfix r))
      GTL.Until -> LTL.Bin LTL.Until (gtlToLTL (unfix l)) (gtlToLTL (unfix r))
    BinRelExpr rel lhs rhs -> case fmap Atom $ flattenRel rel (unfix lhs) (unfix rhs) of
      [e] -> e
      es -> foldl1 (LTL.Bin LTL.And) es
    UnBoolExpr op p -> case op of
      GTL.Not -> LTL.Un LTL.Not (gtlToLTL (unfix p))
      GTL.Always -> LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL (unfix p))
      GTL.Next -> LTL.Un LTL.Next (gtlToLTL (unfix p))
      GTL.Finally Nothing -> LTL.Bin LTL.Until (LTL.Ground True) (gtlToLTL (unfix p))
    IndexExpr _ _ -> Atom expr
    Automaton buchi -> LTLSimpleAutomaton (simpleAutomaton buchi)
  | otherwise = error "Internal error: Non-bool expression passed to gtlToLTL"
    where
      flattenRel :: Relation -> TypedExpr v -> TypedExpr v -> [TypedExpr v]
      flattenRel rel lhs rhs = case (getValue lhs,getValue rhs) of
        (Value (GTLArrayVal xs),Value (GTLArrayVal ys)) -> zipWith (\x y -> Typed GTLBool (BinRelExpr rel x y)) xs ys
        (Value (GTLArrayVal xs),_) -> zipWith (\x i -> Typed GTLBool (BinRelExpr rel x (Fix $ Typed (getType $ unfix x) (IndexExpr (Fix rhs) i)))) xs [0..]
        (_,Value (GTLArrayVal ys)) -> zipWith (\i y -> Typed GTLBool (BinRelExpr rel (Fix $ Typed (getType $ unfix y) (IndexExpr (Fix lhs) i)) y)) [0..] ys
        (Value (GTLTupleVal xs),Value (GTLTupleVal ys)) -> zipWith (\x y -> Typed GTLBool (BinRelExpr rel x y)) xs ys
        (Value (GTLTupleVal xs),_) -> zipWith (\x i -> Typed GTLBool (BinRelExpr rel x (Fix $ Typed (getType $ unfix x) (IndexExpr (Fix rhs) i)))) xs [0..]
        (_,Value (GTLTupleVal ys)) -> zipWith (\i y -> Typed GTLBool (BinRelExpr rel (Fix $ Typed (getType $ unfix y) (IndexExpr (Fix lhs) i)) y)) [0..] ys
        _ -> [Typed GTLBool (BinRelExpr rel (Fix lhs) (Fix rhs))]

expandExpr :: Ord v => TypedExpr v -> [Set (TypedExpr v)]
expandExpr expr
  | getType expr == GTLBool = case getValue expr of
    Var _ _ -> [Set.singleton expr]
    Value (GTLBoolVal False) -> []
    Value (GTLBoolVal True) -> [Set.empty]
    BinBoolExpr op l r -> case op of
      GTL.And -> [ Set.union lm rm | lm <- expandExpr (unfix l), rm <- expandExpr (unfix r) ]
      GTL.Or -> expandExpr (unfix l) ++ expandExpr (unfix r)
      GTL.Implies -> expandExpr (Typed GTLBool (BinBoolExpr GTL.Or (Fix $ Typed GTLBool (UnBoolExpr GTL.Not l)) r))
      GTL.Until -> error "Can't use until in state formulas yet"
    BinRelExpr _ _ _ -> [Set.singleton expr]
    UnBoolExpr op p -> case op of
      GTL.Not -> let expandNot [] = [Set.empty]
                     expandNot (x:xs) = let res = expandNot xs
                                        in Set.fold (\at cur -> fmap (Set.insert (distributeNot at)) res ++ cur) res x
                 in expandNot (expandExpr $ unfix p)
      GTL.Next -> error "Can't use next in state formulas yet"
      GTL.Always -> error "Can't use always in state formulas yet"
    IndexExpr _ _ -> [Set.singleton expr]
    Automaton _ -> error "Can't use automata in state formulas yet"

simpleAutomaton :: Ord  v => GBuchi Integer (Fix (Typed (Term v))) f -> GBuchi Integer (Set (TypedExpr v)) f
simpleAutomaton buchi
  = let expandState st = [ BuchiState { isStart = isStart st
                                      , vars = nvar
                                      , finalSets = finalSets st
                                      , successors = Set.fromList $ concat [ mapping!succ | succ <- Set.toList (successors st) ]
                                      }
                         | nvar <- expandExpr (unfix $ vars st) ]
        (mapping,_,res) = Map.foldrWithKey (\name co (mp,n,stmp) -> let sts = zip [n..] (expandState co)
                                                                        len = genericLength sts
                                                                    in (Map.insert name (fmap fst sts) mp,
                                                                        n+len,
                                                                        foldl (\stmp' (cn,cco) -> Map.insert cn cco stmp') stmp sts)
                                           ) (Map.empty,0,Map.empty) buchi
    in res



buchiSwitch :: Ord a => GBuchi a b f -> GBuchi a b f
buchiSwitch buchi = Map.foldrWithKey (\name co mp->
                                       foldl (\mp2 succ ->
                                               Map.adjust (\co2 -> co2 { successors = Set.insert name (successors co2) }) succ mp2
                                             ) mp (successors co))
                    (fmap (\co -> co { successors = Set.empty }) buchi) buchi

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Inference(infer,Context) where

import Data.List(nub,delete)
import Data.Set as S(Set(..),empty,singleton,insert,delete,union,fromList,toList)
import Control.Monad.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer
import Unification
import Syntax
import ProofTree

type InferenceState a = StateT UsedTypeVars Maybe a

-- TE standing for Type Expression (type TypeExpr)
-- Meaning that we are considering type expressions (with variables to be used
-- in unification) rather than simple types.
type TEContext a = [TECtxtJudgment a]
type TECtxtJudgment a = (a, TypeExpr)

type TypeJudgment a = (LambdaTerm a, Type)

filterElement :: (a -> Bool) -> [a] -> Maybe a
filterElement f list = let filtered = filter f list
                          in if length filtered > 0
                                then Just $ head filtered
                                else Nothing

varTypeJudgment :: Eq a
                => a                        -- Type of variables
                -> TEContext a              -- Typing context, parameterized
                                            -- by the type of term variables
                -> Maybe (TECtxtJudgment a) -- Judgement that involves
                                            -- that variable, if any
varTypeJudgment x = filterElement ((x ==) . fst)

-- Extract the set of variables that are judged in a context.
varsOfContext :: Ord a => TEContext a -> Set a
varsOfContext c = fromList (varsOfContext' c)
  where varsOfContext' [] = []
        varsOfContext' ((a, t) : rest) = a : (varsOfContext' rest)

-- Pick a fresh variable number
newTypeVar :: InferenceState Int
newTypeVar = do usedTypes <- get
                let newVar = pickFresh usedTypes
                put (newVar:usedTypes)
                return newVar

strongDelete :: Eq a => a -> [a] -> [a]
strongDelete x list = let newList = Data.List.delete x list
                          in if length list == length newList
                             then error "strongDelete failed"
                             else newList

strongInsert :: Eq a => TECtxtJudgment a -> TEContext a -> TEContext a
strongInsert (v,t) ctxt = if length (filter (\(x,_) -> x == v) ctxt) > 0
                          then error "strongInsert failed"
                          else (v,t) : ctxt

-- Compute type equations from term.
-- Returns the set of equations, the type variable associated with the input
-- lambda term, and the context in which the term is typable.
-- The output context is a superset of the input context.
-- Notice that a term is not closed iff the output context is non-empty.
equations :: (Ord a, FreshPickable a)
          => TEContext a
          -> LambdaTerm a
          -> InferenceState (TEContext a, Int, Equations)
          -- -> State UsedTypeVars (TEContext a, Int, Equations)
equations gamma0 (Var x) =
  case varTypeJudgment x gamma0 of
       Just (_, t) -> do newV <- newTypeVar
                         return (gamma0, newV, singleton (TEVar newV, t))
       Nothing     -> do newV <- newTypeVar
                         return (strongInsert (x, TEVar newV) gamma0,
                                 newV, fromList [])
equations gamma0 term@(Abstr v t) = do
  boundVType <- newTypeVar
  let freshVar = (pickFresh . toList) (varsOfContext gamma0)
      (Abstr v' t') = alphaRename freshVar term
  (gamma, typ, eq) <- equations (strongInsert (v', TEVar boundVType) gamma0) t'
  freshT <- newTypeVar
  return (strongDelete (v', TEVar boundVType) gamma,
          freshT,
          insert (TEVar freshT, TEArrow (TEVar boundVType) (TEVar typ)) eq)
equations gamma0 term@(Appl term1 term2) = do
  (gamma1, t1, eq1) <- equations gamma0 term1
  (gamma2, t2, eq2) <- equations gamma0 term2
  freshT <- newTypeVar
  return (uniteUnique gamma1 gamma2,
          freshT,
          insert (TEVar t1, TEArrow (TEVar t2) (TEVar freshT))
            (eq1 `union` eq2 `union` (equateContexts gamma1 gamma2)))

  -- Make union of two contexts, dropping possible duplicates
uniteUnique :: forall a . Eq a => TEContext a -> TEContext a -> TEContext a
uniteUnique ctxt1 ctxt2 = nub $ ctxt1 ++ (map mapper ctxt2)
  where mapper :: TECtxtJudgment a -> TECtxtJudgment a
        mapper (v,t) = case varTypeJudgment v ctxt1 of
                            Just (vv,tt) -> (vv,tt)
                            Nothing -> (v,t)

-- Create equations that equate types of duplicate judgements
equateContexts :: forall a . Eq a => TEContext a -> TEContext a -> Equations
equateContexts [] _ = empty
equateContexts ((x, t):rest) ctxt =
  case varTypeJudgment x ctxt of
    Just (_, t') -> S.insert (t,t') (equateContexts rest ctxt)
    Nothing -> equateContexts rest ctxt

-- Infer the type of a term in a given context.
inferTE :: forall a . (Ord a, FreshPickable a)
      => TEContext a
      -> LambdaTerm a
      -> InferenceState (TEContext a, TypeExpr)
inferTE ctxt term = do (newCtxt, typeVar, eqs) <- equations ctxt term
                       sub <- lift $ unify eqs
                       let inferredType = applySubstitution (TEVar typeVar) sub
                           inferredContext = subsContext sub newCtxt
                       return (inferredContext, inferredType)
  where subsContext :: Substitution -> TEContext a -> TEContext a
        subsContext sub = map subsJudgment
          where subsJudgment (x, t) = (x, applySubstitution t sub)

infer :: (Ord a, FreshPickable a)
      => Context a
      -> LambdaTerm a
      -> Maybe (Context a, Type)
infer ctxt term = do (teC, te) <- runInference (inferTE (contextToTEContext ctxt) term)
                     let maxmax = maxTEConst te
                         newCtxt = teContextToContext (maxmax + 1) teC
                         newType = instantiateTypeVar (maxmax +1) te
                     return (newCtxt, newType)

runInference :: InferenceState (TEContext a, TypeExpr) -> Maybe (TEContext a, TypeExpr)
runInference state = case runStateT state [] of
                          Just ((c,t),_) -> Just (c,t)
                          Nothing -> Nothing

maxTEConst :: TypeExpr -> Int
maxTEConst (TEVar _) = -1
maxTEConst (TEConst x) = x
maxTEConst (TEArrow t1 t2) = max (maxTEConst t1) (maxTEConst t2)

contextToTEContext :: Context a -> TEContext a
contextToTEContext [] = []
contextToTEContext ((x,t):rest) = (x, typeToTypeExpr t) : contextToTEContext rest

teContextToContext :: Int -> TEContext a -> Context a
teContextToContext startInt ctxt = Prelude.map mapper ctxt
  where mapper (x,t) = (x, instantiateTypeVar startInt t)

typeToTypeExpr :: Type -> TypeExpr
typeToTypeExpr (TypeVar x) = TEConst x
typeToTypeExpr (Arrow t1 t2) = TEArrow (typeToTypeExpr t1) (typeToTypeExpr t2)

instantiateTypeVar :: Int -> TypeExpr -> Type
instantiateTypeVar startInt (TEVar x) = TypeVar (startInt + x)
instantiateTypeVar startInt (TEConst x) = TypeVar x
instantiateTypeVar startInt (TEArrow t1 t2) = Arrow (instantiateTypeVar startInt t1)
                                                    (instantiateTypeVar startInt t2)

term = Abstr 0 (Abstr 1 (Appl (Var 0) (Var 1))) :: LambdaTerm Int

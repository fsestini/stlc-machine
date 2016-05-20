{-# LANGUAGE ScopedTypeVariables #-}

module Inference(infer, InferenceState, runInference) where

import Data.Set as S
import Control.Monad.Identity
import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer
import Unification
import Syntax

type InferenceState a = StateT UsedTypeVars Maybe a

type UsedTypeVars = [Int]

-- TE standing for Type Expression (type TypeExpr)
-- Meaning that we are considering type expressions (with variables to be used
-- in unification) rather than simple types.
type TEContext a = Set (TECtxtJudgment a)
type TECtxtJudgment a = (a, TypeExpr)

type TypeJudgment a = (LambdaTerm a, Type)

filterElement :: (a -> Bool) -> Set a -> Maybe a
filterElement f set = let filtered = S.filter f set
                          in if size filtered > 0
                                then Just $ (head . toList) filtered
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
varsOfContext = fromList . varsOfContext' . toList
  where varsOfContext' :: [TECtxtJudgment a] -> [a]
        varsOfContext' [] = []
        varsOfContext' ((a, t) : rest) = a : (varsOfContext' rest)

-- Pick a fresh variable number
newTypeVar :: InferenceState Int
newTypeVar = do usedTypes <- get
                let newVar = (pickFresh . fromList) usedTypes
                put (newVar:usedTypes)
                return newVar

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
                         return (insert (x, TEVar newV) gamma0,
                                 newV, fromList [])
equations gamma0 term@(Abstr v t) = do
  boundVType <- newTypeVar
  let freshVar = pickFresh (varsOfContext gamma0)
      (Abstr v' t') = alphaRename freshVar term
  (gamma, typ, eq) <- equations (insert (v', TEVar boundVType) gamma0) t'
  freshT <- newTypeVar
  return (delete (v', TEVar boundVType) gamma,
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
uniteUnique :: forall a . Ord a => TEContext a -> TEContext a -> TEContext a
uniteUnique ctxt1 ctxt2 = union ctxt1 (S.map mapper ctxt2)
  where mapper :: TECtxtJudgment a -> TECtxtJudgment a
        mapper (v,t) = case varTypeJudgment v ctxt1 of
                            Just (vv,tt) -> (vv,tt)
                            Nothing -> (v,t)

-- Create equations that equate types of duplicate judgements
equateContexts :: forall a . Ord a => TEContext a -> TEContext a -> Equations
equateContexts context1 context2 = equateList (toList context1) (toList context2)
    where equateList :: [TECtxtJudgment a] -> [TECtxtJudgment a] -> Equations
          equateList [] _ = empty
          equateList ((x, t):rest) ctxt =
            case varTypeJudgment x (fromList ctxt) of
                 Just (_, t') -> S.insert (t,t') (equateList rest ctxt)
                 Nothing -> equateList rest ctxt

-- Infer the type of a term in a given context.
infer :: forall a . (Ord a, FreshPickable a)
      => TEContext a
      -> LambdaTerm a
      -> InferenceState (TEContext a, TypeExpr)
infer ctxt term = do (newCtxt, typeVar, eqs) <- equations ctxt term
                     sub <- lift $ unify eqs
                     let inferredType = applySubstitution (TEVar typeVar) sub
                         inferredContext = subsContext sub newCtxt
                     return (inferredContext, inferredType)
  where subsContext :: (Ord a) => Substitution -> TEContext a -> TEContext a
        subsContext sub = S.map subsJudgment
          where subsJudgment (x, t) = (x, applySubstitution t sub)

runInference :: InferenceState (TEContext a, TypeExpr) -> Maybe (TEContext a, TypeExpr)
runInference state = case runStateT state [] of
                          Just ((c,t),_) -> Just (c,t)
                          Nothing -> Nothing

inferClosed :: (FreshPickable a, Ord a) => LambdaTerm a -> Maybe TypeExpr
inferClosed term = case runStateT (infer S.empty term) [] of
                        Just ((_,t),_) -> Just t
                        Nothing -> Nothing

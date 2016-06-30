{-# LANGUAGE ScopedTypeVariables #-}

module Eval (compute) where

import Control.Applicative
import Syntax
import Control.Monad.State
import Control.Monad.Writer

type NameContext a = [a]

data NamelessTerm = NLVar Int
                  | NLAbstr NamelessTerm
                  | NLAppl NamelessTerm NamelessTerm deriving (Eq)

instance Show NamelessTerm where
    show (NLVar n) = show n
    show (NLAbstr t) = "λ." ++ show t
    show (NLAppl t t') = "(" ++ show t ++ ")(" ++ show t' ++ ")"

fromContext :: Eq a => NameContext a -> a -> Int
fromContext [] _ = error "ill name context"
fromContext (x:xs) y = if x == y then 0 else 1 + fromContext xs y

index :: [a] -> Int -> a
index [] _ = error "empty list"
index (x:xs) n = if n == 0 then x else index xs (n-1)

removeNames :: Eq a => NameContext a -> LambdaTerm a -> NamelessTerm
removeNames gamma (Var x) = NLVar (fromContext gamma x)
removeNames gamma (Appl t t') = NLAppl (removeNames gamma t)
                                       (removeNames gamma t')
removeNames gamma (Abstr x t) = NLAbstr (removeNames (x:gamma) t)

restoreNames :: FreshPickable a => NameContext a -> NamelessTerm -> LambdaTerm a
restoreNames gamma (NLVar n) = Var (index gamma n)
restoreNames gamma (NLAppl t t') = Appl (restoreNames gamma t)
                                        (restoreNames gamma t')
restoreNames gamma (NLAbstr t) = Abstr fresh (restoreNames (fresh:gamma) t)
    where fresh = pickFresh gamma

-- Apply a step of beta-reduction according to the leftmost outermost reduction
-- strategy. If a redex is found, the whole contractum is returned, otherwise
-- it returns Nothing.
reduce :: NamelessTerm -> Maybe NamelessTerm
reduce (NLAppl (NLAbstr t) t') = Just betaReduced
    where betaReduced = shift (-1) (substitution t 0 (shift 1 t'))
reduce (NLAbstr t) = do t' <- reduce t
                        return $ NLAbstr t'
reduce (NLAppl t t') = (do newT <- reduce t
                           return $ NLAppl newT t')
                   <|> (do newT' <- reduce t'
                           return $ NLAppl t newT')
reduce _ = Nothing

-- shift nameless term d places, only variables k < c, that is, free variables
shift :: Int -> NamelessTerm -> NamelessTerm
shift d = walk 0
    where walk c (NLVar n) = NLVar (if c <= n then n + d else n)
          walk c (NLAbstr t) = NLAbstr (walk (c+1) t)
          walk c (NLAppl t t') = NLAppl (walk c t) (walk c t')

-- substitution t x t' is t [ x := t' ]
substitution :: NamelessTerm -> Int -> NamelessTerm -> NamelessTerm
substitution (NLVar k) j s | k == j = s
                           | otherwise = NLVar k
substitution (NLAbstr t) j s = NLAbstr (substitution t (j+1) (shift 1 s))
substitution (NLAppl t t') j s = NLAppl (substitution t j s)
                                        (substitution t' j s)

type ReductionMonad a = StateT Int (Writer [NamelessTerm]) a

tick :: ReductionMonad ()
tick = do ticks <- get
          put $ ticks + 1

nlCompute' :: NamelessTerm -> ReductionMonad NamelessTerm
nlCompute' term = tell [term] >> case reduce term of
                       Nothing -> return term
                       Just term' -> tick >> nlCompute' term'

nlCompute :: NamelessTerm -> (NamelessTerm, Int, [NamelessTerm])
nlCompute term = (trm, ticks, reductions)
  where ((trm, ticks), reductions) = runWriter $ runStateT (nlCompute' term) 0

compute :: forall a . (FreshPickable a, Eq a)
        => LambdaTerm a -> (LambdaTerm a, Int, [LambdaTerm a])
compute term = (restoreNames [] trm :: LambdaTerm a, ticks,
                map (restoreNames []) reductions :: [LambdaTerm a])
  where (trm, ticks, reductions) = nlCompute (removeNames [] term)

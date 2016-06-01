{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleInstances, DeriveFunctor #-}

module Syntax(
    Var,
    LambdaTerm(..),
    Type(..),
    alphaRename,
    substitute,
    convert,
    varIntToString,
    FreshPickable(..))
    where

import Data.Maybe
import Data.Char
import Data.Set as S
import Data.List

type Var = String

class FreshPickable a where
  pickFresh :: [a] -> a

instance FreshPickable Int where
  pickFresh = pickFresh' . sort
    where pickFresh' [] = 0
          pickFresh' [n] = n + 1
          pickFresh' (n1:n2:xs) = if n2 - n1 > 1
                                     then n1 + 1
                                     else pickFresh' (n2:xs)

data LambdaTerm a = Var a
                  | Abstr a (LambdaTerm a)
                  | Appl (LambdaTerm a) (LambdaTerm a)
                  deriving(Eq, Functor, Foldable)

instance Show (LambdaTerm Int) where
  show (Var x) = varIntToString x
  show (Abstr x t) = "λ" ++ (varIntToString x) ++ "." ++ (show t)
  show (Appl t t') = "(" ++ (show t) ++ ")(" ++ (show t') ++ ")"

varIntToString :: Int -> String
varIntToString n = varsList 0 !! n
  where vars = ["x", "y", "z", "w"]
        varsList n = (Prelude.map (++ (show n)) vars) ++ (varsList (n+1))

data Type = TypeVar Int
          | Arrow Type Type
          deriving (Eq, Ord)

instance Show Type where
    show (TypeVar v) = [chr (97 + v)]
    show (Arrow t1 t2) =
        case t1 of
             Arrow _ _ -> "(" ++ (show t1) ++ ")" ++ " -> " ++ (show t2)
             _         -> (show t1) ++ " -> " ++ (show t2)

freeVars :: Ord a => LambdaTerm a -> Set a
freeVars (Var a) = singleton a
freeVars (Abstr a t) = S.delete a (freeVars t)
freeVars (Appl t1 t2) = S.union (freeVars t1) (freeVars t2)

-- param1 param2 param3 ==> substitute param2 in param3 for var param1
substitute :: Ord a => a -> LambdaTerm a -> LambdaTerm a -> LambdaTerm a
substitute var subs (Var x) | x == var = subs
                            | otherwise = (Var x)
substitute var subs (Abstr x t) | var == x = (Abstr x t)
                                | not (member x (freeVars subs)) = Abstr x (substitute var subs t)
                                | otherwise = error "illegal variable-capturing substitution"
substitute var subs (Appl t1 t2) = Appl (substitute var subs t1) (substitute var subs t2)

-- Partial function. It only applies to lambda abstractions
-- by alpha-renaming the variable bound by it.
alphaRename :: Ord a => a -> LambdaTerm a -> LambdaTerm a
alphaRename newVar (Abstr v t) = Abstr newVar (substitute v (Var newVar) t)

convert :: LambdaTerm String -> LambdaTerm Int
convert term = fmap (mapper vars) term
  where vars = nub $ Prelude.foldr (:) [] term
        mapper vars x = fromJust $ elemIndex x vars

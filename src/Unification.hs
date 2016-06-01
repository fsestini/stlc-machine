module Unification(
    Equation,
    Equations,
    Substitution,
    TypeExpr(..),
    unify,
    applySubstitution) where

import Data.Set as S
import Control.Monad

data TypeExpr = TEVar Int
              | TEConst Int
              | TEArrow TypeExpr TypeExpr
              deriving(Eq, Show,Ord)

-- equations between type terms
type Equation = (TypeExpr, TypeExpr)

-- system of equations
type Equations = Set Equation

-- A substitution is a set of equations of the form 'variable' = 'type'
type Substitution = Set (Int, TypeExpr)

filterElement :: (a -> Bool) -> Set a -> Maybe a
filterElement f set = let filtered = S.filter f set
                          in if size filtered > 0
                                then Just $ (head . toList) filtered
                                else Nothing

-- Find an equation which has the arrow term constructor in both sides
findArrowEquation :: Equations -> Maybe Equation
findArrowEquation = filterElement arrow
    where arrow (TEArrow _ _, TEArrow _ _) = True
          arrow _ = False

-- STEP 1: Type Reduction
termReduction :: Equations -> Equations
termReduction equations =
    case findArrowEquation equations of
         Just arrow@(TEArrow t1 t2, TEArrow t1' t2') ->
             let newSet = S.union (fromList [(t1, t1'), (t2, t2')])
                                  (S.delete arrow equations)
                 in termReduction newSet
         Nothing -> equations
         _ -> error "unexpected value from findArrowEquation"

-- STEP 2: Check for offending equations
hasOffendingEquations :: Equations -> Bool
hasOffendingEquations = any isOffending
    where isOffending (TEConst _, TEArrow _ _) = True
          isOffending (TEArrow _ _, TEConst _) = True
          isOffending (TEConst c1, TEConst c2) = c1 /= c2
          isOffending _ = False

-- Step 3: Filter out identities
isIdentity :: Equation -> Bool
isIdentity (TEVar v, TEVar v') = v == v'
isIdentity _ = False

filterOut :: (a -> Bool) -> Set a -> Set a
filterOut filtr = S.filter (not . filtr)

filterOutIdentities :: Equations -> Equations
filterOutIdentities = filterOut isIdentity

-- STEP 4: Flip equations with variables on the right and not a variable on the
-- left.
flipEquations :: Equations -> Equations
flipEquations = S.map flipEquation
    where flipEquation (TEConst c, TEVar v) = (TEVar v, TEConst c)
          flipEquation (TEArrow t t', TEVar v) = (TEVar v, TEArrow t t')
          flipEquation e = e

-- STEP 5: Substitute
findSubstitutionCandidate :: Equations -> Maybe Equation
findSubstitutionCandidate equations = filterElement filterer equations
    where filterer equ@(TEVar v, t) = setContainsVar v (S.delete equ equations)
          filterer _ = False

setContainsVar :: Int -> Equations -> Bool
setContainsVar v = any (equationContainsVar v)
    where equationContainsVar :: Int -> Equation -> Bool
          equationContainsVar v (t,t') = (containsVar v t) || (containsVar v t')

containsVar :: Int -> TypeExpr -> Bool
containsVar _ (TEConst _) = False
containsVar v' (TEVar v)  = v == v'
containsVar v (TEArrow t t') = (containsVar v t) || (containsVar v t')

substitute :: Int -> TypeExpr -> TypeExpr -> TypeExpr
substitute _ _ (TEConst c) = TEConst c
substitute v' t (TEVar v) | v == v' = t
                        | otherwise = TEVar v
substitute v t'' (TEArrow t t') = TEArrow (substitute v t'' t)
                                          (substitute v t'' t')

substituteSet :: Equations -> Maybe Equations
substituteSet equations =
    case findSubstitutionCandidate equations of
         Just equ@(TEVar v, t) -> do guard ((not . isCircular) equ)
                                     return $ S.insert equ (S.map (substituteEquation v t)
                                                           (S.delete equ equations))
         Nothing -> Just equations
         _ -> error "unexpected value from findSubstitutionCandidate"
    where substituteEquation :: Int -> TypeExpr -> Equation -> Equation
          substituteEquation v t'' (t,t') = ((substitute v t'' t),
                                             (substitute v t'' t'))
          isCircular :: Equation -> Bool
          isCircular (TEVar v, TEArrow t t') = (containsVar v t) || (containsVar v t')
          isCircular (TEArrow t t', TEVar v) = (containsVar v t) || (containsVar v t')
          isCircular _ = False

-- Five-steps step on the algorithm
--guard :: Bool -> Maybe ()
--guard True = Just ()
--guard False = Nothing

step :: Equations -> Maybe Equations
step equations = do let reduced = termReduction equations
                    guard (not (hasOffendingEquations reduced))
                    let filteredAndFlipped = (flipEquations . filterOutIdentities) reduced
                    substituteSet filteredAndFlipped

-- Applies the unification algorithm to find the most general unifier for a set
-- of equations. If it fails, returns Nothing and no unifier exists.
unify :: Equations -> Maybe Substitution
unify equations = do equations' <- step equations
                     if equations == equations'
                        then return $ equationsToSubstitution equations
                        else unify equations'
  where equationsToSubstitution = S.map converter
          where converter (TEVar v, t) = (v,t)
                converter _ = error "unification algorithm didn't yield a substitution"

applySubstitution :: TypeExpr -> Substitution-> TypeExpr
applySubstitution = S.foldr (uncurry substitute)

eqs = fromList [(TEVar 1,TEVar 0),(TEVar 2,TEArrow (TEVar 0) (TEVar 1)),(TEVar 2,TEArrow (TEConst 0) (TEConst 1))]

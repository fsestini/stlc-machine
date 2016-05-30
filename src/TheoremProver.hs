module TheoremProver(proveProp) where

import Control.Applicative((<|>))
import Control.Monad.Trans.State
import Syntax
import ProofTree
import Data.Set(fromList,toList)

type Proof a = LambdaTerm a
type Goal = Type
type Proposition = Type
type Variable = Int
type UsedVars = UsedTypeVars -- fix this

type ProofState a = StateT UsedVars Maybe a

propsInContext :: Context a -> [Proposition]
propsInContext [] = []
propsInContext ((_,p):rest) = p : propsInContext rest

containsVar :: Context a -> Int -> Bool
containsVar [] _ = False
containsVar ((_, TypeVar x):xs) v = if x == v
                                    then True
                                    else containsVar xs v
containsVar (_:xs) v = containsVar xs v

findTargetInProp :: Proposition -> Proposition -> Maybe Proposition
findTargetInProp wanted hyp@(Arrow _ p2) | wanted == p2 = Just hyp
                                         | otherwise    = findTargetInProp wanted p2
findTargetInProp _ _ = Nothing

findTargetInContext :: Proposition -> Context a -> [(Proposition, Proposition)]
findTargetInContext _ [] = []
findTargetInContext wanted ctxt =
  let mapped = map (findTargetInProp wanted) (propsInContext ctxt)
      filtered = filter filterer mapped
      arrowMapper = \(Just (Arrow x y)) -> (x,y)
  in map arrowMapper filtered
    where filterer :: Maybe Proposition -> Bool
          filterer (Just (Arrow _ _)) = True
          filterer _ = False

-- Tactic 'assumption'
assumption :: Context a -> Goal -> Maybe (LambdaTerm a)
assumption [] _ = Nothing
assumption ((v,p):xs) q = if p == q
                             then Just (Var v)
                             else assumption xs q

-- Tactic 'apply'
apply :: Context a -> Goal -> Maybe (Proof a)
apply ctxt goal = (foldr (<|>) Nothing applies)
  where applies = (do (p1, p2) <- findTargetInContext goal ctxt
                      return $ do f <- prove ctxt (Arrow p1 p2)
                                  a <- prove ctxt p1
                                  return $ Appl f a)

-- Tactic 'intro'
intro :: Context a -> Goal -> Maybe (Proof a)
intro ctxt (Arrow p1 p2) = do p <- prove ((0, p1):ctxt) p2
                              return (Abstr 0 p)
intro _ _ = Nothing

prove :: Context a -> Goal -> Maybe (Proof a)
prove ctxt goal =  assumption ctxt goal
               <|> apply ctxt goal
               <|> intro ctxt goal

newVar :: ProofState TypeVarCode
newVar = do usedVars <- get
            let newVar = pickFresh usedVars
            put (newVar:usedVars)
            return newVar

testT = Arrow (TypeVar 0) (Arrow (TypeVar 1) (TypeVar 2))
taut1 = Arrow (TypeVar 0) (TypeVar 0)
taut2 = Arrow (TypeVar 0) (Arrow (TypeVar 1) (TypeVar 0))

taut3 = (TypeVar 0)
        `Arrow` ((TypeVar 1)
                 `Arrow` (((TypeVar 0)
                           `Arrow` ((TypeVar 1)
                                    `Arrow` (TypeVar 2)))
                          `Arrow` (TypeVar 2)))

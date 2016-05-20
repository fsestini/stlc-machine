module TheoremProver where

import Control.Applicative((<|>))
import Control.Monad.Trans.State
import Syntax
import ProofTree

type Proof = Term
type Goal = Type
type Proposition = Type
type ListContext = [(Variable, Proposition)]
type Term = LambdaTerm Int
type Variable = Int
type UsedVars = UsedTypeVars -- fix this

type ProofState a = StateT UsedVars Maybe a

propsInContext :: ListContext -> [Proposition]
propsInContext [] = []
propsInContext ((_,p):rest) = p : propsInContext rest

containsVar :: ListContext -> Int -> Bool
containsVar [] _ = False
containsVar ((_, TypeVar x):xs) v = if x == v
                                    then True
                                    else containsVar xs v
containsVar (_:xs) v = containsVar xs v

findTargetInProp :: Proposition -> Proposition -> Maybe Proposition
findTargetInProp wanted hyp@(Arrow _ p2) | wanted == p2 = Just hyp
                                         | otherwise    = findTargetInProp wanted p2
findTargetInProp _ _ = Nothing

findTargetInContext :: Proposition -> ListContext -> [(Proposition, Proposition)]
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
assumption :: ListContext -> Goal -> Maybe Term
assumption [] _ = Nothing
assumption ((v,p):xs) q = if p == q
                             then Just (Var v)
                             else assumption xs q

-- Tactic 'apply'
apply :: ListContext -> Goal -> Maybe Proof
apply ctxt goal = (foldr (<|>) Nothing applies)
  where applies = (do (p1, p2) <- findTargetInContext goal ctxt
                      return $ do f <- prove ctxt (Arrow p1 p2)
                                  a <- prove ctxt p1
                                  return $ Appl f a)

-- Tactic 'intro'
intro :: ListContext -> Goal -> Maybe Proof
intro ctxt (Arrow p1 p2) = do p <- prove ((0, p1):ctxt) p2
                              return (Abstr 0 p)
intro _ _ = Nothing

{-

     A,B,A->B->C |- A->B->C       A,B,A->B->C |- A
    ----------------------------------------------
                    A,B,A->B->C |- B -> C                       A,B,A->B->C |- B
                   ---------------------------------------------------------------
                                        A, B, (A -> (B -> C)) |- C
                                       ------------------------------
                                       ------------------------------
                                       A -> B -> (A -> (B -> C)) -> C

-}

prove :: ListContext -> Goal -> Maybe Proof
prove ctxt goal =  assumption ctxt goal
               <|> apply ctxt goal
               <|> intro ctxt goal

newVar :: ProofState TypeVarCode
newVar = do usedVars <- get
            let newVar = findUnusedTypeVar usedVars
            put (newVar:usedVars)
            return newVar

-- prove :: ListContext -> Goal -> Proof
-- prove ctxt goal | findInContext ctxt goal = True
--                 | or applies              = True
--                 | otherwise = case goal of
--                                 (Arrow p1 p2) -> prove (('a', p1):ctxt) p2
--                                 _             -> False
--   where applies = ( do (p1, p2) <- findTargetInContext goal ctxt
--                        let provedP1 = prove ctxt (Arrow p1 p2)
--                            provedP2 = prove ctxt p1
--                        return $ provedP1 && provedP2)

-- intros :: ListContext -> Goal -> (ListContext, Goal)
-- intros ctxt (Arrow p1 p2) = intros (('a', p1):ctxt) p2
-- intros ctxt p = (ctxt, p)

testT = Arrow (TypeVar 0) (Arrow (TypeVar 1) (TypeVar 2))
taut1 = Arrow (TypeVar 0) (TypeVar 0)
taut2 = Arrow (TypeVar 0) (Arrow (TypeVar 1) (TypeVar 0))

taut3 = (TypeVar 0)
        `Arrow` ((TypeVar 1)
                 `Arrow` (((TypeVar 0)
                           `Arrow` ((TypeVar 1)
                                    `Arrow` (TypeVar 2)))
                          `Arrow` (TypeVar 2)))

import Data.Maybe
import Control.Applicative
import Syntax

data NamelessTerm = NLVar Int
                  | NLAbstr NamelessTerm
                  | NLAppl NamelessTerm NamelessTerm deriving (Eq)

instance Show NamelessTerm where
    show (NLVar n) = show n
    show (NLAbstr t) = "λ." ++ (show t)
    show (NLAppl t t') = "(" ++ (show t) ++ ")(" ++ (show t') ++ ")"

type NameContext = [String]

------------------------------------

-- Apply a step of beta-reduction according to the leftmost outermost reduction
-- strategy. If a redex is found, the whole contractum is returned, otherwise
-- returns it Nothing.
reduce :: NamelessTerm -> Maybe NamelessTerm
reduce (NLAppl (NLAbstr t) t') = Just betaReduced
    where betaReduced = (shift (-1) (substitution t 0 (shift 1 t')))
reduce (NLAbstr t) = do t' <- reduce t
                        return $ NLAbstr t'
reduce (NLAppl t t') = (do newT <- reduce t
                           return $ NLAppl newT t') <|>
                       (do newT' <- reduce t'
                           return $ NLAppl t newT')
reduce _ = Nothing

fromContext :: NameContext -> String -> Int
fromContext [] _ = error "ill name context"
fromContext (x:xs) y = if x == y then 0 else 1 + (fromContext xs y)

names = ["x", "y", "z", "w", "a", "b", "c", "d", "e"]

index :: [a] -> Int -> a
index [] _ = error "empty list"
index (x:xs) n = if n == 0 then x else index xs (n-1)

freshName :: NameContext -> String
freshName [] = head names
freshName gamma = let ll = filter (not . ((flip elem) gamma)) names
                      in head ll

removeNames :: NameContext -> LambdaTerm -> NamelessTerm
removeNames gamma (Var x) = NLVar (fromContext gamma x)
removeNames gamma (Appl t t') = NLAppl (removeNames gamma t)
                                       (removeNames gamma t')
removeNames gamma (Abstr x t) = NLAbstr (removeNames (x:gamma) t)

restoreNames gamma (NLVar n) = Var (index gamma n)
restoreNames gamma (NLAppl t t') = Appl (restoreNames gamma t)
                                        (restoreNames gamma t')
restoreNames gamma (NLAbstr t) = Abstr fresh (restoreNames (fresh:gamma) t)
    where fresh = freshName gamma

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

{-
nlCompute :: NamelessTerm -> NamelessTerm
nlCompute term = case reduce term of
                      Nothing -> term
                      Just term' -> nlCompute term'

compute :: Term -> Term
compute term = restoreNames [] (nlCompute (removeNames [] term))
-}

nlCompute :: NamelessTerm -> (NamelessTerm, Int)
nlCompute term = case reduce term of
                      Nothing -> (term, 0)
                      Just term' -> let (ttt, n) = nlCompute term'
                                        in (ttt, n+1)

compute :: LambdaTerm -> (LambdaTerm, Int)
compute term = let (t, n) = nlCompute (removeNames [] term)
               in (restoreNames [] t, n)

----------------------------------------------------------------

true = Abstr "x" (Abstr "y" (Var "x"))
false = Abstr "x" (Abstr "y" (Var "y"))
ifThenElse = Abstr "b" (Abstr "m" (Abstr "n" (Appl (Appl (Var "b") (Var "m")) (Var "n"))))
identity = Abstr "x" (Var "x")

isZero = Abstr "n" (Appl (Var "n") true)

sumF = Abstr "f" (Abstr "x" (Abstr "y"
    (ifThenElse `Appl` (Appl isZero (Var "y"))
                `Appl` (Var "x")
                `Appl` (Appl successor ((Var "f")
                                        `Appl` (Var "x")
                                        `Appl` (predecessor <$$> (Var "y")))))))
lambdaSum = Appl yCombinator sumF

-- fact = Abstr "f" (Abstr "n" (ifThenElse `Appl` (Appl isZero (Var "n")) `Appl` (numeral 1) `Appl` (Appl mult (Appl (Var "f") (Appl sub (Var "n") (numeral 1))))))

pair m n = Abstr "x" (Appl (Appl (Var "x") m) n)
first = Abstr "p" (Appl (Var "p") true)
second = Abstr "p" (Appl (Var "p") false)

numeral :: Int -> LambdaTerm
numeral 0 = identity
numeral n = pair false (numeral (n-1))

successor = Abstr "n" (pair false (Var "n"))
predecessor = Abstr "n" (Appl second (Var "n"))

omega = Abstr "x" (Appl (Var "x") (Var "x"))
bigOmega = Appl omega omega

fomega = Abstr "x" (Appl (Var "f") (Appl (Var "x") (Var "x")))
yCombinator = Abstr "f" (Appl fomega fomega)

(<$$>) = Appl

asdF = Abstr "f" (Abstr "x" (ifThenElse <$$> (isZero <$$> (Var "x"))
                                        <$$> (numeral 0)
                                        <$$> ((Var "f")
                                               <$$> (predecessor
                                                     <$$> (Var "x")))))

asd = yCombinator <$$> asdF

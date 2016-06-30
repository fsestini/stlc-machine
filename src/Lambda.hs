import Data.Maybe
import Control.Applicative
import Syntax
import DeBruijn

------------------------------------

compute :: LambdaTerm String -> (LambdaTerm String, Int)
compute term = let (t, n) = nlCompute (removeNames [] term)
               in (restoreNames [] t, n)

----------------------------------------------------------------

true = Abstr "x" (Abstr "y" (Var "x"))
false = Abstr "x" (Abstr "y" (Var "y"))
ifThenElse = Abstr "b" (Abstr "m" (Abstr "n" (Appl (Appl (Var "b") (Var "m")) (Var "n"))))
identity = Abstr "x" (Var "x")

isZero = Abstr "n" $ (Var "n") `Appl` (Abstr "w" $ Abstr "x" $ Abstr "y" (Var "y"))
                               `Appl` (Abstr "x" $ Abstr "y" (Var "x"))

sumF = Abstr "f" (Abstr "x" (Abstr "y"
    (ifThenElse `Appl` (Appl isZero (Var "y"))
                `Appl` (Var "x")
                `Appl` (Appl successor ((Var "f")
                                        `Appl` (Var "x")
                                        `Appl` (predecessor <$$> (Var "y")))))))
lambdaSum = Appl yCombinator sumF

-- fact = Abstr "f" (Abstr "n" (ifThenElse `Appl` (Appl isZero (Var "n")) `Appl` (numeral 1) `Appl` (Appl mult (Appl (Var "f") (Appl sub (Var "n") (numeral 1))))))

kComb :: LambdaTerm String
kComb = Abstr "x" (Abstr "y" (Var "x"))

-- pair m n = Abstr "x" (Appl (Appl (Var "x") m) n)
-- first = Abstr "p" (Appl (Var "p") true)
-- second = Abstr "p" (Appl (Var "p") false)

numeral :: Int -> LambdaTerm String
numeral 0 = Abstr "y" (Abstr "x" (Var "x"))
numeral n = Abstr "y" (Abstr "x" (Appl (Var "y")
                                 (Appl (Appl (numeral (n-1)) (Var "y")) (Var "x"))))

successor :: LambdaTerm String
successor = Abstr "n" $ Abstr "y" $ Abstr "x" $
            (Var "y") `Appl` ((Var "n") `Appl` (Var "y") `Appl` (Var "x"))

predecessor :: LambdaTerm String
predecessor = Abstr "n" $ Abstr "s" $ Abstr "z" $
              (Var "n") `Appl` (Abstr "p" $ Abstr "q" $
                                 (Var "q") `Appl` (Appl (Var "p") (Var "s")))
                        `Appl` (Abstr "x" (Var "z"))
                        `Appl` (Abstr "x" (Var "x"))

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

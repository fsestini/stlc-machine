{-# LANGUAGE OverloadedStrings #-}

import Data.Maybe
import Data.List
import qualified Data.Set as S
import Parser
import Control.Monad
import Inference
import TypeCheck
import Syntax
import Eval
import TheoremProver
import Control.Monad.Trans.State
import Control.Monad.Trans.Either
import Control.Monad.Trans.Writer
import Control.Monad.Identity
import Control.Monad.Trans
import System.IO

main :: IO ()
main = do putStrLn "Welcome to STLC Machine!"
          mainLoop

mainLoop :: IO ()
mainLoop = do putStr "> "
              hFlush stdout
              command <- getLine
              case parseCommand command of
                Right (Infer s) -> inferCommand s
                Right (Prove s) -> proveCommand s
                Right (Check s) -> checkCommand s
                Right (Eval s)  -> evalCommand s
                _ -> putStrLn "an error occurred"
              mainLoop

inferCommand :: String -> IO ()
inferCommand termString = do result <- runEitherT $ do
                               term <- hoistEither $ fmap convert (parseTerm termString)
                               (ctxt,ttt) <- hoistEither $ inferEither [] term
                               return $ (showContext ctxt)
                                 ++ " ⊢ " ++ (show term)
                                 ++ " : " ++ (show ttt)
                             case result of
                               Left err -> putStrLn ("error: " ++ err)
                               Right val -> putStrLn val

proveCommand :: String -> IO ()
proveCommand typeString = do result <- runEitherT $ do
                               t <- hoistEither $ parseType typeString
                               case fastProve t of
                                 Just proofTerm ->
                                   return (show proofTerm)
                                 Nothing -> hoistEither $
                                   Left "not an intuitionistic tautology"
                             case result of
                               Left err -> putStrLn ("error: " ++ err)
                               Right val -> putStrLn val

checkCommand :: String -> IO ()
checkCommand string = do result <- runEitherT $ do
                           (term, typ) <- hoistEither $ parseTermAndType string
                           return $ typeCheck (convert term) typ
                         case result of
                           Left err -> putStrLn $ "error: " ++ err
                           Right True -> putStrLn "Ok."
                           Right False -> putStrLn "Does not typecheck"

evalCommand :: String -> IO ()
evalCommand string = do result <- runEitherT $ do
                          term <- hoistEither $ fmap convert (parseTerm string)
                          let (nf,steps,_) = compute term
                          return $ "Result: " ++ show nf ++ "\nReduction steps: " ++ show steps
                        case result of
                          Left err -> putStrLn $ "error: " ++ err
                          Right str -> putStrLn str

showContext :: Context Int -> String
showContext [] = ""
showContext [(x,t)] = (varIntToString x) ++ " : " ++ (show t)
showContext ((x,t):xs) = (varIntToString x) ++ " : " ++ (show t) ++ ", " ++ (showContext xs)

inferEither :: (Ord a, FreshPickable a)
            => Context a
            -> LambdaTerm a
            -> Either String (Context a, Type)
inferEither c t = case infer c t of
                       Just (cc,tt) -> Right (cc,tt)
                       Nothing -> Left "cannot unify"

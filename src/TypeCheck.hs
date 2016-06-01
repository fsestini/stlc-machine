module TypeCheck(typeCheck) where

import Data.Set(insert)
import Control.Monad.State
import Control.Applicative
import Unification
import Syntax
import Inference

typeCheck :: (FreshPickable a, Ord a) => LambdaTerm a -> Type -> Bool
typeCheck term typ =
  case (do ((ctxt,v,eqs),_) <- runStateT (equations [] term) []
           guard (length ctxt == 0)
           let eqs' = insert (TEVar v, typeToTypeExpr typ) eqs
           unify eqs') of
    Just _ -> True
    Nothing -> False

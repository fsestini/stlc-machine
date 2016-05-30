module ProofTree(
  UsedTypeVars,
  TypeVarCode,
  UsedTypeVars,
  Context,
  CtxtJudgment
  ) where

import Syntax
import Data.Set
import Data.List

type TypeVarCode = Int
type UsedTypeVars = [TypeVarCode]

type Context a = [CtxtJudgment a]
type CtxtJudgment a = (a, Type)

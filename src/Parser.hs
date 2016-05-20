module Parser(parseTerm, parseTermAndType, parseRaw) where

import Text.Parsec
import Text.Parsec.String
import Syntax
import Data.Char

type Term = LambdaTerm String

regularParse :: Parser a -> String -> Either ParseError a
regularParse p = parse p ""

lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

variable :: Parser String
variable = lexeme $ many1 alphaNum

lambda :: Parser ()
lambda = char 'λ' *> spaces *> return ()

point :: Parser ()
point = char '.' *> spaces *> return ()

parseWithEol :: Parser () -> Parser a -> Parser a
parseWithEol myEol p = spaces >> p <* myEol

eol :: Parser ()
eol = eof

lambdaExpr :: Parser Term
lambdaExpr =  Abstr <$> (lambda *> variable) <*> (point *> lambdaExpr)
          <|> foldl1 Appl <$> (many1 lambdaTerm)

lambdaTerm :: Parser Term
lambdaTerm =  Var <$> variable
          <|> char '(' *> lambdaExpr <* char ')'

parseTerm :: String -> Either ParseError Term
parseTerm = regularParse (parseWithEol eol lambdaExpr)

parseRaw :: String -> Term
parseRaw input = case parseTerm input of
                      Left err   -> error $ show err
                      Right term -> term

termAndType :: Parser (Term, Maybe Type)
termAndType = do term <- lambdaExpr <* spaces
                 ttt  <- typePart
                 return (term, ttt)

typePart :: Parser (Maybe Type)
typePart = (char ':' *> spaces *> (Just <$> typeExpr)) <|> return Nothing

parseTermAndType :: String -> Either ParseError (Term, Maybe Type)
parseTermAndType = regularParse (parseWithEol eol termAndType)

---

anyOf :: String -> Parser Char
anyOf xs = foldl1 (<|>) $ map char xs

typeVar :: Parser Type
typeVar = lexeme $ do c <- anyOf ['a'..'z']
                      let n = (ord c) - 97
                      return $ TypeVar n

arrow :: Parser ()
arrow = lexeme (string "->") *> return ()

typeExpr :: Parser Type
typeExpr = foldr1 Arrow <$> (singleType `sepBy` arrow)

singleType :: Parser Type
singleType = typeInParen <|> typeVar

typeInParen :: Parser Type
typeInParen = lexeme (char '(') *> typeExpr <* lexeme (char ')')

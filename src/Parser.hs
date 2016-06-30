module Parser(
  parseTerm,
  parseTermAndType,
  parseType,
  parseRaw,
  Command(..),
  parseCommand)
where

import Text.Parsec
import Text.Parsec.String
import Syntax
import Data.Char

data Command = Infer String
             | Prove String
             | Check String
             | Eval String
             deriving (Eq, Show)

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

commandParser :: Parser Command
commandParser =  parseCommandAux "infer" Infer
             <|> parseCommandAux "prove" Prove
             <|> parseCommandAux "check" Check
             <|> parseCommandAux "eval" Eval
  where parseCommandAux :: String -> (String -> Command) -> Parser Command
        parseCommandAux text ctor = do string text
                                       spaces
                                       command <- many1 anyChar
                                       return $ ctor command

parseWithEol :: Parser () -> Parser a -> Parser a
parseWithEol myEol p = spaces >> p <* myEol

eol :: Parser ()
eol = eof

lambdaExpr :: Parser (LambdaTerm String)
lambdaExpr =  Abstr <$> (lambda *> variable) <*> (point *> lambdaExpr)
          <|> foldl1 Appl <$> (many1 lambdaTerm)

lambdaTerm :: Parser (LambdaTerm String)
lambdaTerm =  Var <$> variable
          <|> char '(' *> lambdaExpr <* char ')'

parseTerm :: String -> Either String (LambdaTerm String)
parseTerm string = case regularParse (parseWithEol eol lambdaExpr) string of
                        Left parseError -> Left (show parseError)
                        Right x -> Right x

parseCommand :: String -> Either String Command
parseCommand string = case regularParse (parseWithEol eol commandParser) string of
                        Left err -> Left (show err)
                        Right x -> Right x

parseType :: String -> Either String Type
parseType string = case regularParse (parseWithEol eol typeExpr) string of
                     Left parseError -> Left (show parseError)
                     Right x -> Right x

parseRaw :: String -> (LambdaTerm String)
parseRaw input = case parseTerm input of
                      Left err   -> error $ show err
                      Right term -> term

termAndType :: Parser ((LambdaTerm String), Type)
termAndType = do term <- lexeme lambdaExpr
                 lexeme (char ':')
                 typ  <- lexeme typeExpr
                 return (term, typ)

--typePart :: Parser (Maybe Type)
--typePart = (char ':' *> spaces *> (Just <$> typeExpr)) <|> return Nothing

parseTermAndType :: String -> Either String ((LambdaTerm String), Type)
parseTermAndType string = case regularParse (parseWithEol eol termAndType) string of
                            Left err -> Left (show err)
                            Right x -> Right x

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

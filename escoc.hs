import Data.List

data Term
  = Var Int
  | Typ
  | All String Term Term
  | Lam String (Maybe Term) Term
  | App Term Term
  | Ref String

type Context = [(String, (Maybe Term, Maybe Term))]

get_bind :: Context -> Int -> Maybe (String, (Maybe Term, Maybe Term))
get_bind [] i                  = Nothing
get_bind (bind : rest) 0       = Just bind
get_bind (bind : rest) i       = fmap shift_bind (get_bind rest (i - 1)) where
  shift_bind (nam, (ter, typ)) = (nam, (shift_maybe ter, shift_maybe typ))
  shift_maybe Nothing          = Nothing
  shift_maybe term             = term

get_name :: Context -> Int -> Maybe String
get_name ctx i = fmap fst (get_bind ctx i)

get_type :: Context -> Int -> Maybe Term
get_type ctx i = get_bind ctx i >>= (fst . snd)

get_term :: Context -> Int -> Maybe Term
get_term ctx i = get_bind ctx i >>= (snd . snd)

index_of :: Context -> String -> Maybe Int
index_of ctx name = findIndex (\x -> fst x == name) ctx

str :: Term -> Context -> String
str (Var index)                 ctx = maybe "*" id (get_name ctx index)
str Typ                         ctx = "Type"
str (All name bind        body) ctx = "{" ++ name ++ " : " ++ str bind ((name, (Nothing, Nothing)) : ctx) ++ "} " ++ str body ((name, (Nothing, Nothing)) : ctx) 
str (Lam name Nothing     body) ctx = "[" ++ name ++ "] " ++ str body ((name, (Nothing, Nothing)) : ctx) 
str (Lam name (Just bind) body) ctx = "[" ++ name ++ " : " ++ str bind ((name, (Nothing, Nothing)) : ctx) ++ "] " ++ str body ((name, (Nothing, Nothing)) : ctx) 
str (App func argm)             ctx = "(" ++ str func ctx ++ " " ++ str argm ctx ++ ")"
str (Ref name)                  ctx = name

-- TODO port remaining of JS implementation

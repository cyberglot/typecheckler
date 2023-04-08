module SystemF where
-- as per TaPL

data Type = K | Arr Type Type | VarT Int | ForAll Type Type
  deriving Eq

data Term = Var Int
          | Lam Type Term
          | App Term Term
          | LamT Type Term
          | AppT Term Type

type TypeChecker = [Type] -> Maybe Type

typecheck :: Term -> TypeChecker
typecheck (Var i)       = var i
typecheck (Lam ty tm)   = lam ty (typecheck tm)
typecheck (App tm1 tm2) = app (typecheck tm1) (typecheck tm2)
typecheck (LamT ty tm)  = lamT ty (typecheck tm)
typecheck (AppT tm ty)  = appT (typecheck tm) ty

var :: Int -> TypeChecker
var i ctx = Just (ctx !! i)

lam :: Type -> TypeChecker -> TypeChecker
lam ty tc ctx = case tc (ty : ctx) of
                  Just ty' -> Just (Fun ty ty')
                  Nothing  -> Nothing

app :: TypeChecker -> TypeChecker -> TypeChecker
app tc1 tc2 ctx = case (tc1 ctx, tc2 ctx) of
                    (Just (Fun ty1 ty2), Just ty'1) | ty1 == ty'1 -> Just ty2
                    _ -> Nothing

lamT :: Type -> TypeChecker -> TypeChecker
lamT ty tc ctx = case tc (ty : ctx) of
                  Just ty' -> Just (ForAll )
                  Nothing  -> Nothing

failure :: TypeChecker
failure _ = Nothing

have :: Int -> Type -> TypeChecker -> TypeChecker
have i ty tc ctx
  | ctx !! i == ty = tc ctx
  | otherwise      = Nothing

hasType :: Type -> TypeChecker -> TypeChecker
hasType ty tc ctx = case tc ctx of
                      Just ty' | ty == ty' -> Just ty
                      _ -> Nothing

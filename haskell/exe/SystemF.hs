{-# LANGUAGE AllowAmbiguousTypes #-}

module SystemF where
-- as per TaPL

data Type = K | Arr Type Type | VarT Int | ForAll Type Type
  deriving Eq

class Typechecker a where
  var :: Int -> a
  lam :: Type -> a -> a
  app :: a -> a -> a
  lamT :: Int -> a -> a
  appT :: Type -> Type -> Type
  failure :: a
  have :: Int -> Type -> a -> a
  hasType :: Type -> a -> a

data TCTerm v a = Return a
                  | Var v
                  | Lam Type (TCTerm v a)
                  | App (TCTerm v a) (TCTerm v a)
                  | LamT Type (TCTerm v a)
                  | AppT Type Type
                  | Failure
                  | Have Int Type (TCTerm v a)
                  | HasType Type (TCTerm v a)

instance Functor (TCTerm v) where
  fmap :: (a -> b) -> TCTerm v a -> TCTerm v b
  fmap f (Return a)     = Return $ f a
  fmap _ (Var i)        = Var i
  fmap f (Lam ty t)     = Lam ty (fmap f t)
  fmap f (App t1 t2)    = App (fmap f t1) (fmap f t2)
  fmap f (LamT ty t)    = LamT ty (fmap f t)
  fmap f (AppT t ty)    = AppT t ty
  fmap _ Failure        = Failure
  fmap f (Have i ty t)  = Have i ty (fmap f t)
  fmap f (HasType ty t) = HasType ty (fmap f t)

instance Applicative (TCTerm v) where
  pure :: a -> TCTerm v a
  pure = Return

  (<*>) :: TCTerm v (a -> b) -> TCTerm v a -> TCTerm v b
  Return f     <*> a = fmap f a
  Var i        <*> _ = Var i
  Lam ty f     <*> a = Lam ty (f <*> a)
  App t1 t2    <*> a = App (t1 <*> a) (t2 <*> a)
  LamT ty t    <*> a = LamT ty (t <*> a)
  AppT t ty    <*> a = AppT t ty
  Have i ty t  <*> a = Have i ty (t <*> a)
  HasType ty t <*> f = HasType ty (t <*> f)
  Failure      <*> _ = Failure

instance Monad (TCTerm v) where
  (>>=) :: TCTerm v a -> (a -> TCTerm v b) -> TCTerm v b
  Return a     >>= f = f a
  Var i        >>= _ = Var i
  Lam ty t     >>= f = Lam ty (t >>= f)
  App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
  LamT ty t    >>= f = LamT ty (t >>= f)
  AppT t ty    >>= f = AppT t ty
  Have i ty t  >>= f = Have i ty (t >>= f)
  HasType ty t >>= f = HasType ty (t >>= f)
  Failure >>= _ = Failure

assumption :: v -> TCTerm v a
assumption = Var

introduce :: Type -> TCTerm v a
introduce t = let v = undefined in Lam t (Return v) -- `v` has to be introduced somewhere

introduceT :: Type -> TCTerm v a -> TCTerm v a
introduceT = LamT

eval :: Typechecker a => TCTerm Int a -> a
eval (Return t)     = t
eval (Var i)        = var i
eval (Lam a t)      = lam a (eval t)
eval (App t1 t2)    = app (eval t1) (eval t2)
eval (LamT t a)     = lamT (undefined t) (eval a)
eval (AppT t a)     = appT t a
eval (Have i ty t)  = have i ty (eval t)
eval (HasType ty t) = hasType ty (eval t)
eval Failure        = failure

-- Typechecker instance for TCTerm
instance Typechecker (([Type], [Type]) -> Maybe Type) where
  var :: Int -> (([Type], [Type]) -> Maybe Type)
  var i (g, _) = Just $ g !! i

  lam :: Type -> (([Type], [Type]) -> Maybe Type) -> (([Type], [Type]) -> Maybe Type)
  lam ty f (g, d) = \x -> f (x : g, d)

  app :: (([Type], [Type]) -> Maybe Type) -> (([Type], [Type]) -> Maybe Type) -> (([Type], [Type]) -> Maybe Type)
  app f g (g', d) = do
    a <- f (g', d)
    b <- g (g', d)
    case a of
      Arr a' b' -> if a' == b then Just b' else Nothing
      _ -> Nothing

  lamT :: Int -> (([Type], [Type]) -> Maybe Type) -> (([Type], [Type]) -> Maybe Type)
  lamT i f (g, d) = \x -> f (g, x : d)

  appT :: Type -> Type -> Type
  appT (Arr a b) a' = if a == a' then b else K
  appT _ _ = K

  failure :: (([Type], [Type]) -> Maybe Type)
  failure = const Nothing

  have :: Int -> Type -> (([Type], [Type]) -> Maybe Type) -> (([Type], [Type]) -> Maybe Type)
  have i ty f (g, d) = \x -> f (g, d ++ [x !! i])

  hasType :: Type -> (([Type], [Type]) -> Maybe Type) -> (([Type], [Type]) -> Maybe Type)
  hasType ty f (g, d) = \x -> if ty == x then f (g, d) else Nothing

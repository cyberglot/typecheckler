module STLC where

data Type = A | B | C | Fun Type Type
  deriving Eq

class Typechecker a where
  var :: Int -> a
  lam :: Type -> a -> a
  app :: a -> a -> a
  have :: Int -> Type -> a -> a
  hasType :: Type -> a -> a
  failure :: a

data TCTerm v a = Return a
                | Var v
                | Lam Type (TCTerm v a)
                | App (TCTerm v a) (TCTerm v a)
                | Have Int Type (TCTerm v a)
                | HasType Type (TCTerm v a)
                | Failure

instance Functor (TCTerm v) where
  fmap :: (a -> b) -> TCTerm v a -> TCTerm v b
  fmap f (Return a)     = Return $ f a
  fmap _ (Var i)        = Var i
  fmap f (Lam ty t)     = Lam ty (fmap f t)
  fmap f (App t1 t2)    = App (fmap f t1) (fmap f t2)
  fmap f (Have i ty t)  = Have i ty (fmap f t)
  fmap f (HasType ty t) = HasType ty (fmap f t)
  fmap _ Failure        = Failure

instance Applicative (TCTerm v) where
  pure :: a -> TCTerm v a
  pure = Return

  (<*>) :: TCTerm v (a -> b) -> TCTerm v a -> TCTerm v b
  Return f     <*> a = fmap f a
  Var i        <*> _ = Var i
  Lam ty f     <*> a = Lam ty (f <*> a)
  App t1 t2    <*> a = App (t1 <*> a) (t2 <*> a)
  Have i ty t  <*> a = Have i ty (t <*> a)
  HasType ty t <*> f = HasType ty (t <*> f)
  Failure      <*> _ = Failure

instance Monad (TCTerm v) where
  (>>=) :: TCTerm v a -> (a -> TCTerm v b) -> TCTerm v b
  Return a     >>= f = f a
  Var i        >>= _ = Var i
  Lam ty t     >>= f = Lam ty (t >>= f)
  App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
  Have i ty t  >>= f = Have i ty (t >>= f)
  HasType ty t >>= f = HasType ty (t >>= f)
  Failure      >>= _ = Failure

assumption :: v -> TCTerm v a
assumption = Var

introduce :: Type -> TCTerm v a
introduce a = let v = undefined in Lam a (Return v) -- `v` has to be introduced somewhere

eval :: Typechecker a => TCTerm Int a -> a
eval (Return t)    = t
eval (Var i)       = var i
eval (Lam a t)     = lam a (eval t)
eval (App t1 t2)   = app (eval t1) (eval t2)
eval (Have i a t)  = have i a (eval t)
eval (HasType a t) = hasType a (eval t)
eval Failure       = failure

instance Typechecker ([Type] -> Maybe Type) where
  var :: Int -> [Type] -> Maybe Type
  var i types = Just (types !! i) -- I hate this

  lam :: Type -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  lam ty f types = case f (ty : types) of
                        Just ty' -> Just (Fun ty ty')
                        _        -> Nothing

  app :: ([Type] -> Maybe Type) -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  app tm1 tm2 types = case (tm1 types, tm2 types) of
                          (Just (Fun t t'), Just ty) -> if t == ty then Just t' else Nothing
                          _                          -> Nothing

  have :: Int -> Type -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  have i t f types = if types !! i == t then f types else Nothing

  hasType :: Type -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  hasType t f types = case f types of
                        Just ty -> if ty == t then Just ty else Nothing
                        _ -> Nothing

  failure :: [Type] -> Maybe Type
  failure _ = Nothing

type Elab = [Type] -> Maybe (Type, TCTerm [Type] Type)

instance Typechecker Elab where
  var :: Int -> Elab
  var i types =
    let t = types !! i
    in Just (t, Var [t])

  lam :: Type -> Elab -> Elab
  lam ty f types = case f (ty : types) of
                     Just (ty', tm) -> Just (Fun ty ty', Lam ty tm)
                     _              -> Nothing

  app :: Elab -> Elab -> Elab
  app tm1 tm2 types =
    case (tm1 types, tm2 types) of
      (Just (Fun t t', tm'1), Just (ty, tm'2)) -> if t == ty then Just (t', App tm'1 tm'2) else Nothing
      _                                      -> Nothing

  have :: Int -> Type -> Elab -> Elab
  have i t f types =
    if types !! i == t
    then let Just (ty, tm) = f types
         in Just (ty, Have i t tm)
    else Nothing

  hasType :: Type -> Elab -> Elab
  hasType t f types =
    case f types of
      Just (ty, tm) -> if ty == t then Just (ty, HasType ty tm) else Nothing
      _ -> Nothing

  failure :: Elab
  failure _ = Nothing

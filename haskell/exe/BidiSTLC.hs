module BidiSTLC where

import Control.Applicative ((<|>))

data Mode = SYN | CHK
  deriving Eq

data Type = K Mode | Fun Mode Type Type
  deriving Eq

class Typechecker a where
  return :: a
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

instance Typechecker ([Type] -> Maybe Type) where
  return :: [Type] -> Maybe Type
  return _ = Nothing

  var :: Int -> [Type] -> Maybe Type
  var i ctx = if i < length ctx then Just (ctx !! i) else Nothing

  lam :: Type -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  lam a f ctx = case f (a : ctx) of
                  Just b -> Just (Fun SYN a b)
                  Nothing -> Nothing

  app :: ([Type] -> Maybe Type) -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  app tm1 tm2 types = case (tm1 types, tm2 types) of
                          (Just (Fun SYN t t'), Just ty) -> if t == ty then Just t' else Nothing
                          _                          -> Nothing

  have :: Int -> Type -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  have i a t ctx = t ctx <|> Nothing

  hasType :: Type -> ([Type] -> Maybe Type) -> [Type] -> Maybe Type
  hasType a t ctx = case t ctx of
                          Just b -> if a == b then Just a else Nothing
                          Nothing -> Nothing

  failure :: [Type] -> Maybe Type
  failure _ = Nothing

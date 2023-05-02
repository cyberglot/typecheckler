module BidiSTLC where

import GHC.TypeLits
import qualified Data.Kind as Kind

data Type = A | B | C | Fun Type Type
  deriving Eq

data Mode = SYN | CHK

class Typechecker (v :: Nat) (a :: Mode -> Kind.Type)  where
  var :: Nat -> a SYN
  lam :: (Nat -> a CHK) -> a CHK
  app :: a SYN -> a CHK -> a SYN
  switch :: a SYN -> a CHK
  ascribe :: Type -> a CHK -> a SYN
  have :: Nat -> (Type -> a mode) -> a mode
  goalIs :: (Type -> a mode) -> a mode
  failure :: a mode

data TCTerm v a = Return a
                | Var v
                | Lam Type (TCTerm v a)
                | App (TCTerm v a) (TCTerm v a)
                | Have Int Type (TCTerm v a)
                | HasType Type (TCTerm v a)
                | Failure

instance Functor (TCTerm v) where
  fmap f (Return a)     = Return $ f a
  fmap _ (Var i)        = Var i
  fmap f (Lam ty t)     = Lam ty (fmap f t)
  fmap f (App t1 t2)    = App (fmap f t1) (fmap f t2)
  fmap f (Have i ty t)  = Have i ty (fmap f t)
  fmap f (HasType ty t) = HasType ty (fmap f t)
  fmap _ Failure        = Failure

instance Applicative (TCTerm v) where
  pure x = Return x
  Return f     <*> a = fmap f a
  Var i        <*> _ = Var i
  Lam ty f     <*> a = Lam ty (f <*> a)
  App t1 t2    <*> a = App (t1 <*> a) (t2 <*> a)
  Have i ty t  <*> a = Have i ty (t <*> a)
  HasType ty t <*> f = HasType ty (t <*> f)
  Failure      <*> _ = Failure

instance Monad (TCTerm v) where
  Return a     >>= f = f a
  Var i        >>= _ = Var i
  Lam ty t     >>= f = Lam ty (t >>= f)
  App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
  Have i ty t  >>= f = Have i ty (t >>= f)
  HasType ty t >>= f = HasType ty (t >>= f)
  Failure      >>= _ = Failure

assumption :: v -> TCTerm v a
assumption v = Var v

introduce :: Type -> TCTerm v a
introduce a = Lam A (\v -> Return v)

eval :: (Typechecker a) => TCTerm Int a -> a
eval (Return t)    = t
eval (Var i)       = var i
eval (Lam a t)     = lam a (eval t)
eval (App t1 t2)   = app (eval t1) (eval t2)
eval (Have i a t)  = have i a (eval t)
eval (HasType a t) = hasType a (eval t)
eval Failure       = failure

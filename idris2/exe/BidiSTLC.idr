module BidiSTLC

import Data.Nat

data T = A | B | C | (:->) T T

data Mode = SYN | CHK

Modality = Mode -> Type

interface Typechecker (v : Nat) (a : Modality) where
  var     : Nat -> a SYN
  lam     : (Nat -> a CHK) -> a CHK
  app     : a SYN -> a CHK -> a SYN
  switch  : a SYN -> a CHK
  ascribe : Type -> a CHK -> a SYN
  have    : Nat -> (Type -> a mode) -> a mode
  goalIs  : (Type -> a mode) -> a mode
  failure : a mode

data TCTerm v a = Return a
                | Var v
                | Lam Type (TCTerm v a)
                | App (TCTerm v a) (TCTerm v a)
                | Have Int Type (TCTerm v a)
                | HasType Type (TCTerm v a)
                | Failure

Functor (TCTerm v) where
  map f (Return a)     = Return $ f a
  map _ (Var i)        = Var i
  map f (Lam ty t)     = Lam ty (map f t)
  map f (App t1 t2)    = App (map f t1) (map f t2)
  map f (Have i ty t)  = Have i ty (map f t)
  map f (HasType ty t) = HasType ty (map f t)
  map _ Failure        = Failure

Applicative (TCTerm v) where
  pure x             = Return x
  Return f     <*> a = map f a
  Var i        <*> _ = Var i
  Lam ty f     <*> a = Lam ty (f <*> a)
  App t1 t2    <*> a = App (t1 <*> a) (t2 <*> a)
  Have i ty t  <*> a = Have i ty (t <*> a)
  HasType ty t <*> f = HasType ty (t <*> f)
  Failure      <*> _ = Failure

Monad (TCTerm v) where
  Return a     >>= f = f a
  Var i        >>= _ = Var i
  Lam ty t     >>= f = Lam ty (t >>= f)
  App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
  Have i ty t  >>= f = Have i ty (t >>= f)
  HasType ty t >>= f = HasType ty (t >>= f)
  Failure      >>= _ = Failure

assumption : v -> TCTerm v a
assumption v = Var v

introduction : (v -> TCTerm v a) -> TCTerm v a
introduction f = Lam A (f 0)

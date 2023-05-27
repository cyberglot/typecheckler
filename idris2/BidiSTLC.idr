module BidiSTLC

import Data.Nat

data T = A | B | C | (:->) T T

data Mode = SYN | CHK

interface Typechecker (v : Type) (a : Mode -> Type) where
  var     : v -> a SYN
  lam     : (v -> a CHK) -> a CHK
  app     : a SYN -> a CHK -> a SYN
  switch  : a SYN -> a CHK
  ascribe : T -> a CHK -> a SYN
  have    : v -> (Type -> a mode) -> a mode
  goalIs  : (Type -> a mode) -> a mode
  failure : a mode

data TCTerm : (v : Type) -> (a : Mode -> Type) -> Type where
   Var     : v -> TCTerm v (a mode)
   Lam     : T -> TCTerm v (a mode) -> TCTerm v (a mode)
   App     : TCTerm v (a mode) -> TCTerm v (a mode) -> TCTerm v (a mode)
   Switch  : TCTerm v (a mode) -> TCTerm v (a mode)
   Ascribe : T -> TCTerm v (a mode) -> TCTerm v (a mode)
   Have    : v -> T -> TCTerm v (a mode) -> TCTerm v (a mode)
   GoalIs  : T -> TCTerm v (a mode) -> TCTerm v (a mode)
   Failure : TCTerm v (a mode)

-- Functor (TCTerm v) where
--   map _ (Var i)        = Var i
--   map f (Lam ty t)     = Lam ty (map f t)
--   map f (App t1 t2)    = App (map f t1) (map f t2)
--   map f (Have i ty t)  = Have i ty (map f t)
--   map _ Failure        = Failure
--   map f (GoalIs ty t)  = GoalIs ty (map f t)

-- Applicative (TCTerm v) where
--   pure _             = Failure
--   Var i        <*> _ = Var i
--   Lam ty f     <*> a = Lam ty (f <*> a)
--   App t1 t2    <*> a = App (t1 <*> a) (t2 <*> a)
--   Have i ty t  <*> a = Have i ty (t <*> a)
--   Failure      <*> _ = Failure
--   GoalIs ty t  <*> a = GoalIs ty (t <*> a)

-- Monad (TCTerm v) where
--   Var i        >>= _ = Var i
--   Lam ty t     >>= f = Lam ty (t >>= f)
--   App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
--   Have i ty t  >>= f = Have i ty (t >>= f)
--   Failure      >>= _ = Failure
--   GoalIs ty t  >>= f = GoalIs ty (t >>= f)

alpha : Mode -> Type
alpha SYN = List T -> Maybe T
alpha CHK = List T -> T -> Bool

instance Typechecker v (TCTerm v) where
  var    = Var
  lam     = Lam
  app     = App
  switch  = Switch
  ascribe = Ascribe
  have    = Have
  goalIs  = GoalIs
  failure = Failure

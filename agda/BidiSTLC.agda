module BidiSTLC where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)

Nat = ℕ

data Type : Set where
  a : Type
  b : Type
  c : Type
  _:->_ : Type -> Type

data Mode : Set where
  SYN : Mode
  CHK : Mode

record Typechecker (v : Set) (a : Mode -> Set) : Set where
  field
    var     : v -> a SYN
    lam     : (v -> a CHK) -> a CHK
    app     : a SYN -> a CHK -> a SYN
    switch  : a SYN -> a CHK
    ascribe : Type -> a CHK -> a SYN
    have    : {mode : Mode} -> v -> (Type -> a mode) -> a mode -- lookup the type of a variable
    goalIs  : {mode : Mode} -> (Type -> a mode) -> a mode        -- looking up the type of the goal
    failure : {mode : Mode} -> a mode

open Typechecker {{...}}

data TCTerm (v : Set) (a : Mode -> Set) : Set where
   Var     : v -> TCTerm v a
   Lam     : Type -> TCTerm v a -> TCTerm v a
   App     : TCTerm v a -> TCTerm v a -> TCTerm v a
   Switch  : TCTerm v a -> TCTerm v a
   Ascribe : Type -> TCTerm v a -> TCTerm v a
   Have    : v -> Type -> TCTerm v a -> TCTerm v a
   GoalIs  : Type -> TCTerm v a -> TCTerm v a
   Failure : TCTerm v a

_>>=_ : {v : Set} -> {a b : Set} -> TCTerm v a -> (a -> TCTerm v b) -> TCTerm v b
Var i        >>= _ = Var i
Lam ty t     >>= f = Lam ty (t >>= f)
App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
Switch t     >>= f = Switch (t >>= f)
Ascribe ty t >>= f = Ascribe ty (t >>= f)
Have i ty t  >>= f = Have i ty (t >>= f)
GoalIs ty t  >>= f = GoalIs ty (t >>= f)
Failure      >>= _ = Failure

alpha : Mode -> Set
alpha SYN = List Type -> Maybe Type
alpha CHK = List Type -> Type -> Bool

-- typechecker : {a : Mode -> Set} {v : Nat} -> {{Typechecker v a}} -> (delta : Mode) -> TCTerm v (a delta) -> a delta
-- typechecker SYN (Var x) = var x
-- typechecker SYN (Lam x x₁) = {!!}
-- typechecker SYN (App x x₁) = {!!}
-- typechecker SYN (Switch x) = {!!}
-- typechecker SYN (Ascribe x x₁) = {!!}
-- typechecker SYN (Have x x₁ x₂) = {!!}
-- typechecker SYN (GoalIs x x₁) = {!!}
-- typechecker SYN Failure = {!!}
-- typechecker CHK (Var x) = {!!}
-- typechecker CHK (Lam x x₁) = {!!}
-- typechecker CHK (App x x₁) = {!!}
-- typechecker CHK (Switch x) = {!!}
-- typechecker CHK (Ascribe x x₁) = {!!}
-- typechecker CHK (Have x x₁ x₂) = {!!}
-- typechecker CHK (GoalIs x x₁) = {!!}
-- typechecker CHK Failure = {!!}

-- instance
--   handler : {v : Nat} -> Typechecker v alpha
--   Typechecker.var handler = {!!}
--   Typechecker.lam handler = {!!}
--   Typechecker.app handler = {!!}
--   Typechecker.switch handler = {!!}
--   Typechecker.ascribe handler = {!!}
--   Typechecker.have handler = {!!}
--   Typechecker.goalIs handler = {!!}
--   Typechecker.failure handler = {!!}


module STLC where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; ∃)


Nat = ℕ
Sigma = Σ

data Type : Set where
  a : Type
  b : Type
  c : Type
  _:->_ : Type -> Type

record Typechecker {V : Set} (v : V) (a : Set) : Set₁ where
  field
    Bound   : V -> Set
    var     : Bound v -> a
    lam     : Type -> (Set -> a) -> a
    app     : a -> a -> a
    have    : Set -> Type -> a -> a  -- lookup the type of a variable
    goalIs  : Type -> a -> a       -- looking up the type of the goal
    failure : a

open Typechecker {{...}}

data Term (v : Nat) (a : Set) : Set₁ where
   Return  : a -> Term v a
   Var     : Nat -> Term v a
   Lam     : Type -> (Nat -> Term v a) -> Term v a
   App     : Term v a -> Term v a -> Term v a
   Have    : Nat -> Type -> Term v a -> Term v a
   GoalIs  : Type -> Term v a -> Term v a
   Failure : Term v a

_>>=_ : {v : Nat} -> {a b : Set} -> Term v a -> (a -> Term v b) -> Term v b
Return x     >>= f = f x
Var i        >>= _ = Var i
Lam ty tm    >>= f = Lam ty (\v -> tm v >>= f)
App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
Have i ty tm >>= f = Have i ty (tm >>= f)
GoalIs ty tm >>= f = GoalIs ty (tm >>= f)
Failure      >>= _ = Failure

eval : {a : Set} -> {{ tcterm : Typechecker 0 a}} -> Term 0 a -> a
eval (Return x) = {!!}
eval (Var x) = {!Typechecker.var x!}
eval (Lam ty tm) = {!Typechecker.lam ty tm!}
eval (App t1 t2) = {!Typechecker.app t1 t2!}
eval (Have i ty tm) = {!Typechecker.have i ty tm!}
eval (GoalIs ty tm) = {!Typechecker.goalIs ty tm!}
eval Failure = {!Typechecker.failure!}

_!!_ : {a : Set} -> List a -> Nat -> Maybe a
[] !! _      = nothing
(x ∷ _) !! 0 = just x
(_ ∷ xs) !! (suc n) = xs !! n

instance
  typechecker : {V : Set} -> {v : V} -> {a : Set} -> {{tc : Typechecker v a}} -> Typechecker v (List Type -> Maybe Type)
  Typechecker.Bound typechecker = {!!}
  Typechecker.var typechecker = {!!}
  Typechecker.lam typechecker = {!!}
  Typechecker.app typechecker = {!!}
  Typechecker.have typechecker = {!!}
  Typechecker.goalIs typechecker = {!!}
  Typechecker.failure typechecker _ = nothing


Elab = {A : Type} -> (Gamma : List Type) -> Maybe (Sigma A (Term Gamma A))

instance
  elaborator : {V : Set} (v : V) -> {a : Set} -> {{tc : Typechecker v a}} -> Typechecker v ({!!})

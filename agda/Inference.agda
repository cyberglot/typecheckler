module Inference where

open import Data.Nat using (ℕ;suc;_+_)
open import Data.List using (List; []; _∷_; _++_; length)
import Data.Maybe as M
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Product using (Σ; _,_; ∃; _×_; proj₁)
open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level;lzero;lsuc)

Nat = ℕ
Empty = ⊥
Unit = ⊤

data Type (u : Set): Set₁ where
  k : Type u
  _=>_ : Type u -> Type u -> Type u
  mv : u -> Type u

record Typechecker {n : Level} (v : Set) (u : Set) (a : Set n) : Set (lsuc n) where
  field
    var     :  v -> a
    lam     :  Type u -> (v -> a) -> a
    app     :  a -> a -> a
    new     :  (u -> a) -> a
    unify   :  Type u -> Type u -> a -> a
    have    :  (List (v × Type u) -> a) -> a
    hasType :  (Type u -> a) -> a
    failure :  a
    choice  :  a -> a -> a

open Typechecker {{...}}

data Term (v : Set) (u : Set) (a : Set) : Set₁ where
   Return  :  a -> Term v u a
   Var     :  v -> Term v u a
   Lam     :  Type u -> (v -> Term v u a) -> Term v u a
   App     :  Term v u a -> Term v u a -> Term v u a
   New     :  (u -> Term v u a) -> Term v u a
   Unify   :  Type u -> Type u -> Term v u a -> Term v u a
   Have    :  (List (v × Type u) -> Term v u a) -> Term v u a
   HasType :  (Type u -> Term v u a) -> Term v u a
   Failure :  Term v u a
   Choice  :  Term v u a -> Term v u a -> Term v u a

_>>=_ : {v u a b : Set} -> Term v u a -> (a -> Term v u b) -> Term v u b
Return x     >>= f = f x
Var i        >>= _ = Var i
Lam ty tm    >>= f = Lam ty λ { v -> tm v >>= f }
App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
New tm       >>= f = New λ { ty -> tm ty >>= f }
Unify ty ty' tm >>= f = Unify ty ty' (tm >>= f)
Have tm      >>= f = Have λ { ctxt -> tm ctxt >>= f }
HasType tm   >>= f = HasType λ { ty -> tm ty >>= f }
Failure      >>= _ = Failure
Choice t1 t2 >>= f = Choice (t1 >>= f) (t2 >>= f)

infix 19 _!!_
_!!_ : {a : Set} -> List a -> Nat -> Maybe a
[] !! _      = nothing
(x ∷ _) !! 0 = just x
(_ ∷ xs) !! (suc n) = xs !! n

Mv : Set
Mv = {!!}

MetaContext : Set
MetaContext = {!!}

TC : Set₁
TC = MetaContext -> List (Type Mv) -> Type Mv -> Bool

instance
  TCTerm : {v u : Set} -> {a : Set₁} -> {{ Typechecker {lsuc lzero} v u a }} -> Typechecker (Nat -> Nat) Mv TC
  Typechecker.var TCTerm = {!!}
  Typechecker.lam TCTerm = {!!}
  Typechecker.app TCTerm = {!!}
  Typechecker.new TCTerm = {!!}
  Typechecker.unify TCTerm = {!!}
  Typechecker.have TCTerm = {!!}
  Typechecker.hasType TCTerm = {!!}
  Typechecker.failure TCTerm _ _ _ = false
  Typechecker.choice TCTerm = {!!}

Elab : Set₁
Elab = {!!}

instance
  ElabTerm : {!!}
  ElabTerm = {!!}
  -- Typechecker.var ElabTerm = ?
  -- Typechecker.lam ElabTerm = ?
  -- Typechecker.app ElabTerm = ?
  -- Typechecker.new ElabTerm = ?
  -- Typechecker.unify ElabTerm = ?
  -- Typechecker.have ElabTerm = ?
  -- Typechecker.hasType ElabTerm = ?
  -- Typechecker.failure ElabTerm = ?
  -- Typechecker.choice ElabTerm = ?

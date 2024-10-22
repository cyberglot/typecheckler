module STLC where

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

data Type : Set where
  k : Type
  _=>_ : Type -> Type -> Type

_==_ : Type -> Type -> Bool
k == k = true
(a => b) == (a' => b') = a == a' ∧ b == b'
k == _ = false
_ == k = false

record Typechecker {n : Level} {v : Set} (a : Set n) : Set n where
  field
    var     :  v -> a
    lam     :  Type -> (v -> a) -> a
    app     :  a -> a -> a
    have    :  v -> Type -> a -> a
    hasType :  Type -> a -> a
    failure :  a

open Typechecker {{...}}

data Term (v : Set) (a : Set) : Set₁ where
   Return  :  a -> Term v a
   Var     :  v -> Term v a
   Lam     :  Type -> (v -> Term v a) -> Term v a
   App     :  Term v a -> Term v a -> Term v a
   Have    :  v -> Type -> Term v a -> Term v a
   HasType :  Type -> Term v a -> Term v a
   Failure :  Term v a

_>>=_ : {v a b : Set} -> Term v a -> (a -> Term v b) -> Term v b
Return x     >>= f = f x
Var i        >>= _ = Var i
Lam ty tm    >>= f = Lam ty λ { v -> tm v >>= f }
App t1 t2    >>= f = App (t1 >>= f) (t2 >>= f)
Have i ty tm >>= f = Have i ty (tm >>= f)
HasType t tm >>= f = HasType t (tm >>= f)
Failure      >>= _ = Failure

eval : {a v : Set} -> {{ Typechecker a }} -> Term v Empty -> a
eval (Return ())
eval (Var x) = var x
eval (Lam ty tm) = lam ty (λ empty -> eval (tm empty))
eval (App t1 t2) = app (eval t1) (eval t2)
eval (Have i ty tm) = have i ty (eval tm)
eval (HasType ty tm) = hasType ty (eval tm)
eval Failure = failure

infix 19 _!!_
_!!_ : {a : Set} -> List a -> Nat -> Maybe a
[] !! _      = nothing
(x ∷ _) !! 0 = just x
(_ ∷ xs) !! (suc n) = xs !! n

instance
  TCTerm : {a v : Set} -> {{ Typechecker {lzero} {v} a }} -> Typechecker (List Type -> Maybe Type)
  Typechecker.var TCTerm v ctxt = ctxt !! v
  Typechecker.lam TCTerm type f ctxt =
     f (length ctxt + 1) (type ∷ ctxt) M.>>= λ type₁ -> just (type => type₁)
  Typechecker.app TCTerm f x ctxt with f ctxt         | x ctxt
  ...                                | just (t => t₁) | just ty = if t == ty then just t₁ else nothing
  ...                                | _              | _       = nothing
  Typechecker.have TCTerm v type f ctxt = ctxt !! v M.>>= λ type₁ -> if type == type₁ then f ctxt else nothing
  Typechecker.hasType TCTerm type f ctxt = f ctxt M.>>= λ type₁ -> if type == type₁ then just type₁ else nothing
  Typechecker.failure TCTerm _ = nothing

Elab : Set₁
Elab = List Type -> Maybe (Type × Term (List Type) Type)

instance
  ElabTerm : {v : Set} -> {a : Set₁} -> {{ Typechecker {lsuc lzero} {v} a }} -> Typechecker Elab
  Typechecker.var ElabTerm v ctxt = ctxt !! v M.>>= λ type -> just (type , Var ctxt)
  Typechecker.lam ElabTerm type f ctxt =  f (length ctxt + 1) (type ∷ ctxt) M.>>= just
  Typechecker.app ElabTerm f x ctxt with f ctxt                        | x ctxt
  ...                                  | just (xtype => ftype , term)  | just (type , term₁) = if  xtype == type then just (xtype , term₁) else nothing
  ...                                  | _              | _          = nothing
  Typechecker.have ElabTerm v type f ctxt =
    ctxt !! v M.>>= λ type₁ -> if type == type₁ then f ctxt else nothing
  Typechecker.hasType ElabTerm type f ctxt =
    f ctxt M.>>= λ type×term -> if proj₁ type×term == type then just type×term else nothing
  Typechecker.failure ElabTerm _ = nothing

assumption : {v : Set} -> v -> Term v Empty
assumption v = Var v

introduce : {v : Set} -> Type -> Term v Unit
introduce a = Lam a (λ v -> Return _)

goalIs : {v : Set} -> Type -> Term v Unit
goalIs a = HasType a (Return _)

application : {a v : Set} -> Term v a -> Term v a -> Term v a
application f x = App f x

having : {v : Set} -> v -> Type -> Term v Unit
having v a = Have v a (Return _)

fail : {a v : Set} -> Term v a
fail = Failure

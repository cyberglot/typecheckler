module BidiSTLC where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
import Data.Maybe as M
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Product using (Σ; _,_; ∃; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level;lzero;lsuc)

Nat = ℕ
Empty = ⊥
Unit = ⊤

data Type : Set where
  k    :  Type
  _=>_ :  Type -> Type -> Type

data Mode : Set where
  chk :  Mode
  syn :  Mode

_==_ : Type -> Type -> Bool
k == k = true
(a => b) == (a' => b') = a == a' ∧ b == b'
k == _ = false
_ == k = false

record Typechecker {n : Level} {v : Set} (a : Mode -> Set n) : Set n where
  field
    var     :  v -> a syn
    lam     :  Type -> (v -> a chk) -> a chk
    app     :  a syn -> a chk -> a syn
    switch  :  a syn -> a chk
    ascribe :  Type -> a chk -> a syn
    have    :  {mode : Mode} -> v -> (Type -> a mode) -> a mode
    hasType :  (Type -> a chk) -> a chk
    failure :  {mode : Mode} -> a mode

open Typechecker {{...}}

data Term (v : Set) : Mode -> (Mode -> Set) -> Set₁ where
   Return  :  {m : Mode} -> {a : Mode -> Set} -> a m -> Term v m a
   Var     :  {m : Mode} -> {a : Mode -> Set} -> v -> Term v m a
   Lam     :  {m : Mode} -> {a : Mode -> Set} -> Type -> (v -> Term v m a) -> Term v m a
   App     :  {m : Mode} -> {a : Mode -> Set} -> Term v m a -> Term v m a -> Term v m a
   Switch  :  {m : Mode} -> {a : Mode -> Set} -> Term v m a -> Term v m a
   Ascribe :  {m : Mode} -> {a : Mode -> Set} -> Type -> Term v m a -> Term v m a
   Have    :  {m : Mode} -> {a : Mode -> Set} -> v -> Type -> Term v m a -> Term v m a
   HasType :  {m : Mode} -> {a : Mode -> Set} -> Type -> Term v m a -> Term v m a
   Failure :  {m : Mode} -> {a : Mode -> Set} -> Term v m a

TC : Mode -> Set
TC chk = List Type -> Type -> Bool
TC syn = List Type -> Maybe Type

_>>=_ : {v : Set} -> {a b : Mode -> Set} -> {mode : Mode} -> Term v mode a -> (a mode -> Term v mode b) -> Term v mode b
Return x     >>= f  = f x
Var i        >>= _  = Var i
Lam ty tm    >>= f  = Lam ty λ { v -> tm v >>= f }
App t1 t2    >>= f  = App (t1 >>= f) (t2 >>= f)
Switch tm    >>= f  = Switch (tm >>= f)
Ascribe ty tm >>= f = Ascribe ty (tm >>= f)
Have i ty tm >>= f  = Have i ty (tm >>= f)
HasType t tm >>= f  = HasType t (tm >>= f)
Failure      >>= _  = Failure

infix 19 _!!_
_!!_ : {a : Set} -> List a -> Nat -> Maybe a
[] !! _      = nothing
(x ∷ _) !! 0 = just x
(_ ∷ xs) !! (suc n) = xs !! n

_~~>_ : Bool -> Type -> Maybe Type
true  ~~> a = just a
false ~~> _ = nothing

>|_ : Maybe Bool -> Bool
>| just true = true
>| _         = false

instance
  TCTerm :  {v : Set} -> {a : Mode -> Set} -> {{ Typechecker {lzero} {v} a }} -> Typechecker TC
  Typechecker.var TCTerm v ctxt = ctxt !! v
  Typechecker.lam TCTerm xtype check ctxt ftype = check (length ctxt + 1) (xtype ∷ ctxt) ftype
  Typechecker.app TCTerm synth check ctxt with synth ctxt
  ...                                        | just (xtype => ftype) = check (xtype ∷ ctxt) ftype ~~> ftype
  ...                                        | _                     = nothing
  Typechecker.switch TCTerm synth ctxt type with synth ctxt
  ...                                        | just type₁ = type == type₁
  ...                                        | _          = false
  Typechecker.ascribe TCTerm type check ctxt = check ctxt type ~~> type
  Typechecker.have TCTerm {mode} v f with mode
  ...                                   | chk = λ ctxt type ->  >| (ctxt !! v M.>>= λ type₁ -> just (f type ctxt type₁))
  ...                                   | syn = λ ctxt -> ctxt !! v M.>>= λ type -> f type ctxt
  Typechecker.hasType TCTerm type-check ctxt type = type-check type ctxt type
  Typechecker.failure TCTerm {mode} with mode
  ...                                  | chk = λ _ _ -> false
  ...                                  | syn = λ _   -> nothing

Elab : Mode -> Set₁
Elab chk = List Type -> Type -> Maybe (Term (List Type) syn (λ mode -> Type))
Elab syn = List Type -> Maybe (Type × Term (List Type) syn (λ mode -> Type))

instance
  ElabTerm : {v : Set} -> {a : Mode -> Set₁} -> {{ Typechecker {lsuc lzero} {v} a }} -> Typechecker Elab
  Typechecker.var ElabTerm v ctxt = ctxt !! v M.>>= λ type -> just (type , Var ctxt)
  Typechecker.lam ElabTerm xtype check ctxt ftype = check (length ctxt + 1) (xtype ∷ ctxt) ftype
  Typechecker.app ElabTerm synth check ctxt with synth ctxt
  ...                                          | just (xtype => ftype , term) with check (xtype ∷ ctxt) ftype
  ...                                                                            | just term₁ = just (ftype , term₁)
  ...                                                                            | _          = nothing
  Typechecker.app ElabTerm synth check ctxt    | _          = nothing
  Typechecker.switch ElabTerm synth ctxt type with synth ctxt
  ...                                            | just (type₁ , term) = if type == type₁ then just term else nothing
  ...                                            | _          = nothing
  Typechecker.ascribe ElabTerm type check ctxt with check ctxt type
  ...                                        | just t = just ( type , t )
  ...                                        | nothing = nothing
  Typechecker.have ElabTerm {mode} v f with mode
  ...                                   | chk = λ ctxt type ->  ctxt !! v M.>>= λ type₁ -> f type ctxt type₁
  ...                                   | syn = λ ctxt -> ctxt !! v M.>>= λ type -> f type ctxt
  Typechecker.hasType ElabTerm type-check ctxt type = type-check type ctxt type
  Typechecker.failure ElabTerm {mode} with mode
  ...                                  | chk = λ _ _ -> nothing
  ...                                  | syn = λ _   -> nothing

assumption : {v : Set} -> {m : Mode} ->  v -> Term v m (λ _ -> Empty)
assumption v = Var v

introduce : {v : Set} -> {m : Mode} -> Type -> Term v m (λ _ -> Unit)
introduce a = Lam a (λ v -> Return _)

goalIs : {v : Set} -> {m : Mode} -> Type -> Term v m (λ _ -> Unit)
goalIs a = HasType a (Return _)

application : {v : Set} -> {a : Mode -> Set} -> {m : Mode} -> Term v m a -> Term v m a -> Term v m a
application f x = App f x

having : {v : Set} -> {m : Mode} -> v -> Type -> Term v m (λ _ -> Unit)
having v a = Have v a (Return _)

fail : {v : Set} -> {a : Mode -> Set} -> {m : Mode} -> Term v m a
fail = Failure

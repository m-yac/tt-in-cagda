
---------------------------------------------------------
--
-- η-long Normalzation for STLC...
--
---------------------------------------------------------

{-# OPTIONS --cubical #-}
module STLC.NormLongNonTerm where

open import Cubical.Foundations.Prelude renaming (_,_ to <_,_>)
open import Cubical.Foundations.Function
open import Cubical.Foundations.BiInvEquiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sum

open import STLC.Base



data NormType : Set where
  Ne : NormType
  Nf : NormType

data [_]-normal_⊣_ : NormType → Typ → Ctx → Set

neutral_⊣_ normal_⊣_ : Typ → Ctx → Set
neutral_⊣_ = [ Ne ]-normal_⊣_
normal_⊣_  = [ Nf ]-normal_⊣_

data [_]-normal_⊣_ where

  var : (i : τ ∈ Γ) → neutral τ ⊣ Γ
  ap  : (y : neutral (σ ⇒ τ) ⊣ Γ) (z : normal σ ⊣ Γ) → neutral τ ⊣ Γ
  recNat : (z : normal τ ⊣ Γ) (s : normal τ ⊣ (Γ , Nat , τ)) (n : neutral Nat ⊣ Γ) → neutral τ ⊣ Γ

  -- normal terms of type (τ ⇒ σ) are always lambdas
  lam : (x : normal τ ⊣ (Γ , σ)) → normal (σ ⇒ τ) ⊣ Γ

  -- normal terms of type Nat are either:
  -- - zero or suc n if n is a normal term of type Nat
  -- - a neutral term of type Nat
  zero : normal Nat ⊣ Γ
  suc  : (n : normal Nat ⊣ Γ) → normal Nat ⊣ Γ
  
  ne : (n : neutral Nat ⊣ Γ) → normal Nat ⊣ Γ



subWkn : ∀ {t} Δ → [ t ]-normal τ ⊣ (append Γ Δ) → [ t ]-normal τ ⊣ (append (Γ , σ) Δ)
subWkn Δ (var i) = var (go Δ i)
  where go : ∀ Δ (i : τ ∈ (append Γ Δ)) → τ ∈ (append (Γ , σ) Δ)
        go ε i = suc i
        go (Δ , ρ) zero = zero
        go (Δ , ρ) (suc i) = suc (go Δ i)
subWkn Δ (ap y z) = ap (subWkn Δ y) (subWkn Δ z)
subWkn Δ (recNat z s n) = recNat (subWkn Δ z) (subWkn (Δ , _ , _) s) (subWkn Δ n)
subWkn Δ (lam x) = lam (subWkn (Δ , _) x)
subWkn Δ zero = zero
subWkn Δ (suc n) = suc (subWkn Δ n)
subWkn Δ (ne n) = ne (subWkn Δ n)

subWkns : ∀ {t} Δ → [ t ]-normal τ ⊣ Γ → [ t ]-normal τ ⊣ (append Γ Δ)
subWkns ε x = x
subWkns (Δ , σ) x = subWkn ε (subWkns Δ x)

ne' : neutral τ ⊣ Γ → normal τ ⊣ Γ
ne' {σ ⇒ τ} y = lam (ne' {τ} (ap (subWkn ε y) (ne' (var zero))))
ne' {Nat} n = ne n

var' : (i : τ ∈ Γ) → normal τ ⊣ Γ
var' = ne' ∘ var


_~>'_ : Ctx → Ctx → Set
Γ ~>' Δ = ∀ τ (i : τ ∈ Γ) → (neutral τ ⊣ Δ) ⊎ (normal τ ⊣ Δ)

id*' : Γ ~>' Γ
id*' τ i = inl (var i)

_,*'_ : (Γ ~>' Δ) → (x : (neutral τ ⊣ Δ) ⊎ (normal τ ⊣ Δ)) → (Γ , τ) ~>' Δ
(f ,*' x) τ zero = x
(f ,*' x) τ (suc i) = f τ i
infixl 6 _,*'_

↑'_ : (f : Γ ~>' Δ) → (Γ , τ) ~>' (Δ , τ)
↑' f = (λ τ i → map-⊎ (subWkn ε) (subWkn ε) (f τ i)) ,*' inl (var zero)
infixr 3 ↑'_


subResult : NormType → Typ → Ctx → Set
subResult Ne τ Δ = (neutral τ ⊣ Δ) ⊎ (normal τ ⊣ Δ)
subResult Nf τ Δ = normal τ ⊣ Δ

{-# TERMINATING #-}
ap'  : (y : normal (σ ⇒ τ) ⊣ Γ) (z : normal σ ⊣ Γ) → normal τ ⊣ Γ
recNat' : (z : normal τ ⊣ Γ) (s : normal τ ⊣ (Γ , Nat , τ)) (n : normal Nat ⊣ Γ) → normal τ ⊣ Γ
sub' : ∀ {t} → (f : Γ ~>' Δ) → [ t ]-normal τ ⊣ Γ → subResult t τ Δ

ap' (lam x) z = sub' (id*' ,*' inr z) x

recNat' z s zero = z
recNat' z s (suc n) = sub' (id*' ,*' inr n ,*' inr (recNat' z s n)) s
recNat' z s (ne n) = ne' (recNat z s n)

sub' f (var i) = f _ i
sub' f (ap y z) = map-⊎ (λ y' → ap  y' (sub' f z))
                        (λ y' → ap' y' (sub' f z))
                        (sub' f y)
sub' f (recNat z s n) = map-⊎ (recNat  (sub' f z) (sub' (↑' ↑' f) s))
                              (recNat' (sub' f z) (sub' (↑' ↑' f) s))
                              (sub' f n)
sub' f (lam x) = lam (sub' (↑' f) x)
sub' f zero = zero
sub' f (suc n) = suc (sub' f n)
sub' f (ne x) = elim-⊎ (λ x' → ne x') (λ x' → x') (sub' f x)



emb : ∀ {t} → [ t ]-normal τ ⊣ Γ → [ k ] τ ⊣ Γ
emb (var i) = var i
emb (ap y z) = apˡ (emb y) (emb z)
emb (recNat z s n) = recNat (emb z) (emb s) (emb n)
emb (ne x) = emb x
emb (lam x) = lam (emb x)
emb zero = zero
emb (suc n) = suc (emb n)

norm : total τ ⊣ Γ → normal τ ⊣ Γ
norm (sub f x) = sub' (λ τ i → inr (norm (f τ i))) (norm x)
norm (sub-id* x i) = {!!}
norm (sub-∘* g f x i) = {!!}
norm (var i) = var' i
norm (lam x) = lam (norm x)
norm (apˡ y z) = ap' (norm y) (norm z)
norm (lam-βˡ x z i) = {!!}
norm (apʳ y z) = ap' (norm y) (norm z)
norm (lam-ηʳ y i) = {!!}
norm (apʳ-unlamˡ y z i) = {!!}
norm zero = zero
norm (suc x) = suc (norm x)
norm (recNat z s n) = recNat' (norm z) (norm s) (norm n)
norm (recNat-zero z s i) = {!!}
norm (recNat-suc z s n i) = {!!}
norm (sub-var f i j) = {!!}
norm (sub-lam f x i) = {!!}
norm (sub-zero f i) = {!!}
norm (sub-suc f x i) = {!!}
norm (sub-recNat f z s n i) = {!!}


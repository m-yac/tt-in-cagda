
---------------------------------------------------------
--
-- η-long Normalzation for STLC with sized types
--
---------------------------------------------------------

{-# OPTIONS --cubical --safe --sized-types #-}
module STLC.NormLongSized where

open import Agda.Builtin.Size renaming (↑_ to _+1)

open import Cubical.Core.Everything renaming (_,_ to <_,_>)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sum

elim-⊎ : ∀ {ℓp ℓq ℓr} {P : Set ℓp} {Q : Set ℓq} {R : Set ℓr} → (P → R) → (Q → R) → P ⊎ Q → R
elim-⊎ f _ (inl x) = f x
elim-⊎ _ f (inr x) = f x

open import Foundations.BiinvertibleEquiv
open import STLC.Base


data NormType : Set where
  Ne : NormType
  Nf : NormType

data [_]-normal_⊣_<_ : NormType → Type → Ctx → Size → Set

neutral_⊣_<_ normal_⊣_<_ : Type → Ctx → Size → Set
neutral_⊣_<_ = [ Ne ]-normal_⊣_<_
normal_⊣_<_  = [ Nf ]-normal_⊣_<_

data [_]-normal_⊣_<_ where

  var : ∀ {s} (i : τ ∈ Γ) → neutral τ ⊣ Γ < s
  ap  : ∀ {s} (y : neutral (σ ⇒ τ) ⊣ Γ < s) → (∀ {s'} → normal σ ⊣ Γ < s') → neutral τ ⊣ Γ < (s +1)
  recNat : (∀ {s} → normal τ ⊣ Γ < s) → (∀ {s} → normal τ ⊣ (Γ , Nat , τ) < s)
           → ∀ {s} (n : neutral Nat ⊣ Γ < s) → neutral τ ⊣ Γ < s

  -- normal terms of type (τ ⇒ σ) are always lambdas
  lam : ∀ {s} (x : normal τ ⊣ (Γ , σ) < (s +1)) → normal (σ ⇒ τ) ⊣ Γ < s

  -- normal terms of type Nat are either:
  -- - zero or suc n if n is a normal term of type Nat
  -- - a neutral term of type Nat
  zero : ∀ {s} → normal Nat ⊣ Γ < s
  suc  : ∀ {s} {s' : Size< s} → (n : normal Nat ⊣ Γ < s') → normal Nat ⊣ Γ < s
  ne : ∀ {s} (n : neutral Nat ⊣ Γ < s) → normal Nat ⊣ Γ < s


[_]-normal_⊣_ : NormType → Type → Ctx → Set
[_]-normal_⊣_ = [_]-normal_⊣_< ∞

neutral_⊣_ normal_⊣_ : Type → Ctx → Set
neutral_⊣_ = neutral_⊣_< ∞
normal_⊣_  = normal_⊣_< ∞



subWkn : ∀ {s t} Δ → [ t ]-normal τ ⊣ (append Γ Δ) < s → [ t ]-normal τ ⊣ (append (Γ , σ) Δ) < s
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

ne' : ∀ {s} → neutral τ ⊣ Γ < s → normal τ ⊣ Γ < s
ne' {σ ⇒ τ} y = lam (ne' {τ} (ap (subWkn ε y) (ne' (var zero))))
ne' {Nat} n = ne n

var' : ∀ {s} (i : τ ∈ Γ) → normal τ ⊣ Γ < s
var' = ne' ∘ var


_~>'_<_ : Ctx → Ctx → Size → Set
Γ ~>' Δ < s = ∀ τ (i : τ ∈ Γ) → (neutral τ ⊣ Δ < s) ⊎ (normal τ ⊣ Δ < s)

id*' : ∀ {s} → Γ ~>' Γ < s
id*' τ i = inl (var i)

_,*'_ :  ∀ {s} (f : Γ ~>' Δ < s) → (neutral τ ⊣ Δ < s) ⊎ (normal τ ⊣ Δ < s) → (Γ , τ) ~>' Δ < s
(f ,*' x) τ zero = x
(f ,*' x) τ (suc i) = f τ i
infixl 6 _,*'_

↑'_ : ∀ {s} (f : Γ ~>' Δ < s) → (Γ , τ) ~>' (Δ , τ) < s
↑' f = (λ τ i → map-⊎ (subWkn ε) (subWkn ε) (f τ i)) ,*' inl (var zero)
infixr 3 ↑'_

getNormal : (neutral τ ⊣ Γ) ⊎ (normal τ ⊣ Γ) → normal τ ⊣ Γ
getNormal (inl x) = ne' x
getNormal (inr x) = x


subResult : NormType → Type → Ctx → Size → Set
subResult Ne τ Δ s = (neutral τ ⊣ Δ < s) ⊎ (normal τ ⊣ Δ < s)
subResult Nf τ Δ s = normal τ ⊣ Δ < s

ap'  : ∀ {s} (y : normal (σ ⇒ τ) ⊣ Γ < s) → (∀ {s'} → normal σ ⊣ Γ < s') → normal τ ⊣ Γ < (s +1)
recNat' : (∀ {s} → normal τ ⊣ Γ < s) → (∀ {s} → normal τ ⊣ (Γ , Nat , τ) < s)
          → ∀ {s} (n : normal Nat ⊣ Γ < s) → normal τ ⊣ Γ < s
sub' : ∀ {s} {s' : Size< s} {t} (f : Γ ~>' Δ < s') → [ t ]-normal τ ⊣ Γ < s → subResult t τ Δ s

ap' (lam x) z = sub' (id*' ,*' inr z) x

recNat' z s zero = z
recNat' z s (suc n) = sub' (id*' ,*' inr n ,*' inr (recNat' z s n)) s
recNat' z s (ne n) = ne' (recNat z s n)

sub' f (var i) = {!!} -- f _ i
sub' f (ap y x) = {!!}
sub' f (recNat x x₁ n) = {!!}
sub' f (lam x) = {!!}
sub' f zero = {!!}
sub' f (suc n) = {!!}
sub' f (ne n) = {!!}

-- sub' f (var i) = f _ i
-- sub' f (ap y z) = map-⊎ (λ y' → ap  y' (sub' f z))
--                         {!!} -- (λ y' → ap' y' (sub' f z))
--                         (sub' f y)
-- sub' f (recNat z s n) = {!!} -- map-⊎ (recNat  (sub' f z) (sub' (↑' ↑' f) s))
--                           --     {!!} -- (recNat' (sub' f z) (sub' (↑' ↑' f) s))
--                           --     (sub' f n)
-- sub' f (lam x) = lam (sub' (↑' f) x)
-- sub' f zero = zero
-- sub' f (suc n) = suc (sub' f n)
-- sub' f (ne x) = elim-⊎ (λ x' → ne' x') (λ x' → x') (sub' f x)

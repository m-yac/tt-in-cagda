
---------------------------------------------------------
--
-- η-long Normalzation for STLC...
--
---------------------------------------------------------

{-# OPTIONS --cubical #-}
module STLC+N.NormLong where

open import Cubical.Foundations.Prelude renaming (_,_ to <_,_>)
open import Cubical.Foundations.Function
open import Cubical.Foundations.BiInvEquiv
open import Cubical.Foundations.Isomorphism

open import STLC+N.Base



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



data _~>⊥_ : Ctx → Ctx → Set where
  ε : ε ~>⊥ ε
  drop : Γ ~>⊥ Δ →  Γ      ~>⊥ (Δ , τ)
  keep : Γ ~>⊥ Δ → (Γ , τ) ~>⊥ (Δ , τ)

id*⊥ : Γ ~>⊥ Γ
id*⊥ {ε} = ε
id*⊥ {Γ , τ} = keep (id*⊥ {Γ})

_∘*⊥_ : Δ ~>⊥ Ε → Γ ~>⊥ Δ → Γ ~>⊥ Ε
ε      ∘*⊥ f      = f
drop g ∘*⊥ f      = drop (g ∘*⊥ f)
keep g ∘*⊥ drop f = drop (g ∘*⊥ f)
keep g ∘*⊥ keep f = keep (g ∘*⊥ f)

sub⊥-∈ : (Γ ~>⊥ Δ) → τ ∈ Γ → τ ∈ Δ
sub⊥-∈ ε x = x
sub⊥-∈ (drop f) x = suc (sub⊥-∈ f x)
sub⊥-∈ (keep f) zero = zero
sub⊥-∈ (keep f) (suc x) = suc (sub⊥-∈ f x)

sub⊥ : ∀ {t} → (Γ ~>⊥ Δ) → [ t ]-normal τ ⊣ Γ → [ t ]-normal τ ⊣ Δ
sub⊥ f (var i) = var (sub⊥-∈ f i)
sub⊥ f (ap y z) = ap (sub⊥ f y) (sub⊥ f z)
sub⊥ f (recNat z s n) = recNat (sub⊥ f z) (sub⊥ (keep (keep f)) s) (sub⊥ f n)
sub⊥ f (lam x) = lam (sub⊥ (keep f) x)
sub⊥ f zero = zero
sub⊥ f (suc n) = suc (sub⊥ f n)
sub⊥ f (ne n) = ne (sub⊥ f n)

sub⊥-∈-id*⊥ : ∀ (i : τ ∈ Γ) → sub⊥-∈ id*⊥ i ≡ i
sub⊥-∈-id*⊥ zero j = zero
sub⊥-∈-id*⊥ (suc i) j = suc (sub⊥-∈-id*⊥ i j)

sub⊥-id*⊥ : ∀ {t} (x : [ t ]-normal τ ⊣ Γ) → sub⊥ id*⊥ x ≡ x
sub⊥-id*⊥ (var i) j = var (sub⊥-∈-id*⊥ i j)
sub⊥-id*⊥ (ap y z) i = ap (sub⊥-id*⊥ y i) (sub⊥-id*⊥ z i)
sub⊥-id*⊥ (recNat z s n) i = recNat (sub⊥-id*⊥ z i) (sub⊥-id*⊥ s i) (sub⊥-id*⊥ n i)
sub⊥-id*⊥ (lam x) i = lam (sub⊥-id*⊥ x i)
sub⊥-id*⊥ zero i = zero
sub⊥-id*⊥ (suc n) i = suc (sub⊥-id*⊥ n i)
sub⊥-id*⊥ (ne n) i = ne (sub⊥-id*⊥ n i)



_⟦⊣⟧_ : Typ → Ctx → Set
(σ ⇒ τ) ⟦⊣⟧ Γ = ∀ {Δ} → Γ ~>⊥ Δ → σ ⟦⊣⟧ Δ → τ ⟦⊣⟧ Δ
Nat ⟦⊣⟧ Γ = normal Nat ⊣ Γ

⟦sub⊥⟧ : (Γ ~>⊥ Δ) → τ ⟦⊣⟧ Γ → τ ⟦⊣⟧ Δ
⟦sub⊥⟧ {τ = σ ⇒ τ} f x = λ g → x (g ∘*⊥ f)
⟦sub⊥⟧ {τ = Nat} f x = sub⊥ f x

_⟦~>⟧_ : Ctx → Ctx → Set
Γ ⟦~>⟧ Δ = ∀ τ (i : τ ∈ Γ) → τ ⟦⊣⟧ Δ

_⟦,*⟧_ : Γ ⟦~>⟧ Δ → (x : τ ⟦⊣⟧ Δ) → (Γ , τ) ⟦~>⟧ Δ
(f ⟦,*⟧ x) τ zero = x
(f ⟦,*⟧ x) τ (suc i) = f τ i
infixl 6 _⟦,*⟧_

_⟦∘*⊥⟧_ : (Δ ~>⊥ Ε) → Γ ⟦~>⟧ Δ → Γ ⟦~>⟧ Ε
f ⟦∘*⊥⟧ e = λ τ i → ⟦sub⊥⟧ f (e τ i)



reflect : neutral τ ⊣ Γ → τ ⟦⊣⟧ Γ
reify : τ ⟦⊣⟧ Γ → normal τ ⊣ Γ

reflect {σ ⇒ τ} x = λ f u → reflect (ap (sub⊥ f x) (reify u))
reflect {Nat} x = ne x

reify {σ ⇒ τ} x = lam (reify (x (drop id*⊥) (reflect (var zero))))
reify {Nat} x = x


⟦id*⟧ : Γ ⟦~>⟧ Γ
⟦id*⟧ = λ τ i → reflect (var i)

⟦↑⟧_ : (Γ ⟦~>⟧ Δ) → (Γ , τ) ⟦~>⟧ (Δ , τ)
⟦↑⟧ f = (drop id*⊥ ⟦∘*⊥⟧ f) ⟦,*⟧ reflect (var zero)
infixr 3 ⟦↑⟧_


⟦_⟧  : (x : τ ⊣ Γ) → ∀ {Δ} (e : Γ ⟦~>⟧ Δ) → τ ⟦⊣⟧ Δ
⟦_⟧* : (f : Γ ~> Ε) → ∀ {Δ} (e : Ε ⟦~>⟧ Δ) → Γ ⟦~>⟧ Δ

⟦recNat⟧ : (∀ {Δ} (e : Γ ⟦~>⟧ Δ) → τ ⟦⊣⟧ Δ) → (∀ {Δ} (e : (Γ , Nat , τ) ⟦~>⟧ Δ) → τ ⟦⊣⟧ Δ) → Nat ⟦⊣⟧ Δ → (Γ ⟦~>⟧ Δ) → τ ⟦⊣⟧ Δ
⟦recNat⟧ ⟦z⟧ ⟦s⟧ zero    e = ⟦z⟧ e
⟦recNat⟧ ⟦z⟧ ⟦s⟧ (suc n) e = ⟦s⟧ (e ⟦,*⟧ n ⟦,*⟧ ⟦recNat⟧ ⟦z⟧ ⟦s⟧ n e)
⟦recNat⟧ ⟦z⟧ ⟦s⟧ (ne n)  e = reflect (recNat (reify (⟦z⟧ e)) (reify (⟦s⟧ (⟦↑⟧ ⟦↑⟧ e))) n)

  -- ⟦ y ⟧ ((λ τ i → ⟦sub⊥⟧ id*⊥ (e τ i)) ⟦,*⟧ ⟦ z ⟧ e)
  --   = ?0 (y = x) (z = x₁) (i = i0) (e = e)
  --   : τ₁ ⟦⊣⟧ Δ
  -- ⟦ y ⟧ (⟦ ⟨ z ⟩ ⟧* e) = ?0 (y = x) (z = x₁) (i = i1) (e = e)
  --   : τ₁ ⟦⊣⟧ Δ

-- ⟦ y ⟧ ((λ τ₁ i₁ → ⟦sub⊥⟧ id*⊥ (e τ₁ i₁)) ⟦,*⟧ ⟦ z ⟧ e)
-- ⟦ y ⟧ (λ τ₁ i₁ → ⟦ ((λ τ₂ i₂ → var i₂) ,* z) τ₁ i₁ ⟧ e)

⟦ sub f x ⟧ e = ⟦ x ⟧ (⟦ f ⟧* e)
⟦ sub-id* x i ⟧ e = ⟦ x ⟧ e
⟦ sub-∘* g f x i ⟧ e = ⟦ x ⟧ (⟦ f ⟧* (⟦ g ⟧* e))
⟦ var i ⟧ e = e _ i
⟦ lam x ⟧ e = λ f u → ⟦ x ⟧ ((f ⟦∘*⊥⟧ e) ⟦,*⟧ u)
⟦ apˡ y z ⟧ e = ⟦ y ⟧ e id*⊥ (⟦ z ⟧ e)
⟦ lam-βˡ y z i ⟧ e = {!!}
⟦ apʳ y z ⟧ e =  ⟦ y ⟧ e id*⊥ (⟦ z ⟧ e)
⟦ lam-ηʳ x i ⟧ e = {!!}
⟦ apʳ-unlamˡ x x₁ i ⟧ e = {!!}
⟦ zero ⟧ e = zero
⟦ suc x ⟧ e = suc (⟦ x ⟧ e)
⟦ recNat z s n ⟧ e = ⟦recNat⟧ ⟦ z ⟧ ⟦ s ⟧ (⟦ n ⟧ e) e
⟦ recNat-zero z s i ⟧ e = ⟦ z ⟧ e
⟦ recNat-suc z s n i ⟧ e = {!!}
⟦ sub-var f i j ⟧ e = ⟦ f _ i ⟧ e
⟦ sub-lam f x i ⟧ e = {!!}
⟦ sub-zero f i ⟧ e = zero
⟦ sub-suc f n i ⟧ e = suc (⟦ n ⟧ (⟦ f ⟧* e))
⟦ sub-recNat f z s n i ⟧ e = {!!}

⟦ f ⟧* e = λ τ i → ⟦ f τ i ⟧ e


norm : τ ⊣ Γ → normal τ ⊣ Γ
norm x = reify (⟦ x ⟧ ⟦id*⟧)

emb : ∀ {t} → [ t ]-normal τ ⊣ Γ → τ ⊣ Γ
emb (var i) = var i
emb (ap y z) = apˡ (emb y) (emb z)
emb (recNat z s n) = recNat (emb z) (emb s) (emb n)
emb (ne x) = emb x
emb (lam x) = lam (emb x)
emb zero = zero
emb (suc n) = suc (emb n)


-- -- stable : ∀ (x : normal τ ⊣ Γ) → norm (emb x) ≡ x
-- -- stableNe : ∀ (x : neutral τ ⊣ Γ) → ⟦ emb x ⟧ id*ᴺ ≡ reflect x

-- -- stable (lam x) = {!!}
-- -- stable zero = refl
-- -- stable (suc n) = cong suc (stable n)
-- -- stable (ne n) = stableNe n

-- -- stableNe (var i) = refl
-- -- stableNe (ap y z) =
-- --    ⟦ emb y ⟧ id*ᴺ id*⊥ (⟦ emb z ⟧ id*ᴺ)                  ≡⟨ cong (λ x → x id*⊥ (⟦ emb z ⟧ id*ᴺ)) (stableNe y) ⟩
-- --    (reflect y) id*⊥ (⟦ emb z ⟧ id*ᴺ)                    ≡⟨⟩
-- --    reflect (ap (sub⊥ id*⊥ y) (reify (⟦ emb z ⟧ id*ᴺ)))  ≡⟨ cong (reflect ∘ ap (sub⊥ id*⊥ y)) (stable z) ⟩
-- --    reflect (ap (sub⊥ id*⊥ y) z)                         ≡⟨ cong (λ x → reflect (ap x z)) (sub⊥-id*⊥ y) ⟩
-- --    reflect (ap y z)                                     ∎
-- -- stableNe (recNat z s n) = {!!}


-- -- complete : ∀ (x : total τ ⊣ Γ) → emb (norm x) ≡ x
-- -- complete x = {!!}








-- -- subWkn : ∀ {t} Δ → [ t ]-normal τ ⊣ (append Γ Δ) → [ t ]-normal τ ⊣ (append (Γ , σ) Δ)
-- -- subWkn Δ (var i) = var (go Δ i)
-- --   where go : ∀ Δ (i : τ ∈ (append Γ Δ)) → τ ∈ (append (Γ , σ) Δ)
-- --         go ε i = suc i
-- --         go (Δ , ρ) zero = zero
-- --         go (Δ , ρ) (suc i) = suc (go Δ i)
-- -- subWkn Δ (ap y z) = ap (subWkn Δ y) (subWkn Δ z)
-- -- subWkn Δ (recNat z s n) = recNat (subWkn Δ z) (subWkn (Δ , _ , _) s) (subWkn Δ n)
-- -- subWkn Δ (lam x) = lam (subWkn (Δ , _) x)
-- -- subWkn Δ zero = zero
-- -- subWkn Δ (suc n) = suc (subWkn Δ n)
-- -- subWkn Δ (ne n) = ne (subWkn Δ n)

-- -- subWkns : ∀ {t} Δ → [ t ]-normal τ ⊣ Γ → [ t ]-normal τ ⊣ (append Γ Δ)
-- -- subWkns ε x = x
-- -- subWkns (Δ , σ) x = subWkn ε (subWkns Δ x)



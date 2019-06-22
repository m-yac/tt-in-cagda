
---------------------------------------------------------
--
-- Normalization and evaluation for STLC, along with...
--
---------------------------------------------------------

{-# OPTIONS --cubical --safe #-}
module STLC.Norm where

open import Cubical.Foundations.Prelude renaming (_,_ to <_,_>)
open import Cubical.Foundations.Function
open import Cubical.Foundations.BiInvEquiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty
open import Cubical.Data.Bool hiding (_or_)

_or_ : Bool → Bool → Bool
true  or _ = true
false or b = b
infixl 10 _or_

isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥

isFalse : Bool → Set
isFalse true = ⊥
isFalse false = ⊤

open import STLC.Base



----------------
-- Definitions
----------------

-- We will mutually inductively define:

-- The type of judements x : normal τ ⊣ Γ ("x of type τ in context Γ is in normal form")
data normal_⊣_ : Typ → Ctx → Set

-- A few predicates as to when β/η/recNat reductions cannot be applied
lam-β-irred : (normal (σ ⇒ τ) ⊣ Γ) → Set
lam-η-irred : (normal τ ⊣ Γ) → Set
recNat-β-irred : (normal Nat ⊣ Γ) → Set
_freeIn_ : (i : σ ∈ Γ) (x : normal τ ⊣ Γ) → Bool


data normal_⊣_ where

  -- (var i) is in normal form
  var : (i : τ ∈ Γ) → normal τ ⊣ Γ

  -- (lam x) is in normal form only if x ≢ unlam y for some y (i.e. lam-η cannot be applied)
  lam : (x : normal τ ⊣ (Γ , σ)) (pf : lam-η-irred x) → normal (σ ⇒ τ) ⊣ Γ

  -- (ap y z) is in normal form only if y ≢ lam x for some x (i.e. lam-β cannot be applied)
  ap  : (y : normal (σ ⇒ τ) ⊣ Γ) (z : normal σ ⊣ Γ) (pf : lam-β-irred y) → normal τ ⊣ Γ

  zero : normal Nat ⊣ Γ
  suc  : (n : normal Nat ⊣ Γ) → normal Nat ⊣ Γ

  -- (recNat τ z s n) is in normal form only if n ≢ zero (i.e. recNat-zero cannot be applied)
  --                                        and n ≢ suc n (i.e. recNat-suc cannot be applied)
  recNat : (z : normal τ ⊣ Γ) (s : normal τ ⊣ (Γ , Nat , τ)) (n : normal Nat ⊣ Γ)
           (pf : recNat-β-irred n) → normal τ ⊣ Γ


-- uninhabited iff y ≡ lam x for some x
lam-β-irred (lam x _) = ⊥
lam-β-irred _ = ⊤

-- uninhabited iff x ≡ unlam y (≡ ap (sub wkn y) (var zero)) for some y
lam-η-irred (ap y (var zero) _) = isTrue (zero freeIn y)
lam-η-irred _ = ⊤

-- uninhabited iff n ≡ zero or n ≡ suc n' for some n'
recNat-β-irred zero = ⊥
recNat-β-irred (suc _) = ⊥
recNat-β-irred _ = ⊤

-- inhabited iff (var i) appears somewhere in x
zero freeIn (var zero) = true
zero freeIn (var (suc _)) = false
(suc _) freeIn (var zero) = false
(suc i) freeIn (var (suc j)) = i freeIn (var j)
i freeIn (lam x _) = (suc i) freeIn x
i freeIn (ap y z _) = i freeIn y or i freeIn z
i freeIn zero = false
i freeIn (suc n) = i freeIn n
i freeIn (recNat z s n _) = i freeIn z or (suc (suc i)) freeIn s or i freeIn n



-----------
-- Values
-----------

-- every y : normal (σ ⇒ τ) ⊣ ε satisfies y ≡ lam x pf for some < x , pf >
⇒-val : (y : normal (σ ⇒ τ) ⊣ ε) → Σ (Σ (normal τ ⊣ (ε , σ)) lam-η-irred) (λ p → y ≡ lam (fst p) (snd p))

-- every n : Nat ⊣ ε satisfies either n ≡ zero or n ≡ suc m for some m
Nat-val : (n : normal Nat ⊣ ε) → (n ≡ zero) ⊎ Σ (normal Nat ⊣ ε) (λ m → n ≡ suc m)

⇒-val (var ())
⇒-val (lam x pf) = < < x , pf > , refl >
⇒-val (ap y z pf) = ⊥-elim (subst lam-β-irred (snd (⇒-val y)) pf)
⇒-val (recNat z s n pf)
  = ⊥-elim (elim-⊎ (λ p → subst recNat-β-irred p pf)
                   (λ p → subst recNat-β-irred (snd p) pf) (Nat-val n))

Nat-val (var ())
Nat-val (ap y z pf) = ⊥-elim (subst lam-β-irred (snd (⇒-val y)) pf)
Nat-val zero = inl refl
Nat-val (suc n) = inr < n , refl >
Nat-val (recNat z s n pf)
  = ⊥-elim (elim-⊎ (λ p → subst recNat-β-irred p pf)
                   (λ p → subst recNat-β-irred (snd p) pf) (Nat-val n))

-- lam defines an equivalence:
⇒-val≡ : (normal (σ ⇒ τ) ⊣ ε) ≡ (Σ (normal τ ⊣ (ε , σ)) lam-η-irred)
⇒-val≡ = isoToPath ⇒-valIso
  where ⇒-valIso : Iso (normal (σ ⇒ τ) ⊣ ε) (Σ (normal τ ⊣ (ε , σ)) lam-η-irred)
        Iso.fun ⇒-valIso x = fst (⇒-val x)
        Iso.inv ⇒-valIso p = lam (fst p) (snd p)
        Iso.rightInv ⇒-valIso p = refl
        Iso.leftInv ⇒-valIso x = sym (snd (⇒-val x))

-- by the universal property of ℕ, we also have an equivalence:
-- ...



------------------
-- Normalization
------------------

inj : normal τ ⊣ Γ → [ k ] τ ⊣ Γ
inj (var i) = var i
inj (lam x _) = lam (inj x)
inj (ap y x _) = apˡ (inj y) (inj x)
inj zero = zero
inj (suc n) = suc (inj n)
inj (recNat z s n _) = recNat (inj z) (inj s) (inj n)


norm : total τ ⊣ Γ → normal τ ⊣ Γ
norm x = {!!}


lamNorm : (x : normal τ ⊣ (Γ , σ)) → normal (σ ⇒ τ) ⊣ Γ
lamNorm (ap y (var zero) pf) = {!!}
-- the rest are trivial
lamNorm (ap y (var (suc i)) pf) = lam (ap y (var (suc i)) pf) tt
lamNorm (ap y (lam x pf') pf) = lam (ap y (lam x pf') pf) tt
lamNorm (ap y (ap y' x pf') pf) = lam (ap y (ap y' x pf') pf) tt
lamNorm (ap y zero pf) = lam (ap y zero pf) tt
lamNorm (ap y (suc z) pf) = lam (ap y (suc z) pf) tt
lamNorm (ap y (recNat z s n pf') pf) = lam (ap y (recNat z s n pf') pf) tt
lamNorm (var i) = lam (var i) tt
lamNorm (lam x pf) = lam (lam x pf) tt
lamNorm zero = lam zero tt
lamNorm (suc x) = lam (suc x) tt
lamNorm (recNat z s n pf) = lam (recNat z s n pf) tt

apNorm : (y : normal (σ ⇒ τ) ⊣ Γ) (z : normal σ ⊣ Γ) → normal τ ⊣ Γ
apNorm (lam y _) z = {!!}
-- the rest are trivial
apNorm (var i) z = ap (var i) z tt
apNorm (ap y z' pf) z = ap (ap y z' pf) z tt
apNorm (recNat z' s n pf) z = ap (recNat z' s n pf) z tt

recNatNorm : (z : normal τ ⊣ Γ) (s : normal τ ⊣ (Γ , Nat , τ)) (n : normal Nat ⊣ Γ) → normal τ ⊣ Γ
recNatNorm z s zero = z
recNatNorm z s (suc n) = {!!}
-- the rest are trivial
recNatNorm z s (var i) = recNat z s (var i) tt
recNatNorm z s (ap y z' pf) = recNat z s (ap y z' pf) tt
recNatNorm z s (recNat z' s' n' pf) = recNat z s (recNat z' s' n' pf) tt





-- case-lam : ∀ {ℓ} (P : normal (σ ⇒ τ) ⊣ Γ → Set ℓ)
--            → ((x : normal τ ⊣ (Γ , σ)) (pf : isFalse (reducible-unlam x)) → P (lam x pf))
--            → ((x :  normal (σ ⇒ τ) ⊣ Γ) → P x) → ∀ x → P x
-- case-lam _ f _ (lam x pf) = f x pf
-- case-lam - _ f x = f x

-- case-ap-zero : ∀ {ℓ} (P : ∀ {Γ} → normal τ ⊣ Γ → Set ℓ)
--                → (∀ {σ Γ} (y : normal (σ ⇒ τ) ⊣ (Γ , σ)) (pf : isFalse (reducible-lam y)) → P (ap y (var zero) {!!}))
--                → (∀ {Γ} (x :  normal τ ⊣ Γ) → P x) → ∀ {Γ} (x : normal τ ⊣ Γ) → P x
-- case-ap-zero _ f _ (ap y (var zero) pf) = f y pf
-- case-ap-zero _ _ f x = f x

-- case-Nat : ∀ {ℓ} (P : normal Nat ⊣ Γ → Set ℓ)
--            → P zero → ((n : normal Nat ⊣ Γ) → P (suc n))
--            → ((x :  normal Nat ⊣ Γ) → P x) → ∀ x → P x
-- case-Nat _ f _ _ zero = f
-- case-Nat _ _ f _ (suc n) = f n
-- case-Nat _ _ _ f x = f x 





-- data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
--   yes : A → Maybe A
--   no  : Maybe A

-- caseMaybe : ∀ {ℓ} {A : Set ℓ} {ℓ'} (P : Maybe A → Set ℓ') → (∀ a → P (yes a)) → P no → ∀ x → P x
-- caseMaybe P y _ (yes x) = y x
-- caseMaybe P _ n no = n

-- isYes isNo : ∀ {ℓ} {A : Set ℓ} → Maybe A → Set
-- isYes = caseMaybe _ (λ _ → ⊤) ⊥
-- isNo  = caseMaybe _ (λ _ → ⊥) ⊤

-- map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Maybe A → Maybe B
-- map f x = caseMaybe _ (yes ∘ f) no x

-- _>>=_ : ∀ {ℓ} {A B : Set ℓ} → Maybe A → (A → Maybe B) → Maybe B
-- x >>= f = caseMaybe _ f no x

-- infixl 8 _<$>_ _<*>_
-- _<$>_ = map

-- _<*>_ : ∀ {ℓ} {A B : Set ℓ} → Maybe (A → B) → Maybe A → Maybe B
-- x <*> y = x >>= (_<$> y)

-- -- ...
-- strengthen : ∀ Δ → (x : normal τ ⊣ (append (Γ , σ) Δ)) → Maybe (normal τ ⊣ (append Γ Δ))

-- strengthen-lam-β-irred : ∀ Δ (y : normal σ ⇒ τ ⊣ append (Γ , σ) Δ)
--                          → lam-β-irred y → caseMaybe (λ _ → Set) lam-β-irred ⊤ (strengthen Δ y)

-- -- : ∀ Δ → (x : normal τ ⊣ (append (Γ , σ) Δ)) → Maybe (normal τ ⊣ (append Γ Δ))
-- strengthen Δ (var i) = map var (rhs Δ i)
--   where rhs : ∀ Δ (i : τ ∈ (append (Γ , σ) Δ)) → Maybe (τ ∈ (append Γ Δ))
--         rhs ε zero = no
--         rhs ε (suc i) = yes i
--         rhs (Δ , τ) zero = yes zero
--         rhs (Δ , τ) (suc i) = map suc (rhs Δ i)
-- strengthen Δ (lam x pf) = strengthen (Δ , _) x >>= (λ x' →
--                             yes (lam x' {!!}))
-- strengthen Δ (ap y z pf) = strengthen Δ z >>= (λ z' →
--                            caseMaybe ? (λ y' → 
--                              yes (ap y' z' (strengthen-lam-β-irred Δ y pf))) no (strengthen Δ y))
-- strengthen Δ zero = yes zero
-- strengthen Δ (suc x) = map suc (strengthen Δ x)
-- strengthen Δ (recNat τ z s n pf) = strengthen Δ z >>= (λ z' →
--                                    strengthen (Δ , _ , _) s >>= (λ s' →
--                                    strengthen Δ n >>= (λ n' →
--                                      yes (recNat τ z' s' n' {!!}))))

-- strengthen-lam-β-irred Δ (var i) tt = {!!}
-- strengthen-lam-β-irred Δ (lam x pf') ()
-- strengthen-lam-β-irred Δ (ap y z pf') tt = {!!}
--   -- = caseMaybe (λ h → caseMaybe (λ _ → Set) lam-β-irred ⊤
--   --     (h >>=
--   --      (λ y' →
--   --         strengthen Δ z >>=
--   --         (λ z' →
--   --            yes
--   --            (ap y' z' _))))) (λ y' →
--   --   caseMaybe (λ h → caseMaybe _ _ _ (h >>= _)) (λ z' →
--   --     {!!}
--   --     ) tt (strengthen Δ z)) tt (strengthen Δ y)
-- strengthen-lam-β-irred Δ (recNat .(_ ⇒ _) z s n pf') tt = {!!}



-- open import Cubical.Data.Nat
-- open import Cubical.Data.Sum renaming (_⊎_ to _⊔_; map-⊎ to map-⊔)
-- open import Cubical.Data.Unit renaming (Unit to ∗)

-- map-inr : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → A ⊔ B → A ⊔ C
-- map-inr = map-⊔ id

-- infixl 8 _<$>_ _<*>_

-- _<$>_ = map-inr

-- _>>=_ : ∀ {ℓ} {A B C : Set ℓ} → A ⊔ B → (B → A ⊔ C) → A ⊔ C
-- (inl a) >>= _ = inl a
-- (inr x) >>= f = f x

-- _<*>_ : ∀ {ℓ} {A B C : Set ℓ} → A ⊔ (B → C) → A ⊔ B → A ⊔ C
-- x <*> y = x >>= (_<$> y)

-- -- the type of partial functions
-- _⇀_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set _
-- A ⇀ B = A → ∗ ⊔ B


-- hfillPair : ∀ {ℓ} {A : Set ℓ}
--             {φ : I}
--             (u : ∀ i → Partial φ A)
--             (u0 : A [ φ ↦ u i0 ]) → Σ A (outS u0 ≡_)
-- hfillPair {φ = φ} u u0 = < (hfill u u0 i1) , (λ j → hfill u u0 j) >

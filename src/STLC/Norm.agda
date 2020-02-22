{-# OPTIONS --cubical --safe #-}
module STLC.Norm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import STLC.Transformations
open import STLC.Base


-----------------------------
-- The Type of Normal Forms
-----------------------------

data NormType : Set where
  Nf : NormType
  Ne : NormType

data [_]-normal_⊣_ : NormType → Typ → Ctx → Set

normal_⊣_ neutral_⊣_ : Typ → Ctx → Set
normal_⊣_  = [ Nf ]-normal_⊣_
neutral_⊣_ = [ Ne ]-normal_⊣_

data [_]-normal_⊣_ where

  -- normal terms of type (τ ⇒ σ) are always lambdas
  lam : (x : normal τ ⊣ (Γ , σ)) → normal (σ ⇒ τ) ⊣ Γ
  
  -- normal terms of type Unit are either tt or a neutral term of type Unit
  tt : normal Unit ⊣ Γ
  ne : neutral Unit ⊣ Γ → normal Unit ⊣ Γ

  -- neutral terms are either a variable or a function application
  var : (i : τ ∈ Γ) → neutral τ ⊣ Γ
  apⁿ : (f : neutral (σ ⇒ τ) ⊣ Γ) (z : normal σ ⊣ Γ) → neutral τ ⊣ Γ

isSet-normal : ∀ {t} → isSet ([ t ]-normal τ ⊣ Γ)
isSet-normal = {!!}


-- order-preserving embeddings between contexts
data _~>ᵉ_ : Ctx → Ctx → Set where
  ε : ε ~>ᵉ ε
  drop : Γ ~>ᵉ Δ →  Γ      ~>ᵉ (Δ , τ)
  keep : Γ ~>ᵉ Δ → (Γ , τ) ~>ᵉ (Δ , τ)

id*ᵉ : Γ ~>ᵉ Γ
id*ᵉ {ε} = ε
id*ᵉ {Γ , τ} = keep (id*ᵉ {Γ})

_∘*ᵉ_ : Δ ~>ᵉ Ε → Γ ~>ᵉ Δ → Γ ~>ᵉ Ε
ε      ∘*ᵉ f      = f
drop g ∘*ᵉ f      = drop (g ∘*ᵉ f)
keep g ∘*ᵉ drop f = drop (g ∘*ᵉ f)
keep g ∘*ᵉ keep f = keep (g ∘*ᵉ f)

∘*-idʳ : (μ : Γ ~>ᵉ Δ) → μ ∘*ᵉ id*ᵉ ≡ μ
∘*-idʳ ε = refl
∘*-idʳ (drop μ) = cong drop (∘*-idʳ μ)
∘*-idʳ (keep μ) = cong keep (∘*-idʳ μ)

subᵉ-∈ : (Γ ~>ᵉ Δ) → τ ∈ Γ → τ ∈ Δ
subᵉ-∈ ε x = x
subᵉ-∈ (drop f) x = suc (subᵉ-∈ f x)
subᵉ-∈ (keep f) zero = zero
subᵉ-∈ (keep f) (suc x) = suc (subᵉ-∈ f x)

subᵉ-∈-id*ᵉ : ∀ (i : τ ∈ Γ) → subᵉ-∈ id*ᵉ i ≡ i
subᵉ-∈-id*ᵉ zero j = zero
subᵉ-∈-id*ᵉ (suc i) j = suc (subᵉ-∈-id*ᵉ i j)

-- embeddings on normal/neutral terms

subᵉ : ∀ {t} → (Γ ~>ᵉ Δ) → [ t ]-normal τ ⊣ Γ → [ t ]-normal τ ⊣ Δ
subᵉ μ (lam x)   = lam (subᵉ (keep μ) x)
subᵉ μ tt        = tt
subᵉ μ (ne x)    = ne (subᵉ μ x)
subᵉ μ (var i)   = var (subᵉ-∈ μ i)
subᵉ μ (apⁿ f z) = apⁿ (subᵉ μ f) (subᵉ μ z)

subᵉ-id*ᵉ : ∀ {t} (x : [ t ]-normal τ ⊣ Γ) → subᵉ id*ᵉ x ≡ x
subᵉ-id*ᵉ (lam x) i   = lam (subᵉ-id*ᵉ x i)
subᵉ-id*ᵉ tt i        = tt
subᵉ-id*ᵉ (ne x) i    = ne (subᵉ-id*ᵉ x i)
subᵉ-id*ᵉ (var i) j   = var (subᵉ-∈-id*ᵉ i j)
subᵉ-id*ᵉ (apⁿ f z) i = apⁿ (subᵉ-id*ᵉ f i) (subᵉ-id*ᵉ z i)


-- ...

_⟦⊣⟧_ : Typ → Ctx → Set
(σ ⇒ τ) ⟦⊣⟧ Γ = ∀ {Δ} → Γ ~>ᵉ Δ → σ ⟦⊣⟧ Δ → τ ⟦⊣⟧ Δ
Unit    ⟦⊣⟧ Γ = normal Unit ⊣ Γ

open Transformations {Typ} {_⟦⊣⟧_} public using ()
  renaming (_~>_ to _⟦~>⟧_; _,*_ to _⟦,*⟧_; head* to ⟦head*⟧; tail* to ⟦tail*⟧; ,*-η to ⟦,*⟧-η)

-- embeddings on ...

⟦subᵉ⟧ : (Γ ~>ᵉ Δ) → τ ⟦⊣⟧ Γ → τ ⟦⊣⟧ Δ
⟦subᵉ⟧ {τ = σ ⇒ τ} f x = λ g → x (g ∘*ᵉ f)
⟦subᵉ⟧ {τ = Unit } f x = subᵉ f x

_⟦∘*ᵉ⟧_ : (Δ ~>ᵉ Ε) → Γ ⟦~>⟧ Δ → Γ ⟦~>⟧ Ε
f ⟦∘*ᵉ⟧ e = λ τ i → ⟦subᵉ⟧ f (e τ i)

⟦subᵉ⟧-id*ᵉ : (⟦x⟧ : τ ⟦⊣⟧ Γ) → ⟦subᵉ⟧ id*ᵉ ⟦x⟧ ≡ ⟦x⟧
⟦subᵉ⟧-id*ᵉ {σ ⇒ τ} ⟦x⟧ i = λ g → ⟦x⟧ (∘*-idʳ g i)
⟦subᵉ⟧-id*ᵉ {Unit } ⟦x⟧ = subᵉ-id*ᵉ ⟦x⟧

⟦∘*ᵉ⟧-id*ᵉ : (⟦η⟧ : Γ ⟦~>⟧ Δ) → (id*ᵉ ⟦∘*ᵉ⟧ ⟦η⟧) ≡ ⟦η⟧
⟦∘*ᵉ⟧-id*ᵉ ⟦η⟧ j τ i = ⟦subᵉ⟧-id*ᵉ (⟦η⟧ τ i) j


-- ...

reflect : neutral τ ⊣ Γ → τ ⟦⊣⟧ Γ
reify : τ ⟦⊣⟧ Γ → normal τ ⊣ Γ

reflect {σ ⇒ τ} x = λ f u → reflect (apⁿ (subᵉ f x) (reify u))
reflect {Unit} x = ne x

reify {σ ⇒ τ} x = lam (reify (x (drop id*ᵉ) (reflect (var zero))))
reify {Unit} x = x


-- presheaf semantics

⟦_⟧  : (x : τ ⊣ Γ) → ∀ {Δ} (e : Γ ⟦~>⟧ Δ) → τ ⟦⊣⟧ Δ
⟦_⟧* : (f : Γ ~> Ε) → ∀ {Δ} (e : Ε ⟦~>⟧ Δ) → Γ ⟦~>⟧ Δ

open import Cubical.Data.Prod
private

  -- this lemma is the hard part...
  lem₁ : (x : (σ ⇒ τ) ⊣ Γ) (e : Γ ⟦~>⟧ Δ) (f : Δ ~>ᵉ Ε) → ⟦ x ⟧ (f ⟦∘*ᵉ⟧ e) id*ᵉ ≡ ⟦ x ⟧ e f
  lem₁ x e f = {!!}

  lem₂ : ∀ {Γ₀} (η : Γ₀ ~> Γ) (e : Γ ⟦~>⟧ Δ) (f : Δ ~>ᵉ Ε) (u : σ ⟦⊣⟧ Ε)
         → ((f ⟦∘*ᵉ⟧ (⟦ η ⟧* e)) ⟦,*⟧ u) ≡ ⟦ ↑ η ⟧* ((f ⟦∘*ᵉ⟧ e) ⟦,*⟧ u)
  lem₂ = {!!}

⟦trunc⟧ : isSet (τ ⟦⊣⟧ Γ)
⟦trunc⟧ {σ ⇒ τ} x y p q i j μ z = ⟦trunc⟧ (x μ z) (y μ z) (λ i → p i μ z) (λ i → q i μ z) i j
⟦trunc⟧ {Unit} = isSet-normal

⟦ sub η x ⟧ e = ⟦ x ⟧ (⟦ η ⟧* e)
⟦ sub-id* x i ⟧ e = ⟦ x ⟧ e
⟦ sub-∘* η ζ x i ⟧ e = ⟦ x ⟧ (⟦ ζ ⟧* (⟦ η ⟧* e))
⟦ var i ⟧ e = e _ i
⟦ tt ⟧ e = tt
⟦ lam x ⟧ e f u = ⟦ x ⟧ ((f ⟦∘*ᵉ⟧ e) ⟦,*⟧ u)
⟦ unlam f ⟧ e = ⟦ f ⟧ (⟦tail*⟧ e) id*ᵉ (⟦head*⟧ e)
⟦ lam-β x i ⟧ e = ⟦ x ⟧ ((cong (_⟦,*⟧ ⟦head*⟧ e) (⟦∘*ᵉ⟧-id*ᵉ (⟦tail*⟧ e)) ∙ ⟦,*⟧-η e) i)
⟦ lam-η x i ⟧ {Δ} e {Ε} f = lem₁ x e f i
⟦ sub-var η i j ⟧ e = ⟦ η _ i ⟧ e
⟦ sub-lam η x i ⟧ e f u = ⟦ x ⟧ (lem₂ η e f u i)
⟦ sub-tt η i ⟧ e = tt
⟦ trunc x y p q i j ⟧ e = ⟦trunc⟧ (⟦ x ⟧ e) (⟦ y ⟧ e) (λ i → ⟦ p i ⟧ e) (λ i → ⟦ q i ⟧ e) i j

⟦ f ⟧* e = λ τ i → ⟦ f τ i ⟧ e


-- open TransformationProperties {Typ} {_⟦⊣⟧_} {reflect ∘ var} {{!!}} public
--   using () renaming (id* to ⟦id*⟧)

⟦id*⟧ : Γ ⟦~>⟧ Γ
⟦id*⟧ τ i = reflect (var i)


-----------------------------------------------
-- Normalization, Stability, and Completeness
-----------------------------------------------

norm : τ ⊣ Γ → normal τ ⊣ Γ
norm x = reify (⟦ x ⟧ ⟦id*⟧)

emb : ∀ {t} → [ t ]-normal τ ⊣ Γ → τ ⊣ Γ
emb (lam x) = lam (emb x)
emb tt = tt
emb (ne x) = emb x
emb (var i) = var i
emb (apⁿ f z) = ap (emb f) (emb z)

private
  lem₃ : Path ((Γ , τ) ⟦~>⟧ (Γ , τ)) (((drop id*ᵉ) ⟦∘*ᵉ⟧ ⟦id*⟧) ⟦,*⟧ (reflect (var zero))) ⟦id*⟧
  lem₃ = {!!}

stable   : (x : normal τ ⊣ Γ)  → norm (emb x) ≡ x -- recall: norm (emb x) = reify (⟦ emb x ⟧ ⟦id*⟧)
stableNe : (x : neutral τ ⊣ Γ) → ⟦ emb x ⟧ ⟦id*⟧ ≡ reflect x

stable (lam x) i = lam (((λ i → reify (⟦ emb x ⟧ (lem₃ i))) ∙ stable x) i)
stable tt i = tt
stable (ne x) i = stableNe x i
stableNe (var i) j = reflect (var i)
stableNe (apⁿ f x) i = (
  ⟦ emb f ⟧ ⟦id*⟧ id*ᵉ (⟦ emb x ⟧ ⟦id*⟧)                 ≡[ i ]⟨ stableNe f i id*ᵉ (⟦ emb x ⟧ ⟦id*⟧) ⟩
--reflect f      id*ᵉ (⟦ emb x ⟧ ⟦id*⟧)                 ≡⟨ refl ⟩
  reflect (apⁿ (subᵉ id*ᵉ f) (reify (⟦ emb x ⟧ ⟦id*⟧))) ≡[ i ]⟨ reflect (apⁿ (subᵉ-id*ᵉ f i) (stable x i)) ⟩
  reflect (apⁿ f x) ∎) i

complete : (x : τ ⊣ Γ) → emb (norm x) ≡ x
complete x = {!!}

-- Thus, the type of terms τ ⊣ Γ is equivalent to the type of *normal* terms τ ⊣ Γ

normEquiv : isEquiv (norm {τ} {Γ})
normEquiv = isoToIsEquiv (iso norm emb stable complete)

normPath : (τ ⊣ Γ) ≡ (normal τ ⊣ Γ)
normPath = isoToPath (iso norm emb stable complete)

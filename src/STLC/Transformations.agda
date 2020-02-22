{-# OPTIONS --cubical --safe #-}
module STLC.Transformations where

open import Cubical.Foundations.Prelude

module Contexts {Typ : Type₀} where
  
  -- Contexts are lists of types
  data Ctx : Type₀ where
    ε : Ctx
    _,_ : Ctx → Typ → Ctx

  private
    variable
      τ σ ρ : Typ
      Γ Δ Ε Ζ : Ctx

  -- A proof that a type is in a context is an index at which it appears
  data _∈_ : Typ → Ctx → Type₀ where
    zero : τ ∈ (Γ , τ)
    suc  : τ ∈ Γ → τ ∈ (Γ , σ)

  ∈-Rec : ∀ {ℓ} (P : ∀ τ Γ → Type ℓ)
          → (∀ {τ Γ} → P τ (Γ , τ))
          → (∀ {σ τ Γ} → P τ Γ → P τ (Γ , σ))
          → ∀ {τ Γ} → τ ∈ Γ → P τ Γ
  ∈-Rec P z s zero = z
  ∈-Rec P z s (suc i) = s (∈-Rec P z s i)

module Transformations
         {Typ : Type₀}
         {_⊣_ : Typ → Contexts.Ctx → Type₀} where
  open Contexts {Typ}
  private
    variable
      τ σ ρ : Typ
      Γ Δ Ε Ζ : Ctx

  -- Transformations Γ ~> Δ are maps from elements of Γ to terms τ ⊣ Δ
  _~>_ : Ctx → Ctx → Type₀
  Γ ~> Δ = ∀ τ (i : τ ∈ Γ) → (τ ⊣ Δ)

  ~>Ext : {f g : Γ ~> Δ} → (∀ τ i → f τ i ≡ g τ i) → f ≡ g
  ~>Ext eq j = λ τ i → eq τ i j

  -- ~> has a list structure on its first argument

  ε* : ε ~> Δ
  ε* τ ()

  _,*_ : (Γ ~> Δ) → (x : τ ⊣ Δ) → (Γ , τ) ~> Δ
  (f ,* x) τ zero = x
  (f ,* x) τ (suc i) = f τ i

  head* : ((Γ , τ) ~> Δ) → τ ⊣ Δ
  head* f = f _ zero

  tail* : ((Γ , τ) ~> Δ) → Γ ~> Δ
  tail* f τ i = f τ (suc i)

  -- the list structure on ~> behaves as one would expect:

  ε*-η : ∀ (f : ε ~> Δ) → f ≡ ε*
  ε*-η f = ~>Ext (λ τ ())

  ,*-η : ∀ (f : (Γ , τ) ~> Δ) → (tail* f ,* head* f) ≡ f
  ,*-η f = ~>Ext (λ { τ zero    → refl
                    ; τ (suc i) → refl } )

  head*-,* : ∀ (f : Γ ~> Δ) (x : τ ⊣ Δ) → head* (f ,* x) ≡ x
  head*-,* f x = refl

  tail*-,* : ∀ (f : Γ ~> Δ) (x : τ ⊣ Δ) → tail* (f ,* x) ≡ f
  tail*-,* f x = ~>Ext (λ τ i → refl)

module TransformationProperties
         {Typ : Type₀}
         {_⊣_ : Typ → Contexts.Ctx → Type₀}
         {var : ∀ {τ} {Γ} (i : τ Contexts.∈ Γ) → τ ⊣ Γ}
         {sub : ∀ {Γ} {Δ} {τ} (η : Γ Transformations.~> Δ) (x : τ ⊣ Γ) → τ ⊣ Δ} where
  open Contexts {Typ}
  open Transformations {Typ} {_⊣_}
  private
    variable
      τ σ ρ : Typ
      Γ Δ Ε Ζ : Ctx

  -- ~> also forms a category (using var and sub from _⊣_)

  id* : Γ ~> Γ
  id* τ i = var i

  _∘*_ : (Δ ~> Ε) → (Γ ~> Δ) → Γ ~> Ε
  (g ∘* f) τ i = sub g (f τ i)

  -- _,*_ is a natural transformation

  ∘*-,* : ∀ (g : Δ ~> Ε) (f : Γ ~> Δ) (x : τ ⊣ Δ)
          → g ∘* (f ,* x) ≡ (g ∘* f) ,* (sub g x)
  ∘*-,* g f x = ~>Ext (λ { τ zero    → refl
                         ; τ (suc i) → refl } )

  -- Some useful derived notions:

  wkn : Γ ~> (Γ , τ)
  wkn = tail* id*

  ↑_ : (f : Γ ~> Δ) → (Γ , τ) ~> (Δ , τ)
  ↑ f = (wkn ∘* f) ,* head* id*

  ⟨_⟩ : (x : τ ⊣ Γ) → (Γ , τ) ~> Γ
  ⟨ x ⟩ = id* ,* x

  module MoreProperties (sub-id* : ∀ {τ} {Γ} (x : τ ⊣ Γ) → sub id* x ≡ x)
                        (sub-∘*  : ∀ {Δ Ε Γ} {τ} (η : Δ ~> Ε) (ζ : Γ ~> Δ) (x : τ ⊣ Γ)
                                   → sub (η ∘* ζ) x ≡ sub η (sub ζ x))
                        (sub-var : ∀ {Γ Δ τ} (η : Γ ~> Δ) (i : τ ∈ Γ) → sub η (var i) ≡ η τ i) where

    -- the categorial structure on ~> behaves as one would expect:

    id*-l : ∀ (f : Γ ~> Δ) → id* ∘* f ≡ f
    id*-l f = ~>Ext (λ τ i → sub-id* (f τ i))

    id*-r : ∀ (f : Γ ~> Δ) → f ∘* id* ≡ f
    id*-r f = ~>Ext (λ τ i → sub-var f i)

    ∘*-assoc : ∀ (h : Ε ~> Ζ) (g : Δ ~> Ε) (f : Γ ~> Δ)
               → (h ∘* g) ∘* f ≡ h ∘* (g ∘* f)
    ∘*-assoc h g f = ~>Ext (λ τ i → sub-∘* h g (f τ i))

    -- Some more facts:

    ,*-wkn : ∀ (f : Γ ~> Δ) (x : τ ⊣ Δ) → (f ,* x) ∘* wkn ≡ f
    ,*-wkn f x = ~>Ext (λ τ i → sub-var (f ,* x) (suc i))

    ⟨⟩-↑ : ∀ (x : τ ⊣ Δ) (f : Γ ~> Δ) → ⟨ x ⟩ ∘* (↑ f) ≡ f ,* x
    ⟨⟩-↑ x f =  (id* ,* x) ∘* ((wkn ∘* f) ,* var zero)                  ≡⟨ i ⟩
              ((id* ,* x) ∘* (wkn ∘* f)) ,* sub (id* ,* x) (var zero)  ≡⟨ ii  ⟩
              ((id* ,* x) ∘* (wkn ∘* f)) ,* x                          ≡⟨ iii ⟩
              (((id* ,* x) ∘* wkn) ∘* f) ,* x                          ≡⟨ iv ⟩
                              (id* ∘* f) ,* x                          ≡⟨ v ⟩
                                       f ,* x                          ∎
      where i   = ∘*-,* (id* ,* x) (wkn ∘* f) (var zero)
            ii  = cong (((id* ,* x) ∘* (wkn ∘* f)) ,*_) (sub-var (id* ,* x) zero)
            iii = cong (_,* x) (sym (∘*-assoc (id* ,* x) wkn f))
            iv  = cong (λ z → (z ∘* f) ,* x) (,*-wkn id* (x))
            v   = cong (_,* x) (id*-l f)


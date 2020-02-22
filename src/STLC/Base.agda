{-# OPTIONS --cubical --safe #-}
module STLC.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import STLC.Transformations


-----------------------
-- Types and Contexts
-----------------------

-- The type of (STLC) types
data Typ : Type₀ where
  Unit : Typ
  _⇒_ : Typ → Typ → Typ

-- The type of contexts over Typ
open Contexts {Typ} public

variable
  τ σ ρ : Typ
  Γ Δ Ε Ζ : Ctx


------------------------------
-- Terms and Transformations
------------------------------

-- The type of judgements x : τ ⊣ Γ ("x has type τ in context Γ")
data _⊣_ : Typ → Ctx → Type₀

-- The type of transfomations Γ ~> Δ between contexts
open Transformations {Typ} {_⊣_} public

id* : Γ ~> Γ
_∘*_ : (Δ ~> Ε) → (Γ ~> Δ) → Γ ~> Ε
↑_ : (f : Γ ~> Δ) → (Γ , τ) ~> (Δ , τ)

data _⊣_ where

  -- permit arbitrary substutions on contexts (explicit substitution)
  sub : (η : Γ ~> Δ) (x : τ ⊣ Γ) → τ ⊣ Δ

  -- sub is a functor on (~>, id*, ∘*)
  sub-id* : (x : τ ⊣ Γ) → sub id* x ≡ x
  sub-∘*  : (η : Δ ~> Ε) (ζ : Γ ~> Δ) (x : τ ⊣ Γ)
            → sub (η ∘* ζ) x ≡ sub η (sub ζ x)

  -- variables as de Bruijn indices
  var : (i : τ ∈ Γ) → τ ⊣ Γ

  -- unit type intro (elim is free)
  tt : Unit ⊣ Γ

  -- function type intro
  lam : (y : τ ⊣ (Γ , σ)) → (σ ⇒ τ) ⊣ Γ

  -- function type elim and uniqueness (the usual elim (ap) is *defined* below)
  unlam : (f : (σ ⇒ τ) ⊣ Γ) → τ ⊣ (Γ , σ)
  lam-β : (x : τ ⊣ (Γ , σ)) → unlam (lam x) ≡ x
  lam-η : (f : (σ ⇒ τ) ⊣ Γ) → lam (unlam f) ≡ f

  -- computation rules for substititon
  sub-var : (η : Γ ~> Δ) (i : τ ∈ Γ) → sub η (var i) ≡ η τ i
  sub-lam : (η : Γ ~> Δ) (x : τ ⊣ (Γ , σ)) → sub η (lam x) ≡ lam (sub (↑ η) x)
  -- sub-ap will be derivable using lam-β and lam-η!
  sub-tt : (η : Γ ~> Δ) → sub η tt ≡ tt

  -- set truncation (without this, sub would requires an infinite number of coherences)
  trunc : isSet (τ ⊣ Γ)

open TransformationProperties {Typ} {_⊣_} {var} {sub} hiding (id*; _∘*_; ↑_) public
id* = TransformationProperties.id* {Typ} {_⊣_} {var} {sub}
_∘*_ = TransformationProperties._∘*_ {Typ} {_⊣_} {var} {sub}
↑_ = TransformationProperties.↑_ {Typ} {_⊣_} {var} {sub}

open MoreProperties sub-id* sub-∘* sub-var public


--------------------------------
-- ap / unlam and Substitution
--------------------------------

-- the usual notion of function elimination
ap : (f : (σ ⇒ τ) ⊣ Γ) (x : σ ⊣ Γ) → τ ⊣ Γ
ap f x = sub ⟨ x ⟩ (unlam f)

-- the 'missing' substitution rules for unlam and ap

unlam-sub : (η : Γ ~> Δ) (f : (σ ⇒ τ) ⊣ Γ)
            → unlam (sub η f) ≡ sub (↑ η) (unlam f)
unlam-sub η f =
  unlam (sub η f                  ) ≡⟨ cong (unlam ∘ sub _) (sym (lam-η f)) ⟩
  unlam (sub η (lam (unlam f))    ) ≡⟨ cong unlam (sub-lam η (unlam f)) ⟩
  unlam (lam (sub (↑ η) (unlam f))) ≡⟨ lam-β (sub (↑ η) (unlam f)) ⟩
              sub (↑ η) (unlam f)   ∎

sub-ap : (η : Γ ~> Δ) (f : (σ ⇒ τ) ⊣ Γ) (x : σ ⊣ Γ)
         → sub η (ap f x) ≡ ap (sub η f) (sub η x)
sub-ap η f x =
  sub η (sub ⟨ x ⟩ (unlam f))             ≡⟨ sym (sub-∘* η ⟨ x ⟩ (unlam f)) ⟩
  sub (η ∘* ⟨ x ⟩) (unlam f)              ≡⟨ cong (λ z → sub z (unlam f)) (∘*-,* η id* x) ⟩
  sub ((η ∘* id*) ,* sub η x) (unlam f)  ≡⟨ cong (λ z → sub (z ,* sub η x) (unlam f)) (id*-r η) ⟩
  sub (η ,* sub η x) (unlam f)           ≡⟨ cong (λ z → sub z (unlam f)) (sym (⟨⟩-↑ (sub η x) η)) ⟩
  sub (⟨ sub η x ⟩ ∘* (↑ η)) (unlam f)    ≡⟨ sub-∘* (id* ,* (sub η x)) (↑ η) (unlam f) ⟩
  sub ⟨ sub η x ⟩ (sub (↑ η) (unlam f))   ≡⟨ cong (sub (id* ,* (sub η x))) (sym (unlam-sub η f)) ⟩
  sub ⟨ sub η x ⟩ (unlam (sub η f))       ∎


----------------
-- Other Facts
----------------

-- Variables can be expressed entirely in terms of head*, tail*, and id*.
-- Since head* id* ≡ var zero and tail* id* ≡ wkn, this is expressing the fact that:
--   var i ≡ sub (wkn ∘* ... ∘* wkn) (var zero)
var-≡ : ∀ {τ Γ} (i : τ ∈ Γ) → var i ≡ (∈-Rec _⊣_ (head* id*) (sub (tail* id*)) i)
var-≡ zero = refl
var-≡ (suc i) = (sym (sub-var wkn i)) ∙ (cong (sub (tail* id*)) (var-≡ i))

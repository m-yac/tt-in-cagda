
----------------------------------------------------------------------------
--
-- A higher inductive type for a simply typed lambda calculus
-- 
-- Inspired by: Type Theory in Type Theory using Quotient Inductive Types
--              by Thorsten Altenkirch and Ambrus Kaposi
-- See: http://www.cs.nott.ac.uk/~psztxa/publ/tt-in-tt.pdf
-- 
----------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}
module STLC+N.Base where

open import Cubical.Foundations.Prelude renaming (_,_ to <_,_>)
open import Cubical.Foundations.Function
open import Cubical.Foundations.BiInvEquiv

_≡⟨⟩_ : ∀ {ℓ} {A : Type ℓ} {z : A} (x : A) → x ≡ z → x ≡ z
_ ≡⟨⟩ eq = eq
infixr 2 _≡⟨⟩_

infixl 6 _,_ _,*_
infixr 7 _∘*_
infixr 3 ↑_



-----------------
-- Declarations
-----------------

-- We will mutually inductively define:

-- The type of contexts
data Ctx : Type₀

-- The type of transformations / generalized substitutions from a context Γ to Δ
_~>_ : Ctx → Ctx → Type₀

-- The type of (STLC) types
data Typ : Type₀

-- The type of judgements x : τ ⊣ Γ ("x has type τ in context Γ")
data _⊣_ : Typ → Ctx → Type₀

variable
  Γ Δ Ε Ζ : Ctx
  τ σ ρ : Typ
  x y z : τ ⊣ Γ



---------------------------------
-- Contexts and Transformations
---------------------------------

data Ctx where
  ε : Ctx
  _,_ : Ctx → Typ → Ctx

append : Ctx → Ctx → Ctx
append Γ ε = Γ
append Γ (Δ , x) = append Γ Δ , x

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


-- Transformations Γ ~> Δ are maps from elements of Γ to terms τ ⊣ Δ
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

-- ~> also forms a category (using var and sub from _⊣_, which has yet to be defined)

id* : Γ ~> Γ
-- id* τ i = var i

_∘*_ : (Δ ~> Ε) → (Γ ~> Δ) → Γ ~> Ε
-- (g ∘* f) τ i = sub g (f τ i)

-- Some useful derived notions:

wkn : Γ ~> (Γ , τ)
wkn = tail* id*

↑_ : (f : Γ ~> Δ) → (Γ , τ) ~> (Δ , τ)
↑ f = (wkn ∘* f) ,* head* id*

⟨_⟩ : (x : τ ⊣ Γ) → (Γ , τ) ~> Γ
⟨ x ⟩ = id* ,* x



--------------------
-- Typs and Terms
--------------------

data Typ where
  _⇒_ : Typ → Typ → Typ
  Nat : Typ

-- ...
unlamʳ unlamˡ : (f : (σ ⇒ τ) ⊣ Γ) → τ ⊣ (Γ , σ)
-- unlamʳ y = apʳ (sub wkn y) (var zero)
-- unlamˡ y = apˡ (sub wkn y) (var zero)

data _⊣_ where

  -- permit arbitrary substutions on contexts (explicit substitution)
  sub : (f : Γ ~> Δ) (x : τ ⊣ Γ) → τ ⊣ Δ

  -- sub is a functor on (~>, id*, ∘*)
  sub-id* : (x : τ ⊣ Γ) → sub id* x ≡ x
  sub-∘*  : (g : Δ ~> Ε) (f : Γ ~> Δ) (x : τ ⊣ Γ)
            → sub (g ∘* f) x ≡ sub g (sub f x)

  -- variables as de Bruijn indices
  var : (i : τ ∈ Γ) → τ ⊣ Γ

  -- function type intro
  lam : (x : τ ⊣ (Γ , σ)) → (σ ⇒ τ) ⊣ Γ

  -- function type elim (left) and β
  apˡ    : (y : (σ ⇒ τ) ⊣ Γ) (z : σ ⊣ Γ) → τ ⊣ Γ
  lam-βˡ : (x : τ ⊣ (Γ , σ)) (z : σ ⊣ Γ) → apˡ (lam x) z ≡ sub ⟨ z ⟩ x

  -- function type elim (right) and η
  apʳ        : (y : (σ ⇒ τ) ⊣ Γ) (z : σ ⊣ Γ) → τ ⊣ Γ
  lam-ηʳ     : (y : (σ ⇒ τ) ⊣ Γ) → lam (unlamʳ y) ≡ y -- recall that unlamʳ y = apʳ (sub wkn y) (var zero)
  apʳ-unlamˡ : (y : (σ ⇒ τ) ⊣ Γ) (z : σ ⊣ Γ) → apʳ y z ≡ sub ⟨ z ⟩ (unlamˡ y)

  -- fix intro and β (not total!)
  fix   : (y : (τ ⇒ τ) ⊣ Γ) → τ ⊣ Γ
  fix-β : (y : (τ ⇒ τ) ⊣ Γ) → fix y ≡ apˡ y (fix y)

  -- natural number intro and elim
  zero : Nat ⊣ Γ
  suc  : (n : Nat ⊣ Γ) → Nat ⊣ Γ
  recNat : (z : τ ⊣ Γ) (s : τ ⊣ (Γ , Nat , τ)) (n : Nat ⊣ Γ) → τ ⊣ Γ

  -- natural number β
  recNat-zero : (z : τ ⊣ Γ) (s : τ ⊣ (Γ , Nat , τ))
                → recNat z s zero ≡ z
  recNat-suc  : (z : τ ⊣ Γ) (s : τ ⊣ (Γ , Nat , τ)) (n : Nat ⊣ Γ)
                → recNat z s (suc n) ≡ sub (id* ,* n ,* recNat z s n) s

  -- computation rules for substititon
  sub-var : (f : Γ ~> Δ) (i : τ ∈ Γ) → sub f (var i) ≡ f τ i
  sub-lam : (f : Γ ~> Δ) (x : τ ⊣ (Γ , σ))
            → sub f (lam x) ≡ lam (sub (↑ f) x)
  -- sub-ap will be derivable using lam-β and lam-η!
  sub-zero : (f : Γ ~> Δ) → sub f zero ≡ zero
  sub-suc  : (f : Γ ~> Δ) (n : Nat ⊣ Γ) → sub f (suc n) ≡ suc (sub f n)
  sub-recNat : (f : Γ ~> Δ) (z : τ ⊣ Γ) (s : τ ⊣ (Γ , Nat , τ)) (n : Nat ⊣ Γ)
               → sub f (recNat z s n) ≡ recNat (sub f z) (sub (↑ ↑ f) s) (sub f n)

-- Skipped definitions now that everything is is scope:
id* τ i = var i
(g ∘* f) τ i = sub g (f τ i)
unlamˡ y = apˡ (sub wkn y) (var zero)
unlamʳ y = apʳ (sub wkn y) (var zero)



---------------------
-- First Properties
---------------------

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

-- _,*_ is a natural transformation

∘*-,* : ∀ (g : Δ ~> Ε) (f : Γ ~> Δ) (x : τ ⊣ Δ)
        → g ∘* (f ,* x) ≡ (g ∘* f) ,* (sub g x)
∘*-,* g f x = ~>Ext (λ { τ zero    → refl
                       ; τ (suc i) → refl } )

-- the categorial structure on ~> behaves as one would expect -- using the sub laws from _⊣_!

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
⟨⟩-↑ x f =  (id* ,* x) ∘* ((wkn ∘* f) ,* var zero)                  ≡⟨ ∘*-,* (id* ,* x) (wkn ∘* f) (var zero) ⟩
          ((id* ,* x) ∘* (wkn ∘* f)) ,* sub (id* ,* x) (var zero)  ≡⟨ cong (((id* ,* x) ∘* (wkn ∘* f)) ,*_) (sub-var (id* ,* x) zero) ⟩
          ((id* ,* x) ∘* (wkn ∘* f)) ,* x                          ≡⟨ cong (_,* x) (sym (∘*-assoc (id* ,* x) wkn f)) ⟩
          (((id* ,* x) ∘* wkn) ∘* f) ,* x                          ≡⟨ cong (λ z → (z ∘* f) ,* x) (,*-wkn id* (x)) ⟩
                          (id* ∘* f) ,* x                          ≡⟨ cong (_,* x) (id*-l f) ⟩
                                   f ,* x                          ∎

-- Variables can be expressed entirely in terms of head*, tail*, id*! (recall head* id* ≡ var zero, tail* id* ≡ wkn)
-- In particular: var i ≡ sub (wkn ∘* ... ∘* wkn) (var zero)
var-≡ : ∀ {τ Γ} (i : τ ∈ Γ) → var i ≡ (∈-Rec _⊣_ (head* id*) (sub (tail* id*)) i)
var-≡ zero = refl
var-≡ (suc i) = (sym (sub-var wkn i)) ∙ (cong (sub (tail* id*)) (var-≡ i))



--------------------------------------
-- apˡ vs. apʳ vs. unlamʳ vs. unlamˡ
--------------------------------------

-- The goal of this section is to show that apˡ ≡ apʳ! We start with some equalities:

-- using lam-βˡ, we can derive an equality for apˡ analgous to apʳ-unlamˡ
apˡ-unlamʳ : (y : (σ ⇒ τ) ⊣ Γ) (z : σ ⊣ Γ) → apˡ y z ≡ sub ⟨ z ⟩ (unlamʳ y)
apˡ-unlamʳ y z =
  apˡ y z                   ≡⟨ cong (λ x → apˡ x z) (sym (lam-ηʳ y)) ⟩
  apˡ (lam (unlamʳ y)) z    ≡⟨ lam-βˡ (unlamʳ y) z ⟩
  sub ⟨ z ⟩ (unlamʳ y) ∎

-- we can also derive an equality for unlamˡ analgous to to lam-ηʳ
unlam-βˡ : (x : τ ⊣ (Γ , σ)) → unlamˡ (lam x) ≡ x
unlam-βˡ x = 
  apˡ (sub wkn (lam x)) (var zero)      ≡⟨ cong (λ z → apˡ z (var zero)) (sub-lam wkn x) ⟩
  apˡ (lam (sub (↑ wkn) x)) (var zero)  ≡⟨ lam-βˡ _ (var zero) ⟩
  sub ⟨ var zero ⟩ (sub (↑ wkn) x)       ≡⟨ sym (sub-∘* ⟨ var zero ⟩ (↑ wkn) x) ⟩
  sub (⟨ var zero ⟩ ∘* (↑ wkn)) x        ≡⟨ cong (λ z → sub z x) (⟨⟩-↑ (var zero) wkn) ⟩
  sub (wkn ,* var zero) x               ≡⟨ cong (λ z → sub z x) (,*-η id*) ⟩
  sub id* x                             ≡⟨ sub-id* x ⟩
  x                                     ∎

-- perhaps a more apt name:
unlam-ηʳ : (x : (σ ⇒ τ) ⊣ Γ) → lam (unlamʳ x) ≡ x
unlam-ηʳ = lam-ηʳ


-- lam with unlamˡ and unlamʳ define a bi-invertible equivalence:
lam-biinvequiv : BiInvEquiv (τ ⊣ (Γ , σ)) ((σ ⇒ τ) ⊣ Γ)
lam-biinvequiv = record { fun = lam ; invr = unlamʳ ; invr-rightInv = unlam-ηʳ
                                    ; invl = unlamˡ ; invl-leftInv  = unlam-βˡ }

-- ...thus:
unlam-uniq : ∀ (y : (σ ⇒ τ) ⊣ Γ) → unlamʳ y ≡ unlamˡ y
unlam-uniq = BiInvEquiv.invr≡invl lam-biinvequiv

-- ...and therefore our ap's are indistinguishable!
ap-uniq : ∀ (y : (σ ⇒ τ) ⊣ Γ) (z : σ ⊣ Γ) → apˡ y z ≡ apʳ y z
ap-uniq y z = apˡ-unlamʳ y z ∙ cong (sub ⟨ z ⟩) (unlam-uniq y) ∙ sym (apʳ-unlamˡ y z)

-- We can also derive substitution rules for unlam and ap:

unlam-sub : (f : Γ ~> Δ) (y : (σ ⇒ τ) ⊣ Γ)
            → sub (↑ f) (unlamʳ y) ≡ unlamˡ (sub f y)
unlam-sub {σ} f y =
               sub (↑ f) (unlamʳ y)    ≡⟨ sym (unlam-βˡ _) ⟩
  unlamˡ (lam (sub (↑ f) (unlamʳ y)))  ≡⟨ cong unlamˡ (sym (sub-lam f (unlamʳ y))) ⟩
  unlamˡ (sub f (lam (unlamʳ y))    )  ≡⟨ cong (unlamˡ ∘ sub f) (unlam-ηʳ y) ⟩
  unlamˡ (sub f y                   )  ∎

ap-sub : (f : Γ ~> Δ) (y : (σ ⇒ τ) ⊣ Γ) (z : σ ⊣ Γ)
         → sub f (apˡ y z) ≡ apʳ (sub f y) (sub f z)
ap-sub f y z =
  sub f (apˡ y z)                         ≡⟨ cong (sub f) (apˡ-unlamʳ y z) ⟩
  sub f (sub ⟨ z ⟩ (unlamʳ y))             ≡⟨ sym (sub-∘* f ⟨ z ⟩ (unlamʳ y)) ⟩
  sub (f ∘* ⟨ z ⟩) (unlamʳ y)              ≡⟨ cong (λ x → sub x (unlamʳ y)) (∘*-,* f id* z) ⟩
  sub ((f ∘* id*) ,* sub f z) (unlamʳ y)  ≡⟨ cong (λ x → sub (x ,* sub f z) (unlamʳ y)) (id*-r f) ⟩
  sub (f ,* sub f z) (unlamʳ y)           ≡⟨ cong (λ x → sub x (unlamʳ y)) (sym (⟨⟩-↑ (sub f z) f)) ⟩
  sub (⟨ sub f z ⟩ ∘* (↑ f)) (unlamʳ y)    ≡⟨ sub-∘* (id* ,* (sub f z)) (↑ f) (unlamʳ y) ⟩
  sub ⟨ sub f z ⟩ (sub (↑ f) (unlamʳ y))   ≡⟨ cong (sub (id* ,* (sub f z))) (unlam-sub f y) ⟩
  sub ⟨ sub f z ⟩ (unlamˡ (sub f y))       ≡⟨ sym (apʳ-unlamˡ (sub f y) (sub f z)) ⟩
  apʳ (sub f y) (sub f z)                 ∎


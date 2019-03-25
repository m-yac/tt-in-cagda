
{-# OPTIONS --cubical --safe #-}
module Foundations.BiinvertibleEquiv where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Function
open import Cubical.Foundations.PathSplitEquiv
  using (isEquivPreComp; isEquivPostComp; preCompEquiv; postCompEquiv)

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

const : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A → B → A
const x _ = x


record BiinvEquiv {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  constructor biiequiv
  field
    fun : A → B
    invr : B → A
    invr-rightInv : section fun invr
    invl : B → A
    invl-leftInv : retract fun invl


  invr-filler : ∀ z {w} (p : invl z ≡ w) → I → I → A
  invr-filler z p j i = hfill (λ j → λ { (i = i0) → invl-leftInv (invr z) j
                                       ; (i = i1) → p j })
                              (inS (invl (invr-rightInv z i))) j

  invr≡invl : ∀ z → invr z ≡ invl z
  invr≡invl z i = invr-filler z refl i1 i

  invr-leftInv : retract fun invr
  invr-leftInv z i = invr-filler (fun z) (invl-leftInv z) i1 i

  invl-rightInv : section fun invl
  invl-rightInv = subst (section fun) (funExt invr≡invl) invr-rightInv


  invl-rightInv' : section fun invl
  invl-rightInv' z i = hcomp (λ j → λ { (i = i0) → fun (invl (invr-rightInv z j))
                                      ; (i = i1) → invr-rightInv z j })
                             (fun (invl-leftInv (invr z) i))


module _ {ℓ} {A B : Set ℓ} (e : BiinvEquiv A B) where
  open BiinvEquiv e

  biiequivToIso : Iso A B
  biiequivToIso = record { fun = fun ; inv = invr ; rightInv = invr-rightInv ; leftInv = invr-leftInv }

  biiequivToIsEquiv : isEquiv fun
  biiequivToIsEquiv = isoToIsEquiv biiequivToIso

  biiEquivToEquiv : A ≃ B
  biiEquivToEquiv = fun , biiequivToIsEquiv



-- module IsoInvl {ℓ} {A B : Set ℓ} (e : BiinvEquiv A B) where
--   open BiinvEquiv e renaming ( fun to f )

--   biiequivToIso : Iso A B
--   biiequivToIso = record { fun = f ; inv = invl ; rightInv = invl-rightInv ; leftInv = invl-leftInv }

--   biiequivToIsEquiv : isEquiv f
--   biiequivToIsEquiv = isoToIsEquiv biiequivToIso

--   biiEquivToEquiv : A ≃ B
--   biiEquivToEquiv = f , biiequivToIsEquiv


  -- This is the way the HoTT book does it...
  -- invr≡invl : invr ≡ invl
  -- invr≡invl = cong fst (isContr→isProp (equiv-proof (isEquivPostComp biiEquivToEquiv) id)
  --                                      (invr , funExt invr-rightInv) (invl , funExt invl-rightInv))

  -- This is the way the HoTT book does it...
  -- invl≡invr : invl ≡ invr
  -- invl≡invr = cong fst (isContr→isProp (equiv-proof (isEquivPreComp biiEquivToEquiv) id)
  --                                      (invl , funExt invl-leftInv) (invr , funExt invr-leftInv))

  -- invr-leftInv : retract fun invr
  -- invr-leftInv z i = hcomp (λ j → λ { (i = i0) → invl-leftInv (invr (fun z)) j
  --                                   ; (i = i1) → invl-leftInv z j })
  --                          (invl (invr-rightInv (fun z) i))

  --                                 we want: invr (fun z) ≡ z
  -- (λ i → invl (invr-rightInv (fun z) i)) : invl (fun (invr (fun z))) ≡ invl (fun z)  (base)
  -- invl-leftInv (invr (fun z))            : invl (fun (invr (fun z))) ≡ invr (fun z)  (i0 side)
  -- invl-leftInv z                         : invl (fun z) ≡ z                          (i1 side)

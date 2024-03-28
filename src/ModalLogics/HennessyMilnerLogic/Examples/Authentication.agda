{-# OPTIONS --without-K --safe #-}
module ModalLogics.HennessyMilnerLogic.Examples.Authentication where

open import Common.Program using (Program)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Container using (Container)
open import Data.Container.FreeMonad using (_⋆_; _>>=_)
open import Data.Empty using () renaming (⊥ to ⊥₀; ⊥-elim to ⊥-elim₀)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_,_)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Function using (const; case_of_)
open import Level using (0ℓ)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_!_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no; ofʸ; ofⁿ)

open Bool
open Container
open _⋆_
open ℕ
open Formula
open _≡_

data EffectOperations : Set where
  login : ℕ → EffectOperations
  logout : EffectOperations
  exception : EffectOperations

effect : Container 0ℓ 0ℓ
Shape effect = EffectOperations
Position effect (login _) = Bool
Position effect logout = ⊤₀
Position effect exception = ⊥₀

instance
  effect-decEq : IsDecEquivalence {A = Shape effect} _≡_
  effect-decEq = isDecEquivalence λ { (login n₁) (login n₂) → case n₁ ≟ n₂ of λ { (no h) → record { does = false ; proof = ofⁿ λ { refl → h refl } }
                                                                                ; (yes refl) → record { does = true ; proof = ofʸ refl } }
                                    ; (login _) logout → record { does = false ; proof = ofⁿ λ () }
                                    ; (login _) exception → record { does = false ; proof = ofⁿ λ () }
                                    ; logout (login _) → record { does = false ; proof = ofⁿ λ () }
                                    ; logout logout → record { does = true ; proof = ofʸ refl }
                                    ; logout exception → record { does = false ; proof = ofⁿ λ () }
                                    ; exception (login _) → record { does = false ; proof = ofⁿ λ () }
                                    ; exception logout → record { does = false ; proof = ofⁿ λ () }
                                    ; exception exception → record { does = true ; proof = ofʸ refl } }

testProgram : Program effect ℕ (const ⊤₀)
testProgram n = do
  b ← impure (login n , pure)
  ( if b
    then impure (logout , pure)
    else impure (exception , ⊥-elim₀) )

property₁ : Formula effect
property₁ = [ logout ] false

test₁ : property₁ ⊩ testProgram ! 0
test₁ = tt

property₂ : Formula effect
property₂ = ⟨ login 0 ⟩ ⟨ logout ⟩ true

test₂ : property₂ ⊩ testProgram ! 0
test₂ = true , tt₀ , tt

property₃ : Formula effect
property₃ = ⟨ login 0 ⟩ [ login 0 ] true

test₃ : property₃ ⊩ testProgram ! 0
test₃ = false , tt

property₄ : Formula effect
property₄ = ⟨ login 0 ⟩ [ logout ] false

test₄ : property₄ ⊩ testProgram ! 0
test₄ = false , tt

property₅ : Formula effect
property₅ = [ login 0 ] [ exception ] false

test₅ : property₅ ⊩ testProgram ! 0
test₅ false = ⊥-elim₀
test₅ true = tt

property₆ : Formula effect
property₆ = [ login 0 ] [ exception ] true

test₆ : property₆ ⊩ testProgram ! 0
test₆ false = ⊥-elim₀
test₆ true = tt

property₇ : ℕ → Formula effect
property₇ n = [ login n ] false

test₇ : ∀ (n : ℕ) → n ≢ 0 → property₇ n ⊩ testProgram ! 0
test₇ zero h = ⊥-elim₀ (h refl)
test₇ (suc _) h = tt

property₈ : Shape effect → Formula effect
property₈ c = ⟨ login 0 ⟩ ([ c ] true ∧ [ c ] false)

test₈ : ∀ c → property₈ c ⊩ testProgram ! 0
test₈ (login x) = false , tt , tt
test₈ logout = false , tt , tt
test₈ exception = false , ⊥-elim₀ , ⊥-elim₀

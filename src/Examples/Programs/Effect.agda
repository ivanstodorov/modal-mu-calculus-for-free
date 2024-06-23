{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.Programs.Effect where

open import Common.Injectable using (_:<:_)
open import Common.Program using (Program; ⦗_⦘; pure; impure)
open import Data.Bool using (Bool)
open import Data.Container using (Container)
open import Data.Container.Combinator using (_⊎_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Level using (Level; 0ℓ)

open _:<:_
open Container

private variable
  ℓ₁ ℓ₂ ℓ₃ : Level

data EffectShape : Set where
  getPIN : EffectShape
  verifyPIN : ℕ → EffectShape
  showBalance : EffectShape
  throwException : EffectShape

effect : Container 0ℓ 0ℓ
Shape effect = EffectShape
Position effect getPIN = ℕ
Position effect (verifyPIN _) = Bool
Position effect showBalance = ⊤
Position effect throwException = ⊥

data IOShape : Set where
  getPIN : IOShape
  showBalance : IOShape

IOEffect : Container 0ℓ 0ℓ
Shape IOEffect = IOShape
Position IOEffect getPIN = ℕ
Position IOEffect showBalance = ⊤

getPINˢ : (C : Container ℓ₁ ℓ₂) → ⦃ IOEffect :<: C ⦄ → Shape C
getPINˢ _ ⦃ inst ⦄ = injS inst getPIN

showBalanceˢ : (C : Container ℓ₁ ℓ₂) → ⦃ IOEffect :<: C ⦄ → Shape C
showBalanceˢ _ ⦃ inst ⦄ = injS inst showBalance

data VerificationShape : Set where
  verifyPIN : ℕ → VerificationShape

verificationEffect : Container 0ℓ 0ℓ
Shape verificationEffect = VerificationShape
Position verificationEffect (verifyPIN _) = Bool

verifyPINˢ : (C : Container ℓ₁ ℓ₂) → ⦃ verificationEffect :<: C ⦄ → ℕ → Shape C
verifyPINˢ _ ⦃ inst ⦄ = injS inst ∘ verifyPIN

data ExceptionShape : Set where
  throwException : ExceptionShape

exceptionEffect : Container 0ℓ 0ℓ
Shape exceptionEffect = ExceptionShape
Position exceptionEffect _ = ⊥

throwExceptionˢ : (C : Container ℓ₁ ℓ₂) → ⦃ exceptionEffect :<: C ⦄ → Shape C
throwExceptionˢ _ ⦃ inst ⦄ = injS inst throwException

effect⁺ : Container 0ℓ 0ℓ
effect⁺ = IOEffect ⊎ verificationEffect ⊎ exceptionEffect

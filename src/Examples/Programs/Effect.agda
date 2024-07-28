{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.Programs.Effect where

open import Data.Bool using (Bool)
open import Data.Container using (Container)
open import Data.Container.Combinator using (_⊎_)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Level using (0ℓ)

open Container

data EffectShape : Set where
  getPIN : EffectShape
  correctPIN : ℕ → EffectShape
  showBalance : EffectShape
  throwException : EffectShape

effect : Container 0ℓ 0ℓ
Shape effect = EffectShape
Position effect getPIN = ℕ
Position effect (correctPIN _) = Bool
Position effect showBalance = ⊤
Position effect throwException = ⊥

data IOShape : Set where
  getPIN : IOShape
  showBalance : IOShape

IOEffect : Container 0ℓ 0ℓ
Shape IOEffect = IOShape
Position IOEffect getPIN = ℕ
Position IOEffect showBalance = ⊤

data VerificationShape : Set where
  correctPIN : ℕ → VerificationShape

verificationEffect : Container 0ℓ 0ℓ
Shape verificationEffect = VerificationShape
Position verificationEffect (correctPIN _) = Bool

data ExceptionShape : Set where
  throwException : ExceptionShape

exceptionEffect : Container 0ℓ 0ℓ
Shape exceptionEffect = ExceptionShape
Position exceptionEffect _ = ⊥

effect⁺ : Container 0ℓ 0ℓ
effect⁺ = IOEffect ⊎ verificationEffect ⊎ exceptionEffect

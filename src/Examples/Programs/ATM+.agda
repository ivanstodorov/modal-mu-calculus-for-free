{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.Programs.ATM+ where

open import Common.Program using (Program; free; impure; ⦗_⦘)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect⁺; IOShape; VerificationShape; ExceptionShape)

open IOShape
open VerificationShape
open ExceptionShape

ATM⁺ : Program effect⁺ ⊤
free ATM⁺ = impure (inj₁ getPIN , λ where
  n → ⦗ impure (inj₂ (inj₁ (correctPIN n)) , λ where
    false → ⦗ impure (inj₂ (inj₂ throwException) , ⊥-elim) ⦘
    true → ⦗ impure (inj₁ showBalance , λ _ → ATM⁺) ⦘) ⦘)

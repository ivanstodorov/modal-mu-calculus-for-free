{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.Programs.ATMs where

open import Common.Injectable using (inj)
open import Common.Program using (Program; free; impure; ⦗_⦘)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect⁺; IOShape; VerificationShape; ExceptionShape)

open IOShape
open VerificationShape
open ExceptionShape

ATMˢ : Program effect⁺ ⊤
free ATMˢ = impure (inj getPIN effect⁺ , λ where
  n → ⦗ impure (inj (correctPIN n) effect⁺ , λ where
    false → ⦗ impure (inj throwException effect⁺ , ⊥-elim) ⦘
    true → ⦗ impure (inj showBalance effect⁺ , λ _ → ATMˢ) ⦘) ⦘)

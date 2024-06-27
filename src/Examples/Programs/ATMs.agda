{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.Programs.ATMs where

open import Common.Injectable using ()
open import Common.Program using (Program; free; impure; ⦗_⦘)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect⁺; getPINˢ; correctPINˢ; showBalanceˢ; throwExceptionˢ)

ATMˢ : Program effect⁺ ⊤
free ATMˢ = impure (getPINˢ effect⁺ , λ where
  n → ⦗ impure (correctPINˢ effect⁺ n , λ where
    true → ⦗ impure (showBalanceˢ effect⁺ , λ _ → ATMˢ) ⦘
    false → ⦗ impure (throwExceptionˢ effect⁺ , ⊥-elim) ⦘) ⦘)

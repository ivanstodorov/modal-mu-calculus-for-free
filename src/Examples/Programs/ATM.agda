{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.Programs.ATM where

open import Common.Program using (Program; free; impure; ⦗_⦘)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect; EffectShape)

open EffectShape

ATM : Program effect ⊤
free ATM = impure (getPIN , λ where
  n → ⦗ impure (correctPIN n , λ where
    false → ⦗ impure (throwException , ⊥-elim) ⦘
    true → ⦗ impure (showBalance , λ _ → ATM) ⦘) ⦘)

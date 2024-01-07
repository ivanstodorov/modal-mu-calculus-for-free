{-# OPTIONS --overlapping-instances #-}
module ModalLogics.HennessyMilnerLogic.Examples.Fusc where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (const)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to refl')
open import Relation.Binary.PropositionalEquality.Properties using (isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)

open Effect
open IsDecEquivalence ⦃...⦄

emptyEffect : Effect 0ℓ 0ℓ
C emptyEffect = ⊥
R emptyEffect ()

instance
  emptyEffectEqIsDecEq : IsDecEquivalence {A = C emptyEffect} _≡_
  emptyEffectEqIsDecEq = isDecEquivalence emptyEffectEqDec
    where
    emptyEffectEqDec : Decidable {A = C emptyEffect} _≡_
    emptyEffectEqDec ()

fusc : recursiveProgram emptyEffect ℕ (const ℕ)
fusc zero = pure zero
fusc (suc n) = do
  fn ← callF n
  ffn ← callF fn
  pure (suc ffn)

test : (recursionHandler fusc 3) 3 ≡ pure (just 3)
test = refl'

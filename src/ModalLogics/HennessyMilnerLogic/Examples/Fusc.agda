{-# OPTIONS --without-K --overlapping-instances #-}
module ModalLogics.HennessyMilnerLogic.Examples.Fusc where

open import Common.Container using (_:<:_)
open import Common.Program using (RecursiveProgram; callF; recursionHandler)
open import Data.Container using (Container)
open import Data.Container.FreeMonad using (pure; _>>=_)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Function using (const)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)

open Container
open ℕ
open _≡_
open IsDecEquivalence ⦃...⦄ hiding (refl)

emptyEffect : Container 0ℓ 0ℓ
Shape emptyEffect = ⊥
Position emptyEffect ()

instance
  emptyEffectEqIsDecEq : IsDecEquivalence {A = Shape emptyEffect} _≡_
  emptyEffectEqIsDecEq = isDecEquivalence emptyEffectEqDec
    where
    emptyEffectEqDec : Decidable {A = Shape emptyEffect} _≡_
    emptyEffectEqDec ()

fusc : RecursiveProgram emptyEffect ℕ (const ℕ)
fusc zero = pure zero
fusc (suc n) = do
  fn ← callF n
  ffn ← callF fn
  pure (suc ffn)

test : (recursionHandler fusc 3) 3 ≡ pure (just 3)
test = refl

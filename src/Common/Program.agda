{-# OPTIONS --without-K --safe #-}
module Common.Program where

open import Common.Container using (_:<:_)
open import Data.Container using (Container)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; _>>=_)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; maybe)
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level; _⊔_)

open _:<:_
open Container
open _⋆_
open Maybe
open ℕ

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

Program : Container ℓ₁ ℓ₂ → (I : Set ℓ₃) → (I → Set ℓ₄) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
Program C I O = (i : I) → C ⋆ O i

data RecursionOperations (I : Set ℓ) : Set ℓ where
  call : I → RecursionOperations I

recursionEffect : (I : Set ℓ₁) → (I → Set ℓ₂) → Container ℓ₁ ℓ₂
Shape (recursionEffect I _) = RecursionOperations I
Position (recursionEffect _ O) (call i) = O i

callS : {C : Container ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ⦃ recursionEffect I O :<: C ⦄ → I → Shape C
callS ⦃ inst ⦄ = (injS inst) ∘ call

callF : {C : Container ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ⦃ recursionEffect I O :<: C ⦄ → (i : I) → C ⋆ (O i)
callF ⦃ inst ⦄ i = impure (callS i , pure ∘ projP inst)

RecursiveProgram : Container ℓ₁ ℓ₂ → (I : Set ℓ₃) → (I → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
RecursiveProgram C I O = (i : I) → (recursionEffect I O ⊎ C) ⋆ O i

recursionHandler : {C : Container ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₂} → RecursiveProgram C I O → ℕ → Program C I (Maybe ∘ O)
recursionHandler x n i = recursionHandler' x n (x i)
  where
  recursionHandler' : {C : Container ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₂} → {α : Set ℓ₄} → RecursiveProgram C I O → ℕ → (recursionEffect I O ⊎ C) ⋆ α → C ⋆ Maybe α
  recursionHandler' _ _ (pure a) = pure (just a)
  recursionHandler' _ zero (impure (inj₁ _ , _)) = pure nothing
  recursionHandler' f (suc n) (impure (inj₁ (call i) , c)) = recursionHandler' f n (f i) >>= maybe (recursionHandler' f (suc n) ∘ c) (pure nothing)
  recursionHandler' f n (impure (inj₂ s , c)) = impure (s , recursionHandler' f n ∘ c)

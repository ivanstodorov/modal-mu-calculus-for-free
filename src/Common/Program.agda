{-# OPTIONS --overlapping-instances #-}
module Common.Program where

open import Common.Effect
open import Common.Free
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level; lift)

open Effect
open _:<:_

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

program : Effect ℓ₁ ℓ₂ → (I : Set ℓ₃) → (I → Set ℓ₄) → Set _
program ε I O = (i : I) → Free ε (O i)

data RecursionOperations (I : Set ℓ) : Set ℓ where
  call : I → RecursionOperations I

recursionEffect : (I : Set ℓ₁) → (I → Set ℓ₂) → Effect ℓ₁ ℓ₂
C (recursionEffect I _) = RecursionOperations I
R (recursionEffect _ O) (call i) = O i

callC : {ε : Effect ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ⦃ recursionEffect I O :<: ε ⦄ → I → C ε
callC ⦃ inst ⦄ = (injC inst) ∘ call

callF : {ε : Effect ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ⦃ recursionEffect I O :<: ε ⦄ → (i : I) → Free ε (O i)
callF ⦃ inst ⦄ i = step (callC i) (pure ∘ projR inst)

recursiveProgram : Effect ℓ₁ ℓ₂ → (I : Set ℓ₃) → (I → Set ℓ₄) → Set _
recursiveProgram ε I O = (i : I) → Free (recursionEffect I O :+: ε) (O i)

recursionHandler : {ε : Effect ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → recursiveProgram ε I O → ℕ → program ε I (Maybe ∘ O)
recursionHandler x n i = recursionHandler' x n (x i)
  where
    recursionHandler' : {ε : Effect ℓ₁ ℓ₂} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → {α : Set ℓ₅} → recursiveProgram ε I O → ℕ → Free (recursionEffect I O :+: ε) α → Free ε (Maybe α)
    recursionHandler' _ _ (pure a) = pure (just a)
    recursionHandler' _ zero (step (inj₁ _) _) = pure nothing
    recursionHandler' f (suc n) (step (inj₁ (call i)) k) = recursionHandler' f n (f i) >>= maybe (recursionHandler' f (suc n) ∘ k ∘ lift) (pure nothing)
    recursionHandler' {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} f n (step (inj₂ c) k) = step c (recursionHandler' f n ∘ k ∘ lift)

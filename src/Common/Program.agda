module Common.Program where

open import Common.Effect
open import Common.Free
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_∘_)

program : Effect → (I : Set) → (I → Set) → Set
program ε I O = (i : I) → Free ε (O i)

data RecursionOperations (I : Set) : Set where
  call : I → RecursionOperations I

recursionEffect : (I : Set) → (I → Set) → Effect
Effect.C (recursionEffect I _) = RecursionOperations I
Effect.R (recursionEffect _ O) (call i) = O i

recursiveProgram : Effect → (I : Set) → (I → Set) → Set
recursiveProgram ε I O = (i : I) → Free (recursionEffect I O :+: ε) (O i)

recursionHandler : {ε : Effect} → {I : Set} → {O : I → Set} → recursiveProgram ε I O → ℕ → program ε I (Maybe ∘ O)
recursionHandler x n i = recursionHandler' x n (x i)
  where
    recursionHandler' : {ε : Effect} → {I : Set} → {O : I → Set} → {α : Set} → recursiveProgram ε I O → ℕ → Free (recursionEffect I O :+: ε) α → Free ε (Maybe α)
    recursionHandler' _ _ (pure a) = pure (just a)
    recursionHandler' _ zero (step (inj₁ _) _) = pure nothing
    recursionHandler' f (suc n) (step (inj₁ (call i)) k) = recursionHandler' f n (f i) >>= maybe (recursionHandler' f (suc n) ∘ k) (pure nothing)
    recursionHandler' f n (step (inj₂ c) k) = step c (recursionHandler' f n ∘ k)

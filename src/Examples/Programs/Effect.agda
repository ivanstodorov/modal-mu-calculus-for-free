{-# OPTIONS --without-K --safe #-}
module Examples.Programs.Effect where

open import Common.Injectable using (_:<:_)
open import Data.Bool using (Bool)
open import Data.Container using (Container)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty using () renaming (⊥ to ⊥₀; ⊥-elim to ⊥₀-elim)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Function using (case_of_; _∘_)
open import Level using (Level; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no; ofʸ; ofⁿ)

open _:<:_
open Bool
open Container
open _⋆_
open _≡_
open IsDecEquivalence ⦃...⦄ hiding (refl)

private variable
  ℓ₁ ℓ₂ ℓ₃ : Level

data AuthOperations : Set where
  login : ℕ → AuthOperations
  logout : AuthOperations

authEffect : Container 0ℓ 0ℓ
Shape authEffect = AuthOperations
Position authEffect (login _) = Bool
Position authEffect logout = ⊤₀

instance
  authEffect-decEq : IsDecEquivalence {A = Shape authEffect} _≡_
  authEffect-decEq = isDecEquivalence λ { (login n₁) (login n₂) → case n₁ ≟ⁿ n₂ of λ { (no h) → record { does = false ; proof = ofⁿ λ { refl → h refl } }
                                                                                    ; (yes refl) → record { does = true ; proof = ofʸ refl } }
                                        ; (login _) logout → record { does = false ; proof = ofⁿ λ () }
                                        ; logout (login _) → record { does = false ; proof = ofⁿ λ () }
                                        ; logout logout → record { does = true ; proof = ofʸ refl } }

loginS : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → ℕ → Shape C
loginS _ ⦃ inst ⦄ = injS inst ∘ login

loginF : {C : Container ℓ₁ ℓ₂} → ⦃ authEffect :<: C ⦄ → ℕ → C ⋆ Bool
loginF {C = C} ⦃ inst ⦄ n = impure (loginS C n , pure ∘ projP inst)

logoutS : (C : Container ℓ₁ ℓ₂) → ⦃ authEffect :<: C ⦄ → Shape C
logoutS _ ⦃ inst ⦄ = injS inst logout

logoutF : {C : Container ℓ₁ ℓ₂} → ⦃ authEffect :<: C ⦄ → C ⋆ ⊤₀
logoutF {C = C} ⦃ inst ⦄ = impure (logoutS C , pure ∘ projP inst)

exceptionEffect : Container 0ℓ 0ℓ
Shape exceptionEffect = ⊤₀
Position exceptionEffect _ = ⊥₀

instance
  exceptionEffect-decEq : IsDecEquivalence {A = Shape exceptionEffect} _≡_
  exceptionEffect-decEq = isDecEquivalence λ { tt₀ tt₀ → record { does = true ; proof = ofʸ refl } }

exceptionS : (C : Container ℓ₁ ℓ₂) → ⦃ exceptionEffect :<: C ⦄ → Shape C
exceptionS _ ⦃ inst ⦄ = injS inst tt₀

exceptionF : {C : Container ℓ₁ ℓ₂} → ⦃ exceptionEffect :<: C ⦄ → {α : Set ℓ₃} → C ⋆ α
exceptionF {C = C} ⦃ inst ⦄ = impure (exceptionS C , ⊥₀-elim ∘ projP inst)

effect : Container 0ℓ 0ℓ
effect = authEffect ⊎ exceptionEffect

instance
  effect-decEq : IsDecEquivalence {A = Shape effect} _≡_
  effect-decEq = isDecEquivalence λ { (inj₁ x) (inj₁ y) → case x ≟ y of λ { (no h) → record { does = false ; proof = ofⁿ λ { refl → h refl } }
                                                                          ; (yes refl) → record { does = true ; proof = ofʸ refl } }
                                    ; (inj₁ _) (inj₂ _) → record { does = false ; proof = ofⁿ λ () }
                                    ; (inj₂ _) (inj₁ _) → record { does = false ; proof = ofⁿ λ () }
                                    ; (inj₂ x) (inj₂ y) → case x ≟ y of λ { (no h) → record { does = false ; proof = ofⁿ λ { refl → h refl } }
                                                                          ; (yes refl) → record { does = true ; proof = ofʸ refl } } }

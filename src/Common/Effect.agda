module Common.Effect where

open import Data.Bool using (false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Level using (Level; suc; _⊔_; Lift; lift)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to refl')
open import Relation.Binary.PropositionalEquality.Properties using (isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (does; proof; yes; no; ofʸ; ofⁿ; _because_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

record Effect (ℓ₁ : Level) (ℓ₂ : Level) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    C : Set ℓ₁
    R : C → Set ℓ₂

open Effect

_:+:_ : Effect ℓ₁ ℓ₂ → Effect ℓ₃ ℓ₄ → Effect (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄)
C (ε₁ :+: ε₂) = C ε₁ ⊎ C ε₂
R (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} ε₁ ε₂) (inj₁ c) = Lift (ℓ₂ ⊔ ℓ₄) (R ε₁ c)
R (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} ε₁ ε₂) (inj₂ c) = Lift (ℓ₂ ⊔ ℓ₄) (R ε₂ c)

infixr 20 _:+:_

open IsDecEquivalence ⦃...⦄

instance
  effectSumEqIsDecEq : {ε₁ : Effect ℓ₁ ℓ₂} → {ε₂ : Effect ℓ₃ ℓ₄} → ⦃ IsDecEquivalence {A = C ε₁} _≡_ ⦄ → ⦃ IsDecEquivalence {A = C ε₂} _≡_ ⦄ → IsDecEquivalence {A = C (ε₁ :+: ε₂)} _≡_
  effectSumEqIsDecEq {ε₁ = ε₁} {ε₂ = ε₂} = isDecEquivalence effectSumEqDec
    where
    effectSumEqDec : Decidable {A = C (ε₁ :+: ε₂)} _≡_
    does (effectSumEqDec (inj₁ c₁) (inj₁ c₂)) with c₁ ≟ c₂
    ... | does₁ because _ = does₁
    does (effectSumEqDec (inj₁ _) (inj₂ _)) = false
    does (effectSumEqDec (inj₂ _) (inj₁ _)) = false
    does (effectSumEqDec (inj₂ c₁) (inj₂ c₂)) with c₁ ≟ c₂
    ... | does₁ because _ = does₁
    proof (effectSumEqDec (inj₁ c₁) (inj₁ c₂)) with c₁ ≟ c₂
    ... | _ because ofʸ refl' = ofʸ refl'
    ... | _ because ofⁿ ¬p = ofⁿ λ {refl' → ¬p refl'}
    proof (effectSumEqDec (inj₁ _) (inj₂ _)) = ofⁿ λ ()
    proof (effectSumEqDec (inj₂ _) (inj₁ _)) = ofⁿ λ ()
    proof (effectSumEqDec (inj₂ c₁) (inj₂ c₂)) with c₁ ≟ c₂
    ... | _ because ofʸ refl' = ofʸ refl'
    ... | _ because ofⁿ ¬p = ofⁿ λ {refl' → ¬p refl'}

record _:<:_ (ε₁ : Effect ℓ₁ ℓ₂) (ε₂ : Effect ℓ₃ ℓ₄) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    injC : C ε₁ → C ε₂
    projR : {c : C ε₁} → R ε₂ (injC c) → R ε₁ c

open _:<:_
open _:<:_ ⦃...⦄

instance
  ε:<:ε : {ε : Effect ℓ₁ ℓ₂} → ε :<: ε
  injC ⦃ ε:<:ε ⦄ = id
  projR ⦃ ε:<:ε ⦄ = id

  ε₁:<:|ε₁:+:ε₂| : {ε₁ : Effect ℓ₁ ℓ₂} → {ε₂ : Effect ℓ₃ ℓ₄} → ε₁ :<: (ε₁ :+: ε₂)
  injC ⦃ ε₁:<:|ε₁:+:ε₂| ⦄ = inj₁
  projR ⦃ ε₁:<:|ε₁:+:ε₂| ⦄ (lift r) = r

  ε₁:<:ε₂→ε₁:<:|ε₃:+:ε₂| : {ε₁ : Effect ℓ₁ ℓ₂} → {ε₂ : Effect ℓ₃ ℓ₄} → {ε₃ : Effect ℓ₅ ℓ₆} → ⦃ ε₁ :<: ε₂ ⦄ → ε₁ :<: (ε₃ :+: ε₂)
  injC ⦃ ε₁:<:ε₂→ε₁:<:|ε₃:+:ε₂| ⦃ inst ⦄ ⦄ = inj₂ ∘ injC inst
  projR ⦃ ε₁:<:ε₂→ε₁:<:|ε₃:+:ε₂| ⦃ inst ⦄ ⦄ (lift r) = projR inst r

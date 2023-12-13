module Common.Effect where

open import Data.Bool using (false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Level using (Level; suc; _⊔_; Lift; lift)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (does; proof; yes; no; ofʸ; ofⁿ; _because_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

record Effect : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    C : Set ℓ₁
    R : C → Set ℓ₂

open Effect

_:+:_ : Effect {ℓ₁} {ℓ₂} → Effect {ℓ₃} {ℓ₄} → Effect {ℓ₁ ⊔ ℓ₃} {ℓ₂ ⊔ ℓ₄}
C (ε₁ :+: ε₂) = C ε₁ ⊎ C ε₂
R (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} ε₁ ε₂) (inj₁ c) = Lift (ℓ₂ ⊔ ℓ₄) (R ε₁ c)
R (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} ε₁ ε₂) (inj₂ c) = Lift (ℓ₂ ⊔ ℓ₄) (R ε₂ c)

infixr 20 _:+:_

record Eq (α : Set ℓ) : Set ℓ where
  field
    _==_ : DecidableEquality α

open Eq ⦃...⦄

instance
  effectSumEq : {ε₁ : Effect {ℓ₁} {ℓ₂}} → {ε₂ : Effect {ℓ₃} {ℓ₄}} → ⦃ Eq (C ε₁) ⦄ → ⦃ Eq (C ε₂) ⦄ → Eq (C (ε₁ :+: ε₂))
  does (_==_ ⦃ effectSumEq ⦄ (inj₁ c₁) (inj₁ c₂)) with c₁ == c₂
  ... | eq because _ = eq
  proof (_==_ ⦃ effectSumEq ⦄ (inj₁ c₁) (inj₁ c₂)) with c₁ == c₂
  ... | no ¬p = ofⁿ λ {refl → ¬p refl}
  ... | yes refl = ofʸ refl
  does (_==_ ⦃ effectSumEq ⦄ (inj₁ _) (inj₂ _)) = false
  proof (_==_ ⦃ effectSumEq ⦄ (inj₁ _) (inj₂ _)) = ofⁿ λ ()
  does (_==_ ⦃ effectSumEq ⦄ (inj₂ _) (inj₁ _)) = false
  proof (_==_ ⦃ effectSumEq ⦄ (inj₂ _) (inj₁ _)) = ofⁿ λ ()
  does (_==_ ⦃ effectSumEq ⦄ (inj₂ c₁) (inj₂ c₂)) with c₁ == c₂
  ... | eq because _ = eq
  proof (_==_ ⦃ effectSumEq ⦄ (inj₂ c₁) (inj₂ c₂)) with c₁ == c₂
  ... | no ¬p = ofⁿ λ {refl → ¬p refl}
  ... | yes refl = ofʸ refl

record _:<:_ (ε₁ : Effect {ℓ₁} {ℓ₂}) (ε₂ : Effect {ℓ₃} {ℓ₄}) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    injC : C ε₁ → C ε₂
    projR : {c : C ε₁} → R ε₂ (injC c) → R ε₁ c

open _:<:_
open _:<:_ ⦃...⦄

instance
  ε:<:ε : {ε : Effect {ℓ₁} {ℓ₂}} → ε :<: ε
  injC ⦃ ε:<:ε ⦄ = id
  projR ⦃ ε:<:ε ⦄ = id

  ε₁:<:|ε₁:+:ε₂| : {ε₁ : Effect {ℓ₁} {ℓ₂}} → {ε₂ : Effect {ℓ₃} {ℓ₄}} → ε₁ :<: (ε₁ :+: ε₂)
  injC ⦃ ε₁:<:|ε₁:+:ε₂| ⦄ = inj₁
  projR ⦃ ε₁:<:|ε₁:+:ε₂| ⦄ (lift r) = r

  ε₁:<:ε₂→ε₁:<:|ε₃:+:ε₂| : {ε₁ : Effect {ℓ₁} {ℓ₂}} → {ε₂ : Effect {ℓ₃} {ℓ₄}} → {ε₃ : Effect {ℓ₅} {ℓ₆}} → ⦃ ε₁ :<: ε₂ ⦄ → ε₁ :<: (ε₃ :+: ε₂)
  injC ⦃ ε₁:<:ε₂→ε₁:<:|ε₃:+:ε₂| ⦃ inst ⦄ ⦄ = inj₂ ∘ injC inst
  projR ⦃ ε₁:<:ε₂→ε₁:<:|ε₃:+:ε₂| ⦃ inst ⦄ ⦄ (lift r) = projR inst r

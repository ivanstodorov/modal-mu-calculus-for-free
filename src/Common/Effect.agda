module Common.Effect where

open import Data.Bool using (false)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Level using (Level; suc; _⊔_; Lift)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (does; proof; yes; no; ofʸ; ofⁿ; _because_)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record Effect : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    C : Set ℓ₁
    R : C → Set ℓ₂

open Effect

emptyEffect : Effect {ℓ₁} {ℓ₂}
C emptyEffect = ⊥
R emptyEffect c = ⊥-elim c

record Eq (α : Set ℓ) : Set ℓ where
  field
    _==_ : DecidableEquality α

open Eq ⦃...⦄

instance
  emptyEffectEq : Eq (Effect.C (emptyEffect {ℓ₁} {ℓ₂}))
  _==_ ⦃ emptyEffectEq ⦄ ()

_:+:_ : Effect {ℓ₁} {ℓ₂} → Effect {ℓ₃} {ℓ₄} → Effect {ℓ₁ ⊔ ℓ₃} {ℓ₂ ⊔ ℓ₄}
C (ε₁ :+: ε₂) = C ε₁ ⊎ C ε₂
R (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} ε₁ ε₂) (inj₁ c) = Lift (ℓ₂ ⊔ ℓ₄) (R ε₁ c)
R (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} ε₁ ε₂) (inj₂ c) = Lift (ℓ₂ ⊔ ℓ₄) (R ε₂ c)

instance
  effectSumEq : {ε₁ : Effect {ℓ₁} {ℓ₂}} → {ε₂ : Effect {ℓ₃} {ℓ₄}} → ⦃ Eq (Effect.C ε₁) ⦄ → ⦃ Eq (Effect.C ε₂) ⦄ → Eq (Effect.C (ε₁ :+: ε₂))
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

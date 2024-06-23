{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.HennessyMilnerLogic.Properties where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program; free; pure; impure)
open import Data.Container using (Container; Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; no; yes; contradiction)

open Formula

private variable
  ℓ₁ ℓ₂ ℓ₃ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ⊨-dec : (x : Program C α) → (f : Formula C) → Dec (x ⊨ f)

-- Proposition Logic

-- Theorems for ~_

~true⇔false : (x : Program C α) → x ⊨ ~ true ⇔ x ⊨ false
~true⇔false x = forward x , backward x
  where
  forward : (x : Program C α) → x ⊨ ~ true → x ⊨ false
  forward _ h = ⊥₀-elim (h tt)

  backward : (x : Program C α) → x ⊨ false → x ⊨ ~ true
  backward _ = ⊥-elim

~false⇔true : (x : Program C α) → x ⊨ ~ false ⇔ x ⊨ true
~false⇔true x = forward x , backward x
  where
  forward : (x : Program C α) → x ⊨ ~ false → x ⊨ true
  forward _ _ = tt

  backward : (x : Program C α) → x ⊨ true → x ⊨ ~ false
  backward _ _ = ⊥-elim

~~f⇔f : (f : Formula C) → (x : Program C α) → x ⊨ ~ ~ f ⇔ x ⊨ f
~~f⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → x ⊨ ~ ~ f → x ⊨ f
  forward f x ¬¬h with ⊨-dec x f
  ... | no ¬h = ⊥₀-elim (¬¬h ¬h)
  ... | yes h = h

  backward : (f : Formula C) → (x : Program C α) → x ⊨ f → x ⊨ ~ ~ f
  backward _ _ h ¬h = ¬h h

~|f₁∧f₂|⇔~f₁∨~f₂ : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ~ (f₁ ∧ f₂) ⇔ x ⊨ ~ f₁ ∨ ~ f₂
~|f₁∧f₂|⇔~f₁∨~f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ~ (f₁ ∧ f₂) → x ⊨ ~ f₁ ∨ ~ f₂
  forward f₁ f₂ x h with ⊨-dec x f₁
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ with ⊨-dec x f₂
  ...   | no ¬h₂ = inj₂ ¬h₂
  ...   | yes h₂ = ⊥₀-elim (h (h₁ , h₂))

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ~ f₁ ∨ ~ f₂ → x ⊨ ~ (f₁ ∧ f₂)
  backward _ _ _ (inj₁ ¬h₁) (h₁ , _) = ⊥₀-elim (¬h₁ h₁)
  backward _ _ _ (inj₂ ¬h₂) (_ , h₂) = ⊥₀-elim (¬h₂ h₂)

~|f₁∨f₂|⇔~f₁∧~f₂ : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ~ (f₁ ∨ f₂) ⇔ x ⊨ ~ f₁ ∧ ~ f₂
~|f₁∨f₂|⇔~f₁∧~f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ~ (f₁ ∨ f₂) → x ⊨ ~ f₁ ∧ ~ f₂
  forward _ _ _ h = (λ h₁ → h (inj₁ h₁)) , λ h₂ → h (inj₂ h₂)

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ~ f₁ ∧ ~ f₂ → x ⊨ ~ (f₁ ∨ f₂)
  backward _ _ _ (¬h₁ , _) (inj₁ h₁) = ¬h₁ h₁
  backward _ _ _ (_ , ¬h₂) (inj₂ h₂) = ¬h₂ h₂

-- Theorems for _∧_

f∧f⇔f : (f : Formula C) → (x : Program C α) → x ⊨ f ∧ f ⇔ x ⊨ f
f∧f⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → x ⊨ f ∧ f → x ⊨ f
  forward _ _ (h , _) = h

  backward : (f : Formula C) → (x : Program C α) → x ⊨ f → x ⊨ f ∧ f
  backward _ _ h = h , h

f₁∧f₂⇔f₂∧f₁ : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₁ ∧ f₂ ⇔ x ⊨ f₂ ∧ f₁
f₁∧f₂⇔f₂∧f₁ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₁ ∧ f₂ → x ⊨ f₂ ∧ f₁
  forward _ _ _ (h₁ , h₂) = h₂ , h₁

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₂ ∧ f₁ → x ⊨ f₁ ∧ f₂
  backward _ _ _ (h₂ , h₁) = h₁ , h₂

|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ (f₁ ∧ f₂) ∧ f₃ ⇔ x ⊨ f₁ ∧ (f₂ ∧ f₃)
|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ (f₁ ∧ f₂) ∧ f₃ → x ⊨ f₁ ∧ (f₂ ∧ f₃)
  forward _ _ _ _ ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ f₁ ∧ (f₂ ∧ f₃) → x ⊨ (f₁ ∧ f₂) ∧ f₃
  backward _ _ _ _ (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ f₁ ∧ (f₂ ∨ f₃) ⇔ x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃)
f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ f₁ ∧ (f₂ ∨ f₃) → x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃)
  forward _ _ _ _ (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
  forward _ _ _ _ (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) → x ⊨ f₁ ∧ (f₂ ∨ f₃)
  backward _ _ _ _ (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
  backward _ _ _ _ (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

f∧true⇔f : (f : Formula C) → (x : Program C α) → x ⊨ f ∧ true ⇔ x ⊨ f
f∧true⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → x ⊨ f ∧ true → x ⊨ f
  forward _ _ (h , _) = h

  backward : (f : Formula C) → (x : Program C α) → x ⊨ f → x ⊨ f ∧ true
  backward _ _ h = h , tt

f∧false⇔false : (f : Formula C) → (x : Program C α) → x ⊨ f ∧ false ⇔ x ⊨ false
f∧false⇔false f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → x ⊨ f ∧ false → x ⊨ false
  forward _ _ ()

  backward : (f : Formula C) → (x : Program C α) → x ⊨ false → x ⊨ f ∧ false
  backward _ _ ()

-- Theorems for _∨_

f∨f⇔f : (f : Formula C) → (x : Program C α) → x ⊨ f ∨ f ⇔ x ⊨ f
f∨f⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → x ⊨ f ∨ f → x ⊨ f
  forward _ _ (inj₁ h) = h
  forward _ _ (inj₂ h) = h

  backward : (f : Formula C) → (x : Program C α) → x ⊨ f → x ⊨ f ∨ f
  backward _ _ h = inj₁ h

f₁∨f₂⇔f₂∨f₁ : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₁ ∨ f₂ ⇔ x ⊨ f₂ ∨ f₁
f₁∨f₂⇔f₂∨f₁ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₁ ∨ f₂ → x ⊨ f₂ ∨ f₁
  forward _ _ _ (inj₁ h₁) = inj₂ h₁
  forward _ _ _ (inj₂ h₂) = inj₁ h₂

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₂ ∨ f₁ → x ⊨ f₁ ∨ f₂
  backward _ _ _ (inj₁ h₂) = inj₂ h₂
  backward _ _ _ (inj₂ h₁) = inj₁ h₁

|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ (f₁ ∨ f₂) ∨ f₃ ⇔ x ⊨ f₁ ∨ (f₂ ∨ f₃)
|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ (f₁ ∨ f₂) ∨ f₃ → x ⊨ f₁ ∨ (f₂ ∨ f₃)
  forward _ _ _ _ (inj₁ (inj₁ h₁)) = inj₁ h₁
  forward _ _ _ _ (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
  forward _ _ _ _ (inj₂ h₃) = inj₂ (inj₂ h₃)

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ f₁ ∨ (f₂ ∨ f₃) → x ⊨ (f₁ ∨ f₂) ∨ f₃
  backward _ _ _ _ (inj₁ h₁) = inj₁ (inj₁ h₁)
  backward _ _ _ _ (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
  backward _ _ _ _ (inj₂ (inj₂ h₃)) = inj₂ h₃

f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ f₁ ∨ (f₂ ∧ f₃) ⇔ x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃)
f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| f₁ f₂ f₃ x = forward f₁ f₂ f₃ x , backward f₁ f₂ f₃ x
  where
  forward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ f₁ ∨ (f₂ ∧ f₃) → x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃)
  forward _ _ _ _ (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
  forward _ _ _ _ (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃

  backward : (f₁ f₂ f₃ : Formula C) → (x : Program C α) → x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) → x ⊨ f₁ ∨ (f₂ ∧ f₃)
  backward _ _ _ _ (inj₁ h₁ , _) = inj₁ h₁
  backward _ _ _ _ (_ , inj₁ h₁) = inj₁ h₁
  backward _ _ _ _ (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

f∨true⇔true : (f : Formula C) → (x : Program C α) → x ⊨ f ∨ true ⇔ x ⊨ true
f∨true⇔true f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → x ⊨ f ∨ true → x ⊨ true
  forward _ _ _ = tt

  backward : (f : Formula C) → (x : Program C α) → x ⊨ true → x ⊨ f ∨ true
  backward _ _ _ = inj₂ tt

f∨false⇔f : (f : Formula C) → (x : Program C α) → x ⊨ f ∨ false ⇔ x ⊨ f
f∨false⇔f f x = forward f x , backward f x
  where
  forward : (f : Formula C) → (x : Program C α) → x ⊨ f ∨ false → x ⊨ f
  forward _ _ (inj₁ h) = h

  backward : (f : Formula C) → (x : Program C α) → x ⊨ f → x ⊨ f ∨ false
  backward _ _ h = inj₁ h

-- Theorems for _⇒_

f₁⇒f₂⇔~f₁∨f₂ : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₁ ⇒ f₂ ⇔ x ⊨ ~ f₁ ∨ f₂
f₁⇒f₂⇔~f₁∨f₂ f₁ f₂ x = forward f₁ f₂ x , backward f₁ f₂ x
  where
  forward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ f₁ ⇒ f₂ → x ⊨ ~ f₁ ∨ f₂
  forward f₁ _ x h with ⊨-dec x f₁
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ = inj₂ (h h₁)

  backward : (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ~ f₁ ∨ f₂ → x ⊨ f₁ ⇒ f₂
  backward _ _ _ (inj₁ ¬h₁) h₁ = ⊥₀-elim (¬h₁ h₁)
  backward _ _ _ (inj₂ h₂) _ = h₂

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

~|⟨s⟩f|⇔[s]~f : (s : Shape C) → (f : Formula C) → (x : Program C α) → x ⊨ ~ (⟨ s ⟩ f) ⇔ x ⊨ [ s ] ~ f
~|⟨s⟩f|⇔[s]~f s f x = forward s f x , backward s f x
  where
  forward : (s : Shape C) → (f : Formula C) → (x : Program C α) → x ⊨ ~ (⟨ s ⟩ f) → x ⊨ [ s ] ~ f
  forward _ _ x h¬∃ with free x
  ... | pure _ = tt
  ... | impure _ = λ { refl p h → h¬∃ (refl , p , h) }

  backward : (s : Shape C) → (f : Formula C) → (x : Program C α) → x ⊨ [ s ] ~ f → x ⊨ ~ (⟨ s ⟩ f)
  backward _ _ x h¬∀ h∃ with free x
  backward _ _ x h¬∀ () | pure _
  backward _ _ x h¬∀ (refl , p , h) | impure _ = h¬∀ refl p h

⟨s⟩false⇔false : (s : Shape C) → (x : Program C α) → x ⊨ ⟨ s ⟩ false ⇔ x ⊨ false
⟨s⟩false⇔false s x = forward s x , backward s x
  where
  forward : (s : Shape C) → (x : Program C α) → x ⊨ ⟨ s ⟩ false → x ⊨ false
  forward _ x h∃ with free x
  forward _ x () | pure _
  forward _ x () | impure _

  backward : (s : Shape C) → (x : Program C α) → x ⊨ false → x ⊨ ⟨ s ⟩ false
  backward _ _ ()

⟨s⟩|f₁∨f₂|⇔⟨s⟩f₁∨⟨s⟩f₂ : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ⟨ s ⟩ (f₁ ∨ f₂) ⇔ x ⊨ ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂
⟨s⟩|f₁∨f₂|⇔⟨s⟩f₁∨⟨s⟩f₂ s f₁ f₂ x = forward s f₁ f₂ x , backward s f₁ f₂ x
  where
  forward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ⟨ s ⟩ (f₁ ∨ f₂) → x ⊨ ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂
  forward _ _ _ x h∃ with free x
  forward _ _ _ x (refl , p , inj₁ h₁) | impure _ = inj₁ (refl , p , h₁)
  forward _ _ _ x (refl , p , inj₂ h₂) | impure _ = inj₂ (refl , p , h₂)

  backward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ⟨ s ⟩ f₁ ∨ ⟨ s ⟩ f₂ → x ⊨ ⟨ s ⟩ (f₁ ∨ f₂)
  backward _ _ _ x h∃ with free x
  backward _ _ _ x (inj₁ ()) | pure _
  backward _ _ _ x (inj₂ ()) | pure _
  backward _ _ _ x (inj₁ (refl , p , h₁)) | impure _ = refl , p , inj₁ h₁
  backward _ _ _ x (inj₂ (refl , p , h₂)) | impure _ = refl , p , inj₂ h₂

⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ ⟨ s ⟩ f₁ ∧ [ s ] f₂ → x ⊨ ⟨ s ⟩ (f₁ ∧ f₂)
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| _ _ _ x h with free x
⟨s⟩f₁∧[s]f₂→⟨s⟩|f₁∧f₂| _ _ _ x ((refl , p , h₁) , h∀₂) | impure _ = refl , p , h₁ , h∀₂ refl p

-- Theorems for [_]_

~|[s]f|⇔⟨s⟩~f : (s : Shape C) → (f : Formula C) → (x : Program C α) → x ⊨ ~ ([ s ] f) ⇔ x ⊨ ⟨ s ⟩ ~ f
~|[s]f|⇔⟨s⟩~f s f x = forward s f x , backward s f x
  where
  forward : (s : Shape C) → (f : Formula C) → (x : Program C α) → x ⊨ ~ ([ s ] f) → x ⊨ ⟨ s ⟩ ~ f
  forward s f x h¬∀ with ⊨-dec x (⟨ s ⟩ ~ f)
  ... | yes h∃ = h∃
  ... | no h¬∃ with free x
  ...   | pure _ = ⊥₀-elim (h¬∀ tt)
  ...   | impure (_ , c) = contradiction (λ { refl p → case ⊨-dec (c p) f of λ { (no ¬h) → ⊥₀-elim (h¬∃ (refl , p , ¬h)) ; (yes h) → h } }) h¬∀

  backward : (s : Shape C) → (f : Formula C) → (x : Program C α) → x ⊨ ⟨ s ⟩ ~ f → x ⊨ ~ ([ s ] f)
  backward _ _ x h∃ h∀ with free x
  backward _ _ x (refl , p , ¬h) h∀ | impure _ = ¬h (h∀ refl p)

[s]true⇔true : (s : Shape C) → (x : Program C α) → x ⊨ [ s ] true ⇔ x ⊨ true
[s]true⇔true s x = forward s x , backward s x
  where
  forward : (s : Shape C) → (x : Program C α) → x ⊨ [ s ] true → x ⊨ true
  forward _ _ _ = tt

  backward : (s : Shape C) → (x : Program C α) → x ⊨ true → x ⊨ [ s ] true
  backward _ x _ with free x
  ... | pure _ = tt
  ... | impure _ = λ { refl _ → tt }

[s]|f₁∧f₂|⇔[s]f₁∧[s]f₂ : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ [ s ] (f₁ ∧ f₂) ⇔ x ⊨ [ s ] f₁ ∧ [ s ] f₂
[s]|f₁∧f₂|⇔[s]f₁∧[s]f₂ s f₁ f₂ x = forward s f₁ f₂ x , backward s f₁ f₂ x
  where
  forward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ [ s ] (f₁ ∧ f₂) → x ⊨ [ s ] f₁ ∧ [ s ] f₂
  forward _ _ _ x h∀ with free x
  ... | pure _ = tt , tt
  ... | impure _ = (λ { refl p → proj₁ (h∀ refl p) }) , λ { refl p → proj₂ (h∀ refl p) }

  backward : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ [ s ] f₁ ∧ [ s ] f₂ → x ⊨ [ s ] (f₁ ∧ f₂)
  backward _ _ _ x (h∀₁ , h∀₂) with free x
  ... | pure _ = tt
  ... | impure _ = λ { refl p → h∀₁ refl p , h∀₂ refl p }

[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ : (s : Shape C) → (f₁ f₂ : Formula C) → (x : Program C α) → x ⊨ [ s ] (f₁ ∨ f₂) → x ⊨ ⟨ s ⟩ f₁ ∨ [ s ] f₂
[s]|f₁∨f₂|→⟨s⟩f₁∨[s]f₂ s f₁ f₂ x h with ⊨-dec x (⟨ s ⟩ f₁)
... | yes h∃ = inj₁ h∃
... | no h¬∃ with ⊨-dec x ([ s ] f₂)
...   | yes h∀ = inj₂ h∀
...   | no h¬∀ with free x
...     | pure _ = inj₂ tt
...     | impure _ = contradiction (λ { refl p → case h refl p of λ { (inj₁ h₁) → ⊥₀-elim (h¬∃ (refl , p , h₁)) ; (inj₂ h₂) → h₂  } }) h¬∀

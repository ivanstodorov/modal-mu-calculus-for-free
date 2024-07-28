{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.ActionFormulas.Properties where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program; free; pure; impure)
open import Common.RegularFormulas using (ActionFormula; _∈_)
open import Data.Container using (Container; Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.ActionFormulas.Base using (Formula; _⊨_)
open import Relation.Nullary using (Dec; no; yes; contradiction)

open ActionFormula
open Formula

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  S : Set ℓ
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ∈-dec : (s : S) → (af : ActionFormula S) → Dec (s ∈ af)
  ⊨-dec : (x : Program C α) → (f : Formula (Shape C)) → Dec (x ⊨ f)

-- Action formulas

trueᶜ⇔false : (s : S) → s ∈ true ᶜ ⇔ s ∈ false
trueᶜ⇔false s = forward s , backward s
  where
  forward : (s : S) → s ∈ true ᶜ → s ∈ false
  forward _ h = ⊥₀-elim (h tt)

  backward : (s : S) → s ∈ false → s ∈ true ᶜ
  backward _ ()

false⇔trueᶜ : (s : S) → s ∈ false ᶜ ⇔ s ∈ true
false⇔trueᶜ s = forward s , backward s
  where
  forward : (s : S) → s ∈ false ᶜ → s ∈ true
  forward _ _ = tt

  backward : (s : S) → s ∈ true → s ∈ false ᶜ
  backward _ _ ()

|af₁∪af₂|ᶜ⇔af₁ᶜ∩af₂ᶜ : (s : S) → (af₁ af₂ : ActionFormula S) → s ∈ (af₁ ∪ af₂) ᶜ ⇔ s ∈ af₁ ᶜ ∩ af₂ ᶜ
|af₁∪af₂|ᶜ⇔af₁ᶜ∩af₂ᶜ s af₁ af₂ = forward s af₁ af₂ , backward s af₁ af₂
  where
  forward : (s : S) → (af₁ af₂ : ActionFormula S) → s ∈ (af₁ ∪ af₂) ᶜ → s ∈ af₁ ᶜ ∩ af₂ ᶜ
  forward _ _ _ hn = (λ h₁ → hn (inj₁ h₁)) , λ h₂ → hn (inj₂ h₂)

  backward : (s : S) → (af₁ af₂ : ActionFormula S) → s ∈ af₁ ᶜ ∩ af₂ ᶜ → s ∈ (af₁ ∪ af₂) ᶜ
  backward s af₁ af₂ (hn₁ , _) (inj₁ h₁) = hn₁ h₁
  backward s af₁ af₂ (_ , hn₂) (inj₂ h₂) = hn₂ h₂

|af₁∩af₂|ᶜ⇔af₁ᶜ∪af₂ᶜ : (s : S) → (af₁ af₂ : ActionFormula S) → s ∈ (af₁ ∩ af₂) ᶜ ⇔ s ∈ af₁ ᶜ ∪ af₂ ᶜ
|af₁∩af₂|ᶜ⇔af₁ᶜ∪af₂ᶜ s af₁ af₂ = forward s af₁ af₂ , backward s af₁ af₂
  where
  forward : (s : S) → (af₁ af₂ : ActionFormula S) → s ∈ (af₁ ∩ af₂) ᶜ → s ∈ af₁ ᶜ ∪ af₂ ᶜ
  forward s af₁ af₂ hn with ∈-dec s af₁
  ... | no hn₁ = inj₁ hn₁
  ... | yes h₁ with ∈-dec s af₂
  ...   | no hn₂ = inj₂ hn₂
  ...   | yes h₂ = ⊥₀-elim (hn (h₁ , h₂))

  backward : (s : S) → (af₁ af₂ : ActionFormula S) → s ∈ af₁ ᶜ ∪ af₂ ᶜ → s ∈ (af₁ ∩ af₂) ᶜ
  backward _ _ _ (inj₁ hn₁) (h₁ , _) = hn₁ h₁
  backward _ _ _ (inj₂ hn₂) (_ , h₂) = hn₂ h₂

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

~~f⇔f : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ ~ ~ f ⇔ x ⊨ f
~~f⇔f x f = forward x f , backward x f
  where
  forward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ ~ ~ f → x ⊨ f
  forward x f ¬¬h with ⊨-dec x f
  ... | no ¬h = ⊥₀-elim (¬¬h ¬h)
  ... | yes h = h

  backward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f → x ⊨ ~ ~ f
  backward _ _ h ¬h = ¬h h

~|f₁∧f₂|⇔~f₁∨~f₂ : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ~ (f₁ ∧ f₂) ⇔ x ⊨ ~ f₁ ∨ ~ f₂
~|f₁∧f₂|⇔~f₁∨~f₂ x f₁ f₂ = forward x f₁ f₂ , backward x f₁ f₂
  where
  forward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ~ (f₁ ∧ f₂) → x ⊨ ~ f₁ ∨ ~ f₂
  forward x f₁ f₂ h with ⊨-dec x f₁
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ with ⊨-dec x f₂
  ...   | no ¬h₂ = inj₂ ¬h₂
  ...   | yes h₂ = ⊥₀-elim (h (h₁ , h₂))

  backward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ~ f₁ ∨ ~ f₂ → x ⊨ ~ (f₁ ∧ f₂)
  backward _ _ _ (inj₁ ¬h₁) (h₁ , _) = ⊥₀-elim (¬h₁ h₁)
  backward _ _ _ (inj₂ ¬h₂) (_ , h₂) = ⊥₀-elim (¬h₂ h₂)

~|f₁∨f₂|⇔~f₁∧~f₂ : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ~ (f₁ ∨ f₂) ⇔ x ⊨ ~ f₁ ∧ ~ f₂
~|f₁∨f₂|⇔~f₁∧~f₂ x f₁ f₂ = forward x f₁ f₂ , backward x f₁ f₂
  where
  forward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ~ (f₁ ∨ f₂) → x ⊨ ~ f₁ ∧ ~ f₂
  forward _ _ _ h = (λ h₁ → h (inj₁ h₁)) , λ h₂ → h (inj₂ h₂)

  backward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ~ f₁ ∧ ~ f₂ → x ⊨ ~ (f₁ ∨ f₂)
  backward _ _ _ (¬h₁ , _) (inj₁ h₁) = ¬h₁ h₁
  backward _ _ _ (_ , ¬h₂) (inj₂ h₂) = ¬h₂ h₂

-- Theorems for _∧_

f∧f⇔f : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∧ f ⇔ x ⊨ f
f∧f⇔f x f = forward x f , backward x f
  where
  forward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∧ f → x ⊨ f
  forward _ _ (h , _) = h

  backward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f → x ⊨ f ∧ f
  backward _ _ h = h , h

f₁∧f₂⇔f₂∧f₁ : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₁ ∧ f₂ ⇔ x ⊨ f₂ ∧ f₁
f₁∧f₂⇔f₂∧f₁ x f₁ f₂ = forward x f₁ f₂ , backward x f₁ f₂
  where
  forward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₁ ∧ f₂ → x ⊨ f₂ ∧ f₁
  forward _ _ _ (h₁ , h₂) = h₂ , h₁

  backward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₂ ∧ f₁ → x ⊨ f₁ ∧ f₂
  backward _ _ _ (h₂ , h₁) = h₁ , h₂

|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ (f₁ ∧ f₂) ∧ f₃ ⇔ x ⊨ f₁ ∧ (f₂ ∧ f₃)
|f₁∧f₂|∧f₃⇔f₁∧|f₂∧f₃| x f₁ f₂ f₃ = forward x f₁ f₂ f₃ , backward x f₁ f₂ f₃
  where
  forward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ (f₁ ∧ f₂) ∧ f₃ → x ⊨ f₁ ∧ (f₂ ∧ f₃)
  forward _ _ _ _ ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃

  backward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ f₁ ∧ (f₂ ∧ f₃) → x ⊨ (f₁ ∧ f₂) ∧ f₃
  backward _ _ _ _ (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ f₁ ∧ (f₂ ∨ f₃) ⇔ x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃)
f₁∧|f₂∨f₃|⇔|f₁∧f₂|∨|f₁∧f₃| x f₁ f₂ f₃ = forward x f₁ f₂ f₃ , backward x f₁ f₂ f₃
  where
  forward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ f₁ ∧ (f₂ ∨ f₃) → x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃)
  forward _ _ _ _ (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
  forward _ _ _ _ (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)

  backward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) → x ⊨ f₁ ∧ (f₂ ∨ f₃)
  backward _ _ _ _ (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
  backward _ _ _ _ (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

f∧true⇔f : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∧ true ⇔ x ⊨ f
f∧true⇔f x f = forward x f , backward x f
  where
  forward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∧ true → x ⊨ f
  forward _ _ (h , _) = h

  backward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f → x ⊨ f ∧ true
  backward _ _ h = h , tt

f∧false⇔false : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∧ false ⇔ x ⊨ false
f∧false⇔false x f = forward x f , backward x f
  where
  forward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∧ false → x ⊨ false
  forward _ _ ()

  backward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ false → x ⊨ f ∧ false
  backward _ _ ()

-- Theorems for _∨_

f∨f⇔f : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∨ f ⇔ x ⊨ f
f∨f⇔f x f = forward x f , backward x f
  where
  forward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∨ f → x ⊨ f
  forward _ _ (inj₁ h) = h
  forward _ _ (inj₂ h) = h

  backward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f → x ⊨ f ∨ f
  backward _ _ h = inj₁ h

f₁∨f₂⇔f₂∨f₁ : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₁ ∨ f₂ ⇔ x ⊨ f₂ ∨ f₁
f₁∨f₂⇔f₂∨f₁ x f₁ f₂ = forward x f₁ f₂ , backward x f₁ f₂
  where
  forward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₁ ∨ f₂ → x ⊨ f₂ ∨ f₁
  forward _ _ _ (inj₁ h₁) = inj₂ h₁
  forward _ _ _ (inj₂ h₂) = inj₁ h₂

  backward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₂ ∨ f₁ → x ⊨ f₁ ∨ f₂
  backward _ _ _ (inj₁ h₂) = inj₂ h₂
  backward _ _ _ (inj₂ h₁) = inj₁ h₁

|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ (f₁ ∨ f₂) ∨ f₃ ⇔ x ⊨ f₁ ∨ (f₂ ∨ f₃)
|f₁∨f₂|∨f₃⇔f₁∨|f₂∨f₃| x f₁ f₂ f₃ = forward x f₁ f₂ f₃ , backward x f₁ f₂ f₃
  where
  forward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ (f₁ ∨ f₂) ∨ f₃ → x ⊨ f₁ ∨ (f₂ ∨ f₃)
  forward _ _ _ _ (inj₁ (inj₁ h₁)) = inj₁ h₁
  forward _ _ _ _ (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
  forward _ _ _ _ (inj₂ h₃) = inj₂ (inj₂ h₃)

  backward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ f₁ ∨ (f₂ ∨ f₃) → x ⊨ (f₁ ∨ f₂) ∨ f₃
  backward _ _ _ _ (inj₁ h₁) = inj₁ (inj₁ h₁)
  backward _ _ _ _ (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
  backward _ _ _ _ (inj₂ (inj₂ h₃)) = inj₂ h₃

f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ f₁ ∨ (f₂ ∧ f₃) ⇔ x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃)
f₁∨|f₂∧f₃|⇔|f₁∨f₂|∧|f₁∨f₃| x f₁ f₂ f₃ = forward x f₁ f₂ f₃ , backward x f₁ f₂ f₃
  where
  forward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ f₁ ∨ (f₂ ∧ f₃) → x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃)
  forward _ _ _ _ (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
  forward _ _ _ _ (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃

  backward : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C)) → x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) → x ⊨ f₁ ∨ (f₂ ∧ f₃)
  backward _ _ _ _ (inj₁ h₁ , _) = inj₁ h₁
  backward _ _ _ _ (_ , inj₁ h₁) = inj₁ h₁
  backward _ _ _ _ (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

f∨true⇔true : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∨ true ⇔ x ⊨ true
f∨true⇔true x f = forward x f , backward x f
  where
  forward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∨ true → x ⊨ true
  forward _ _ _ = tt

  backward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ true → x ⊨ f ∨ true
  backward _ _ _ = inj₂ tt

f∨false⇔f : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∨ false ⇔ x ⊨ f
f∨false⇔f x f = forward x f , backward x f
  where
  forward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f ∨ false → x ⊨ f
  forward _ _ (inj₁ h) = h

  backward : (x : Program C α) → (f : Formula (Shape C)) → x ⊨ f → x ⊨ f ∨ false
  backward _ _ h = inj₁ h

-- Theorems for _⇒_

f₁⇒f₂⇔~f₁∨f₂ : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₁ ⇒ f₂ ⇔ x ⊨ ~ f₁ ∨ f₂
f₁⇒f₂⇔~f₁∨f₂ x f₁ f₂ = forward x f₁ f₂ , backward x f₁ f₂
  where
  forward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ f₁ ⇒ f₂ → x ⊨ ~ f₁ ∨ f₂
  forward x f₁ _ h with ⊨-dec x f₁
  ... | no ¬h₁ = inj₁ ¬h₁
  ... | yes h₁ = inj₂ (h h₁)

  backward : (x : Program C α) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ~ f₁ ∨ f₂ → x ⊨ f₁ ⇒ f₂
  backward _ _ _ (inj₁ ¬h₁) h₁ = ⊥₀-elim (¬h₁ h₁)
  backward _ _ _ (inj₂ h₂) _ = h₂

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

~|⟨af⟩f|⇔[af]~f : (x : Program C α) → (af : ActionFormula (Shape C)) → (f : Formula (Shape C)) → x ⊨ ~ (⟨ af ⟩ f) ⇔ x ⊨ [ af ] ~ f
~|⟨af⟩f|⇔[af]~f x af f = forward x af f , backward x af f
  where
  forward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f : Formula (Shape C)) → x ⊨ ~ (⟨ af ⟩ f) → x ⊨ [ af ] ~ f
  forward x _ _ h¬∃ with free x
  ... | pure _ = tt
  ... | impure _ = λ { refl p h → h¬∃ (refl , p , h) }

  backward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f : Formula (Shape C)) → x ⊨ [ af ] ~ f → x ⊨ ~ (⟨ af ⟩ f)
  backward x _ _ h¬∀ h∃ with free x
  backward x _ _ h¬∀ () | pure _
  backward x _ _ h¬∀ (refl , p , h) | impure _ = h¬∀ refl p h

⟨af⟩false⇔false : (x : Program C α) → (af : ActionFormula (Shape C)) → x ⊨ ⟨ af ⟩ false ⇔ x ⊨ false
⟨af⟩false⇔false x af = forward x af , backward x af
  where
  forward : (x : Program C α) → (af : ActionFormula (Shape C)) → x ⊨ ⟨ af ⟩ false → x ⊨ false
  forward x _ h∃ with free x
  forward x _ () | pure _
  forward x _ () | impure _

  backward : (x : Program C α) → (af : ActionFormula (Shape C)) → x ⊨ false → x ⊨ ⟨ af ⟩ false
  backward _ _ ()

⟨af⟩|f₁∨f₂|⇔⟨af⟩f₁∨⟨af⟩f₂ : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ⟨ af ⟩ (f₁ ∨ f₂) ⇔ x ⊨ ⟨ af ⟩ f₁ ∨ ⟨ af ⟩ f₂
⟨af⟩|f₁∨f₂|⇔⟨af⟩f₁∨⟨af⟩f₂ x af f₁ f₂ = forward x af f₁ f₂ , backward x af f₁ f₂
  where
  forward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ⟨ af ⟩ (f₁ ∨ f₂) → x ⊨ ⟨ af ⟩ f₁ ∨ ⟨ af ⟩ f₂
  forward x _ _ _ h∃ with free x
  forward x _ _ _ (refl , p , inj₁ h₁) | impure _ = inj₁ (refl , p , h₁)
  forward x _ _ _ (refl , p , inj₂ h₂) | impure _ = inj₂ (refl , p , h₂)

  backward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ⟨ af ⟩ f₁ ∨ ⟨ af ⟩ f₂ → x ⊨ ⟨ af ⟩ (f₁ ∨ f₂)
  backward x _ _ _ h∃ with free x
  backward x _ _ _ (inj₁ ()) | pure _
  backward x _ _ _ (inj₂ ()) | pure _
  backward x _ _ _ (inj₁ (refl , p , h₁)) | impure _ = refl , p , inj₁ h₁
  backward x _ _ _ (inj₂ (refl , p , h₂)) | impure _ = refl , p , inj₂ h₂

⟨af⟩f₁∧[af]f₂→⟨af⟩|f₁∧f₂| : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ ⟨ af ⟩ f₁ ∧ [ af ] f₂ → x ⊨ ⟨ af ⟩ (f₁ ∧ f₂)
⟨af⟩f₁∧[af]f₂→⟨af⟩|f₁∧f₂| x _ _ _ h with free x
⟨af⟩f₁∧[af]f₂→⟨af⟩|f₁∧f₂| x _ _ _ ((refl , p , h₁) , h∀₂) | impure _ = refl , p , h₁ , h∀₂ refl p

-- Theorems for [_]_

~|[af]f|⇔⟨af⟩~f : (x : Program C α) → (af : ActionFormula (Shape C)) → (f : Formula (Shape C)) → x ⊨ ~ ([ af ] f) ⇔ x ⊨ ⟨ af ⟩ ~ f
~|[af]f|⇔⟨af⟩~f x af f = forward x af f , backward x af f
  where
  forward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f : Formula (Shape C)) → x ⊨ ~ ([ af ] f) → x ⊨ ⟨ af ⟩ ~ f
  forward x af f h¬∀ with ⊨-dec x (⟨ af ⟩ ~ f)
  ... | yes h∃ = h∃
  ... | no h¬∃ with free x
  ...   | pure _ = ⊥₀-elim (h¬∀ tt)
  ...   | impure (_ , c) = contradiction (λ { refl p → case ⊨-dec (c p) f of λ { (no ¬h) → ⊥₀-elim (h¬∃ (refl , p , ¬h)) ; (yes h) → h } }) h¬∀

  backward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f : Formula (Shape C)) → x ⊨ ⟨ af ⟩ ~ f → x ⊨ ~ ([ af ] f)
  backward x _ _ h∃ h∀ with free x
  backward x _ _ (refl , p , ¬h) h∀ | impure _ = ¬h (h∀ refl p)

[af]true⇔true : (x : Program C α) → (af : ActionFormula (Shape C)) → x ⊨ [ af ] true ⇔ x ⊨ true
[af]true⇔true x af = forward x af , backward x af
  where
  forward : (x : Program C α) → (af : ActionFormula (Shape C)) → x ⊨ [ af ] true → x ⊨ true
  forward _ _ _ = tt

  backward : (x : Program C α) → (af : ActionFormula (Shape C)) → x ⊨ true → x ⊨ [ af ] true
  backward x _ _ with free x
  ... | pure _ = tt
  ... | impure _ = λ { refl _ → tt }

[af]|f₁∧f₂|⇔[af]f₁∧[af]f₂ : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ [ af ] (f₁ ∧ f₂) ⇔ x ⊨ [ af ] f₁ ∧ [ af ] f₂
[af]|f₁∧f₂|⇔[af]f₁∧[af]f₂ x af f₁ f₂ = forward x af f₁ f₂ , backward x af f₁ f₂
  where
  forward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ [ af ] (f₁ ∧ f₂) → x ⊨ [ af ] f₁ ∧ [ af ] f₂
  forward x _ _ _ h∀ with free x
  ... | pure _ = tt , tt
  ... | impure _ = (λ { refl p → proj₁ (h∀ refl p) }) , λ { refl p → proj₂ (h∀ refl p) }

  backward : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ [ af ] f₁ ∧ [ af ] f₂ → x ⊨ [ af ] (f₁ ∧ f₂)
  backward x _ _ _ (h∀₁ , h∀₂) with free x
  ... | pure _ = tt
  ... | impure _ = λ { refl p → h∀₁ refl p , h∀₂ refl p }

[af]|f₁∨f₂|→⟨af⟩f₁∨[af]f₂ : (x : Program C α) → (af : ActionFormula (Shape C)) → (f₁ f₂ : Formula (Shape C)) → x ⊨ [ af ] (f₁ ∨ f₂) → x ⊨ ⟨ af ⟩ f₁ ∨ [ af ] f₂
[af]|f₁∨f₂|→⟨af⟩f₁∨[af]f₂ x af f₁ f₂ h with ⊨-dec x (⟨ af ⟩ f₁)
... | yes h∃ = inj₁ h∃
... | no h¬∃ with ⊨-dec x ([ af ] f₂)
...   | yes h∀ = inj₂ h∀
...   | no h¬∀ with free x
...     | pure _ = inj₂ tt
...     | impure _ = contradiction (λ { refl p → case h refl p of λ { (inj₁ h₁) → ⊥₀-elim (h¬∃ (refl , p , h₁)) ; (inj₂ h₂) → h₂  } }) h¬∀

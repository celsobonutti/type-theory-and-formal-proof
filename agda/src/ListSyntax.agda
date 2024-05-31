module ListSyntax where

open import Data.List as List using (List; _∷_; [])
open import Data.Product
open import Level using (_⊔_; Level)
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Function

variable
  a b : Level
  A : Set a
  B : Set b


record ListSyntax {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field [_] : B → List A

open ListSyntax ⦃ ... ⦄ public

instance
  cons : ∀ {a b} {A : Set a} {B : Set b} ⦃ _ : ListSyntax A B ⦄
        →  ListSyntax A (A × B)
  [_] ⦃ cons ⦄ (x , xs) = x ∷ [ xs ]

instance
  sing : ∀ {a} {A : Set a} → ListSyntax A A
  [_] ⦃ sing ⦄ = _∷ []

_ : List ℕ
_ = [ 1 , 2 , 3 ]

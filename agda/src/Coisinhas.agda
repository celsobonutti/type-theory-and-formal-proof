module Coisinhas where

open import Data.String as String using (String)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality

if_then_else_ : {A : Set} → Bool → A → A → A
if false then x₁ else x₂ = x₂
if true then x₁ else x₂ = x₁

record Sigma (A : Set) (F : A -> Set) : Set where
  field
    fst : A
    snd : F fst

not : (x : Bool) → Σ Bool (λ y → y ≢ x)
not false = true , (λ ())
not true = false , (λ ())

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _::_ : ∀ {n} → A → Vec A n → Vec A (suc n)

variable
  A B : Set
  n m : ℕ

concat : Vec A m → Vec A n → Vec A (m + n)
concat [] x₁ = x₁
concat (x :: x₂) x₁ = x :: concat x₂ x₁

map : (A → B) → Vec A n → Vec B n
map x [] = []
map x (x₁ :: x₂) = x x₁ :: map x x₂

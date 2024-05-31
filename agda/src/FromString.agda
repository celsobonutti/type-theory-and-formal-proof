module FromString where

open import Data.String as String using (String; _++_) renaming (_≈_ to _≈ₛ_; _≈?_ to _≈ₛ?_)
open import Function.Base using (_∘_; id)

record IsString (A : Set) : Set where
  field
    from-string : String → A

instance
  stringIsString : IsString String
  IsString.from-string stringIsString = id

open IsString ⦃...⦄ public using (from-string)

{-# BUILTIN FROMSTRING from-string #-}

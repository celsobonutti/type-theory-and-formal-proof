module StrMap where

open import Data.String.Properties using (<-strictTotalOrder-≈; ≈-setoid; ≈-decSetoid; _≟_)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as StrMap public

module StrSet where

open import Data.String.Properties using (<-strictTotalOrder-≈; ≈-setoid; ≈-decSetoid; _≟_) renaming (≈-sym to ≈ₛ-sym; ≈-refl to ≈ₛ-refl; ≈-trans to ≈ₛ-trans)
open import Data.Tree.AVL.Sets <-strictTotalOrder-≈ as StrSet renaming (⟨Set⟩ to StrSet; _∈?_ to do-not-use) public
open import Data.Tree.AVL <-strictTotalOrder-≈ as AVL using () renaming (Tree to AVLTree)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Binary.PropositionalEquality.Properties
open import Data.String using (String; _++_) renaming (_≈_ to _≈ₛ_; _≈?_ to _≈ₛ?_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary using (DecidableEquality) renaming (Decidable to Decidable₂)
open import Data.List as List using (List; _∷_; [])
open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (≋⇒≡; ≡⇒≋; _≡?_) renaming (_≋_ to _≋ₗ_; _≋?_ to _≋ₗ?_; ≋-refl to ≋ₗ-refl; ≋-sym to ≋ₗ-sym; ≋-trans to ≋ₗ-trans)
open import Data.Tree.AVL.Map.Relation.Unary.Any <-strictTotalOrder-≈ using (Any; any?) public

data _≋_ : StrSet → StrSet → Set where
  to-list-eq : ∀ {x y} → toList x ≡ toList y → x ≋ y

_≋?_ : Decidable₂ (_≋_)
_≋?_ x y with toList x ≡? toList y
... | no ¬eq = no λ { (to-list-eq x) → ¬eq x}
... | yes p = yes (to-list-eq p)

≋-refl : ∀ {x} → x ≋ x
≋-refl {x} = to-list-eq refl

≋-sym : ∀ {x y} → x ≋ y → y ≋ x
≋-sym {x} {y} (to-list-eq x≋y) = to-list-eq (sym x≋y)

≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
≋-trans (to-list-eq x≋y) (to-list-eq y≋z) = to-list-eq (trans x≋y y≋z)

≋-is-equivalence : IsEquivalence _≋_
IsEquivalence.refl ≋-is-equivalence = ≋-refl
IsEquivalence.sym ≋-is-equivalence = ≋-sym
IsEquivalence.trans ≋-is-equivalence = ≋-trans

reflexive : ∀ {x y} → x ≡ y → x ≋ y
reflexive = IsEquivalence.reflexive ≋-is-equivalence

module ≋-Reasoning where

  begin_ : {x y : StrSet} → x ≋ y → x ≋ y
  begin_ x~y = x~y

  infix 1 begin_

  _∎ : (x : StrSet) → x ≋ x
  _∎ x = ≋-refl

  infix 3 _∎

  _≋⟨_⟩_ : (x : StrSet) → ∀ {y z} → x ≋ y → y ≋ z → x ≋ z
  _ ≋⟨ x~y ⟩ y~z = ≋-trans x~y y~z

  infixr 2 _≋⟨_⟩_

  _≡⟨⟩_ : (x : StrSet) → ∀ {y} → x ≋ y → x ≋ y
  x ≡⟨⟩ p = p

  infixr 2 _≡⟨⟩_


  _≡⟨_⟩_ : (x : StrSet) → ∀ {y z} → x ≡ y → y ≋ z → x ≋ z
  _ ≡⟨ refl ⟩ y~z = y~z

  infixr 2 _≡⟨_⟩_

open AVLTree

postulate
  -- TODO: Prove this (if possible)
  union-sym : ∀ x y → union x y ≋ union y x
  delete-singleton : (x : String) → delete x (singleton x) ≡ empty
  to-from-list : ∀ x → fromList (toList x) ≡ x
  union-is-empty-then-both-are-empty : ∀ {x y} → union x y ≋ empty → x ≋ empty × y ≋ empty

to-list-≡ : ∀ {x y} → x ≡ y → toList x ≡ toList y
to-list-≡ refl = refl

from-list-≡ : ∀ {x y} → x ≡ y → fromList x ≡ fromList y
from-list-≡ refl = refl

≋-cong : {x y : StrSet} → (f : StrSet → StrSet) → x ≋ y → f x ≋ f y
≋-cong {x} {y} f (to-list-eq eq) =
  begin
   f x
   ≡⟨ sym (cong f (to-from-list x)) ⟩
   f (fromList (toList x))
   ≡⟨ cong (λ a → f (fromList a)) eq ⟩
   f (fromList (toList y))
   ≡⟨ cong f (to-from-list y) ⟩
   f y
  ∎
  where
    open ≋-Reasoning

≋⇒≡ₛ : ∀ {x y} → x ≋ y → x ≡ y
≋⇒≡ₛ {x} {y} (to-list-eq list-eq) =
  begin
    x
    ≡⟨ sym (to-from-list x) ⟩
    fromList (toList x)
    ≡⟨ cong fromList list-eq ⟩
    fromList (toList y)
    ≡⟨ to-from-list y ⟩
    y
  ∎
  where
    open ≡-Reasoning

empty-[] : toList empty ≡ []
empty-[] = refl

delete-empty : (x : String) → delete x empty ≡ empty
delete-empty x = refl

delete-empty-equiv : ∀ {x} → delete x empty ≋ empty
delete-empty-equiv = reflexive refl

union-empty-is-x : ∀ {x} → union empty x ≋ x
union-empty-is-x {x} = reflexive refl

union-empty-is-xˡ : ∀ {x} → union x empty ≋ x
union-empty-is-xˡ {x} =
  begin
    union x empty
  ≋⟨ union-sym x empty ⟩
    union empty x
  ≋⟨ union-empty-is-x ⟩
    x
  ∎
  where
    open ≋-Reasoning

union-empty-empty : union empty empty ≋ empty
union-empty-empty = to-list-eq refl

union-emptyʳ : ∀ {x} → union empty x ≋ empty → x ≋ empty
union-emptyʳ {x} eq =
  begin
    union empty x
    ≋⟨ eq ⟩
    empty
  ∎
  where
    open ≋-Reasoning

union-emptyˡ : ∀ {x} → union x empty ≋ empty → x ≋ empty
union-emptyˡ {x} union-is-empty =
  begin
    x
  ≋⟨ ≋-sym union-empty-is-xˡ ⟩
    union x empty
  ≋⟨ union-is-empty ⟩
    empty
  ∎
  where open ≋-Reasoning

union-of-empty-is-empty : ∀ {x y} → x ≡ empty → y ≡ empty → union x y ≡ empty
union-of-empty-is-empty refl refl = refl

union-of-empty-is-empty-≋ : ∀ {x y} → x ≋ empty → y ≋ empty → union x y ≋ empty
union-of-empty-is-empty-≋ {x} {y} x≋empty y≋empty =
  begin
    union x y
    ≋⟨ ≋-cong (λ a → union a y) x≋empty ⟩
    union empty y
    ≋⟨ ≋-cong (union empty) y≋empty ⟩
    union empty empty
    ≡⟨⟩
    empty
  ∎
  where open ≋-Reasoning

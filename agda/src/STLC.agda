module STLC where

open import ListSyntax
open import Data.Empty using (⊥)
open import Data.List as List using (List; []; _∷_)
open import Data.String as String using (String)
open import Data.String.Properties as String using ()
open import Data.Unit using (⊤; tt)
open import FromString
open import Level using (Level; 0ℓ)
open import Relation.Binary renaming (Decidable to Decidable₂)
open import Relation.Binary.Bundles
open import Relation.Binary.Core using (Rel; REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary.Decidable using (True; False; _×-dec_; Dec; yes; no; toWitness; fromWitness; fromWitnessFalse; toWitnessFalse)
open import Relation.Unary using (Pred; Decidable)

infixr 5 _-→_

data Type : Set where
  var : String → Type
  _-→_ : Type → Type → Type

module TypeEq where
  infix 0 _≟_

  _≟_ : DecidableEquality Type
  var x ≟ var x₁ with x String.≟ x₁
  ... | yes refl = yes refl
  ... | no  ¬p   = no λ{ refl → ¬p refl }
  var x ≟ y -→ y₁ = no λ ()
  x -→ x₁ ≟ var x₂ = no λ ()
  x -→ x₁ ≟ y -→ y₁ with x ≟ y | x₁ ≟ y₁
  ... | yes refl | yes refl = yes refl
  ... | no  ¬p   | _        = no λ { refl → ¬p refl }
  ... | _        | no ¬p    = no λ { refl → ¬p refl }


infixl 5 λ[_∶_],_
infixl 6 _[_]

data Lambda : Set where
  var : String → Lambda
  _[_] : Lambda → Lambda → Lambda
  λ[_∶_],_ : String → Type → Lambda → Lambda

instance
  typeIsString : IsString Type
  IsString.from-string typeIsString = Type.var

  lambdaIsString : IsString Lambda
  IsString.from-string lambdaIsString = Lambda.var

_ : "a" -→ "b" -→ "c" ≡ "a" -→ ("b" -→ "c")
_ = refl

_ : λ[ "x" ∶ "y" ], λ[ "z" ∶ "u" ], "x" [ "z" ] ≡ λ[ "x" ∶ "y" ], (λ[ "z" ∶ "u" ], "x" [ "z" ])
_ = refl

IsVar : Pred Lambda 0ℓ
IsVar (var x) = ⊤
IsVar (x [ x₁ ]) = ⊥
IsVar (λ[ x ∶ x₁ ], x₂) = ⊥

is-var? : Decidable IsVar
is-var? (var x) = yes tt
is-var? (x [ x₁ ]) = no λ()
is-var? (λ[ x ∶ x₁ ], x₂) = no λ()

infix 2 _∶_

infix 2 _⦂_

record Statement : Set where
  constructor _∶_
  field
    term : Lambda
    type : Type

record Declaration : Set where
  constructor _⦂_
  field
    name : String
    type : Type

decl-to-statement : Declaration → Statement
decl-to-statement (M ⦂ σ) = var M ∶ σ

statement-to-decl : (st : Statement) → {True (is-var? (Statement.term st))} →  Declaration
statement-to-decl (var x₁ ∶ type) = x₁ ⦂ type

module DeclEqual where
  open import Relation.Binary.PropositionalEquality.Properties renaming (decSetoid to isDecSetoid)

  _≟_ : DecidableEquality Declaration
  (name ⦂ type) ≟ (name₁ ⦂ type₁) with name String.≟ name₁ | type TypeEq.≟ type₁
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ{ refl → ¬p refl }
  ... | _        | no ¬p    = no λ{ refl → ¬p refl }

  decSetoid : DecSetoid 0ℓ 0ℓ
  decSetoid = isDecSetoid _≟_


module SameName where
  infix 0 _≈_

  data _≈_ : Declaration → Declaration → Set where
    eq : ∀ {x y 𝕥₁ 𝕥₂} → x String.≈ y → (x ⦂ 𝕥₁) ≈ (y ⦂ 𝕥₂)

  ≈-refl : ∀ {x} → x ≈ x
  ≈-refl {x ⦂ _} = eq (String.≈-refl {x})

  ≈-sym : ∀ {x y} → x ≈ y → y ≈ x
  ≈-sym {x ⦂ _} {y ⦂ _} (eq x≈y) = eq (String.≈-sym {x} {y} x≈y)

  ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans {x ⦂ _} {y ⦂ _} {z ⦂ _} (eq x≈y) (eq y≈z) =
    eq (String.≈-trans {x} {y} {z} x≈y y≈z)

  infix 0 _≈?_

  _≈?_ : Decidable₂ _≈_
  (x ⦂ _) ≈? (y ⦂ _) with x String.≈? y
  ... | yes p = yes (eq p)
  ... | no ¬p = no (λ{(eq p) → ¬p p})

  equivalence : IsEquivalence _≈_
  IsEquivalence.refl equivalence = ≈-refl
  IsEquivalence.sym equivalence = ≈-sym
  IsEquivalence.trans equivalence = ≈-trans

  decEquivalence : IsDecEquivalence _≈_
  IsDecEquivalence.isEquivalence decEquivalence = equivalence
  IsDecEquivalence._≟_ decEquivalence = _≈?_

  decSetoid : DecSetoid 0ℓ 0ℓ
  DecSetoid.Carrier decSetoid = Declaration
  DecSetoid._≈_ decSetoid = _≈_
  DecSetoid.isDecEquivalence decSetoid = decEquivalence

open import Data.List.Relation.Unary.Unique.DecSetoid SameName.decSetoid using (unique?)
open import Data.List.Membership.DecSetoid DeclEqual.decSetoid using (_∈_; _∈?_)


Context : Set
Context = List Declaration

infixl 1 _,_

⟦_⟧ : Declaration → Context
⟦_⟧ = _∷ []

_,_ : Context → Declaration → Context
x , x₁ = x₁ ∷ x

∅ : Context
∅ = []

data _⊢_ : Context → Statement → Set where
  var  : ∀ {Γ x σ}
      → {True ((x ⦂ σ) ∈? Γ)}
      → Γ ⊢ decl-to-statement (x ⦂ σ)

  appl : ∀ {Γ M N σ τ}
      → Γ ⊢ (M ∶ σ -→ τ)
      → Γ ⊢ (N ∶ σ)
      → Γ ⊢ (M [ N ] ∶ τ)

  abst : ∀ {Γ x σ M τ}
      → (Γ , x ⦂ σ) ⊢ (M ∶ τ)
      → Γ ⊢ (λ[ x ∶ σ ], M ∶ σ -→ τ)

y : String
y = "y"

z : String
z = "z"

α : Type
α = "α"

β : Type
β = "β"

_ : List Declaration
_ = ⟨ ("y" ⦂ α -→ β) , (z ⦂ α) ⟩

fst : (⟦ "y" ⦂ α -→ β ⟧ , z ⦂ α) ⊢ ("y" ∶ α -→ β)
fst = var

snd : (⟦ "y" ⦂ α -→ β ⟧ , z ⦂ α) ⊢ ("z" ∶ α)
snd = var

third : (⟦ "y" ⦂ α -→ β ⟧ , z ⦂ α) ⊢ ("y" [ "z" ] ∶ β)
third = appl fst snd

fourth : (⟦ "y" ⦂ α -→ β ⟧) ⊢ (λ[ "z" ∶ α ], "y" [ "z" ] ∶ α -→ β)
fourth = abst third

_ : ∅ ⊢ (λ[ "y" ∶ α -→ β ], (λ[ "z" ∶ α ], "y" [ "z" ]) ∶ (α -→ β) -→ α -→ β )
_ = abst fourth

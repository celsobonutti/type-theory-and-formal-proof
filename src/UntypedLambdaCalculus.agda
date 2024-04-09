module UntypedLambdaCalculus where

open import Data.Char using (Char)
open import Data.List as List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_; ∃)
open import Data.String as String using (String; _++_) renaming (_≈_ to _≈ₛ_; _≈?_ to _≈ₛ?_)
open import Data.String.Properties renaming (≈-sym to ≈ₛ-sym; ≈-refl to ≈ₛ-refl; ≈-trans to ≈ₛ-trans)
open import Data.Unit using (⊤; tt)
open import Function.Base using (_∘_; id)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (DecidableEquality) renaming (Decidable to Decidable₂)
open import Relation.Binary.Core using (Rel; REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary.Decidable using (True; False; _×-dec_; Dec; yes; no; toWitness; fromWitness; fromWitnessFalse; toWitnessFalse)
open import Relation.Unary using (Pred)
open import Relation.Nullary.Negation
open import StrSet
open import StrMap as Map using () renaming (Map to StrMap)

infix 5 λ'_⇒_
infixl 6 _[_]

data Lambda : Set where
  var : String → Lambda
  λ'_⇒_ : String → Lambda → Lambda
  _[_] : Lambda → Lambda → Lambda

record IsString (A : Set) : Set where
  field
    from-string : String → A

instance
  stringIsString : IsString String
  IsString.from-string stringIsString = id

  lambdaIsString : IsString Lambda
  IsString.from-string lambdaIsString = var

open IsString ⦃...⦄ public using (from-string)

{-# BUILTIN FROMSTRING from-string #-}

Map : Set
Map = StrMap Lambda

_ : "x" [ "y" ] [ "z"  ] ≡ ("x" [ "y" ]) [ "z" ]
_ = refl

_ : λ' "x" ⇒ "x" [ "y" ] ≡ λ' "x" ⇒ ("x" [ "y" ])
_ = refl

_ : Lambda
_ = λ' "x" ⇒ "x"

_ : Lambda
_ = (λ' "x" ⇒ "x") [ "y" ]

infix 0 _≈_
data _≈_ : Rel Lambda 0ℓ where
  var-eq : ∀ {x y} → x ≈ₛ y → var x ≈ var y
  abs-eq : ∀ {x y l₁ l₂} → x ≈ₛ y → l₁ ≈ l₂ → λ' x ⇒ l₁ ≈ λ' y ⇒ l₂
  app-eq : ∀ {f g x y} → f ≈ g → x ≈ y → f [ x ] ≈ g [ y ]

≈-refl : ∀ {x} → x ≈ x
≈-refl {var x} = var-eq (≈ₛ-refl {x})
≈-refl {λ' x ⇒ x₁} = abs-eq (≈ₛ-refl {x}) ≈-refl
≈-refl {x [ x₁ ]} = app-eq ≈-refl ≈-refl

≈-sym : ∀ {x y} → x ≈ y → y ≈ x
≈-sym (var-eq {x} {y} p) = var-eq (≈ₛ-sym {x} {y} p)
≈-sym (abs-eq {v₁} {v₂} {l₁} {l₂} p b) = abs-eq (≈ₛ-sym {v₁} {v₂} p) (≈-sym b)
≈-sym (app-eq {f} {g} {x} {y} p b) = app-eq (≈-sym p) (≈-sym b)

≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈-trans (var-eq {x} {y} var₁) (var-eq {y} {z} var₂) = var-eq (≈ₛ-trans {x} {y} {z} var₁ var₂)
≈-trans (abs-eq {x} {y} {l₁} {l₂} p₁ b₁) (abs-eq {y} {z} {l₃} {l₄} p₂ b₂) = abs-eq (≈ₛ-trans {x} {y} {z} p₁ p₂) (≈-trans b₁ b₂)
≈-trans (app-eq x x₁) (app-eq x₂ x₃) = app-eq (≈-trans x x₂) (≈-trans x₁ x₃)

infix 0 _≟λ_

_≟λ_ : DecidableEquality Lambda
var x ≟λ var y with x ≟ y
... | no ¬p = no λ { refl → ¬p refl }
... | yes refl = yes refl
var x ≟λ (λ' x₁ ⇒ y) = no λ ()
var x ≟λ (y [ y₁ ]) = no λ ()
(λ' x ⇒ x₁) ≟λ var x₂ = no λ ()
(λ' x ⇒ b₁) ≟λ (λ' y ⇒ b₂) with x ≟ y | b₁ ≟λ b₂
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p    = no λ {refl → ¬p refl}
... | no ¬p    | _        = no λ {refl → ¬p refl}
(λ' x ⇒ x₁) ≟λ (y [ y₁ ]) = no λ ()
(x [ x₁ ]) ≟λ var x₂ = no λ ()
(x [ x₁ ]) ≟λ (λ' x₂ ⇒ y) = no λ ()
(x [ x₁ ]) ≟λ (y [ y₁ ]) with x ≟λ y | x₁ ≟λ y₁
... | yes refl | yes refl = yes refl
... | _        | no ¬p    = no λ {refl → ¬p refl}
... | no ¬p    | _        = no λ {refl → ¬p refl}

≈-equivalence : IsEquivalence _≈_
IsEquivalence.refl ≈-equivalence = ≈-refl
IsEquivalence.sym ≈-equivalence = ≈-sym
IsEquivalence.trans ≈-equivalence = ≈-trans

FV : Lambda → StrSet
FV (var x) = singleton x
FV (λ' x ⇒ x₁) = delete x (FV x₁)
FV (x [ x₁ ]) = union (FV x) (FV x₁)

data IsClosed : Pred Lambda 0ℓ where
  closed : ∀ {x} → FV x ≋ empty → IsClosed x

data IsBinding : REL String Lambda 0ℓ where
  is-binding : ∀ {x l} → IsBinding x (λ' x ⇒ l)

is-binding? : Decidable₂ IsBinding
is-binding? x (var x₁) = no λ ()
is-binding? x (y [ y₁ ]) = no λ ()
is-binding? x (λ' x₁ ⇒ y) with x ≟ x₁
... | yes refl = yes is-binding
... | no  ¬eq  = no λ { is-binding → ¬eq refl}

rename : (x : String)
       → (y : String)
       → (original : Lambda)
       → {True (y ∉? FV original)}
       → {False (is-binding? y original)}
       → Lambda
rename x y (var z) with x ≟ z
... | yes _ = var y
... | no  _ = var z
rename x y (M [ N ]) =
  new-M [ new-N ]
  where
    new-M : Lambda
    new-M with is-binding? y M
    ... | yes _    = M
    ... | no  ¬binding with y ∉? FV M
    ... | no  _    = M
    ... | yes y∉FV = rename x y M {fromWitness y∉FV} {fromWitnessFalse ¬binding}
    new-N : Lambda
    new-N with is-binding? y N
    ... | yes _        = N
    ... | no  ¬binding with y ∉? FV N
    ... | no  _        = N
    ... | yes y∉FV     = rename x y N {fromWitness y∉FV} {fromWitnessFalse ¬binding}
rename x y (λ' z ⇒ body) with is-binding? y body | y ∉? FV body
... | yes _        | _        = (λ' z ⇒ body)
... | no  _        | no  _    = (λ' z ⇒ body)
... | no  ¬binding | yes y∉FV = (λ' z ⇒ rename x y body {fromWitness y∉FV} {fromWitnessFalse ¬binding})

infix 0 _=α_

data _=α_ : Rel Lambda 0ℓ where
  α-renaming : ∀ {x y body₁ body₂}
             → {y∉FV : True (y ∉? FV body₁)}
             → {¬binding : False (is-binding? y body₁)}
             → {body₂-is-rename : True (body₂ ≟λ rename x y body₁ {y∉FV} {¬binding})}
             → λ' x ⇒ body₁ =α λ' y ⇒ body₂
  α-compat₁ : ∀ {M N L} → M =α N → M [ L ] =α N [ L ]
  α-compat₂ : ∀ {M N L} → M =α N → L [ M ] =α L [ N ]
  α-compat₃ : ∀ {M N z} → M =α N → λ' z ⇒ M =α λ' z ⇒ N
  α-refl    : ∀ {x} → x =α x
  α-sym     : ∀ {x y} → x =α y → y =α x
  α-trans   : ∀ {x y z} → x =α y → y =α z → x =α z

exercise-3 : λ' "x" ⇒ ("x" [ λ' "z" ⇒ "y" ]) =α λ' "z" ⇒ ("z" [ λ' "z" ⇒ "y" ])
exercise-3 = α-renaming

show-subscript : ℕ → String
show-subscript = to-subscript ∘ show
  where
   to-subscript-letter : Char → Char
   to-subscript-letter '0' = '₀'
   to-subscript-letter '1' = '₁'
   to-subscript-letter '2' = '₂'
   to-subscript-letter '3' = '₃'
   to-subscript-letter '4' = '₄'
   to-subscript-letter '5' = '₅'
   to-subscript-letter '6' = '₆'
   to-subscript-letter '7' = '₇'
   to-subscript-letter '8' = '₈'
   to-subscript-letter '9' = '₉'
   to-subscript-letter x   = x
   to-subscript : String → String
   to-subscript = String.fromList ∘ List.map to-subscript-letter ∘ String.toList

record NameWithProofs (body : Lambda) (new-value : Lambda) : Set where
  field
    name : String
    ∉FVb : name ∉ FV body
    ¬binding : ¬ (IsBinding name body)
    ∉FVn : name ∉ FV new-value

{-# TERMINATING #-}
new-binding-var : (seed : String)
                → (count : ℕ)
                → (binding-var : String)
                → (subst-var : String)
                → (body : Lambda)
                → (new-value : Lambda)
                → NameWithProofs body new-value
new-binding-var seed count binding-var subst-var body new-value with new-name ← seed ++ show-subscript count
  with new-name ≟ binding-var | new-name ≟ subst-var | new-name ∉? FV body | is-binding? new-name body | new-name ∉? FV new-value
... | no _ | no _ | yes y∉FVb | no ¬binding | yes y∉FVn =
    record { name = new-name
           ; ∉FVb = y∉FVb
           ; ¬binding = ¬binding
           ; ∉FVn = y∉FVn
           }
... | _    | _    | _         | _           | _        =
    new-binding-var seed (suc count) binding-var subst-var body new-value

{-# TERMINATING #-}
_⟨_:=_⟩ : Lambda → String → Lambda → Lambda
var v ⟨ x := N ⟩ with v ≟ x
... | yes _ = N
... | no  _ = var v
(P [ Q ]) ⟨ x := N ⟩ = (P ⟨ x := N ⟩) [ Q ⟨ x := N ⟩ ]
(λ' y ⇒ M) ⟨ x := N ⟩ with
  y ≟ x
... | yes _ = λ' y ⇒ M
... | no  _ with
  y ∉? FV N
... | yes _ = λ' y ⇒ (M ⟨ x := N ⟩)
... | no  _ =
  let
    record {name = var-name ; ∉FVb = name∉FVM ; ¬binding = ¬binding ; ∉FVn = _} = new-binding-var "z" 0 y x M N
  in λ' var-name ⇒ (rename y var-name M {fromWitness name∉FVM} {fromWitnessFalse ¬binding}) ⟨ x := N ⟩

_ : (λ' "y" ⇒ "y" [ "x" ]) ⟨ "x" := "x" [ "y" ] ⟩ ≡ λ' "z₀" ⇒ "z₀" [ "x" [ "y" ] ]
_ = refl

all-free-variables : Map → StrSet
all-free-variables m = union (Map.foldr (λ x l s → union (FV l) s) empty m) empty

record NameWithProofsMulti (body : Lambda) (new-values : Map) : Set where
  field
    name : String
    ∉FVb : name ∉ FV body
    ¬binding : ¬ (IsBinding name body)
    ∉FVn : name ∉ (all-free-variables new-values)

{-# TERMINATING #-}
new-binding-var-multi : (seed : String)
                      → (count : ℕ)
                      → (binding-var : String)
                      → (body : Lambda)
                      → (new-values : Map)
                      → NameWithProofsMulti body new-values
new-binding-var-multi seed count binding-var body new-values with new-name ← seed ++ show-subscript count
  with new-name ≟ binding-var | new-name ∉? FV body | is-binding? new-name body | new-name ∉? all-free-variables new-values
... | no _ | yes y∉FVb | no ¬binding | yes y∉FVn =
    record { name = new-name
           ; ∉FVb = y∉FVb
           ; ¬binding = ¬binding
           ; ∉FVn = y∉FVn
           }
... | _    | _         | _           | _        =
           new-binding-var-multi seed (suc count) binding-var body new-values

{-# TERMINATING #-}
_⟨[_]⟩ : Lambda → Map → Lambda
var x ⟨[ m ]⟩ with Map.lookup m x
... | nothing = var x
... | just N  = N
(P [ Q ]) ⟨[ m ]⟩ = (P ⟨[ m ]⟩) [ Q ⟨[ m ]⟩ ]
(λ' y ⇒ M) ⟨[ m ]⟩ with y ∉? all-free-variables (Map.delete y m)
... | yes _ = λ' y ⇒ (M ⟨[ Map.delete y m ]⟩)
... | no  _ =
  let
    record {name = var-name; ∉FVb = name∉FVM; ¬binding = ¬binding; ∉FVn = _}
      = new-binding-var-multi "z" 0 y M (Map.delete y m)
  in λ' var-name ⇒ (rename y var-name M {fromWitness name∉FVM} {fromWitnessFalse ¬binding} ⟨[ (Map.delete y m) ]⟩)

substs : Map
substs = Map.fromList (("y" , "x") ∷ ("x" , "y") ∷ [])

_ : ("x" [ "y" ]) ⟨[ substs ]⟩ ≡ "y" [ "x" ]
_ = refl

infix 0 _≈α_

data _≈α_ : Rel Lambda 0ℓ where
  term  : ∀ {x y} → x =α y → x ≈α y
  app   : ∀ {M₁ M₂ N₁ N₂} → M₁ ≈α M₂ → N₁ ≈α N₂ → M₁ [ N₁ ] ≈α M₂ [ N₂ ]
  abs   : ∀ {x M₁ M₂} → M₁ ≈α M₂ → λ' x ⇒ M₁ ≈α λ' x ⇒ M₂
  subst : ∀ {x M₁ M₂ N₁ N₂} → M₁ ≈α M₂ → N₁ ≈α N₂ → M₁ ⟨ x := N₁ ⟩ ≈α M₂ ⟨ x := N₂ ⟩

U : Lambda
U = (λ' "z" ⇒ "z" [ "x" ] [ "z" ])
        [ (λ' "y" ⇒ "x" [ "y" ]) [ "x" ] ]

V : Lambda
V = (λ' "y" ⇒ "y" [ "x" ] [ "y" ])
        [ (λ' "z" ⇒ "x" [ "z" ]) [ "x" ] ]

W : Lambda
W = (λ' "x" ⇒ "x" [ "y" ] [ "x" ])
        [ (λ' "z" ⇒ "y" [ "z" ]) [ "y" ] ]

X : Lambda
X = (λ' "y" ⇒ "y" [ "x" ] [ "y" ])
        [ (λ' "z" ⇒ "x" [ "z" ]) [ "x" ] ]

_ : U ≈α V
_ = app (term α-renaming) (app (term α-renaming) (term α-refl))

_ : U ≈α X
_ = app (term α-renaming) (app (term α-renaming) (term α-refl))

-- ¬ (W ≈α X) because free variables were renamed

a-15 : (λ' "x" ⇒ "y" [ λ' "y" ⇒ "x" [ "y" ] ] ) ⟨ "y" := λ' "z" ⇒ "z" [ "x" ] ⟩
      ≡ λ' "z₀" ⇒ (λ' "z" ⇒ "z" [ "x" ]) [ λ' "y" ⇒ "z₀" [ "y" ] ]
a-15 = refl

b-15 : (("x" [ "y" ] [ "z" ]) ⟨ "x" := "y" ⟩) ⟨ "y" := "z" ⟩ ≡ "z" [ "z" ] [ "z" ]
b-15 = refl

c-15 : ((λ' "x" ⇒ "x" [ "y" ] [ "z" ]) ⟨ "x" := "y" ⟩) ⟨ "y" := "z" ⟩ ≡ λ' "x" ⇒ "x" [ "z" ] [ "z" ]
c-15 = refl

d-15 : (λ' "y" ⇒ "y" [ "y" ] [ "x" ]) ⟨ "x" := "y" [ "z" ] ⟩ ≡ λ' "z₀" ⇒ "z₀" [ "z₀" ] [ "y"  [ "z" ] ]
d-15 = refl

ex-16 : {x : Lambda} → ∃ (λ x → ¬ (x ⟨ "y" := "x"⟩) ⟨ "x" := "y" ⟩ ≡ (x ⟨[ substs ]⟩) )
ex-16 = v , not-eq
  where
    v : Lambda
    v = "x" [ "y" ]
    not-eq : ¬ ((v ⟨ "y" := "x"⟩) ⟨ "x" := "y" ⟩ ≡ (v ⟨[ substs ]⟩))
    not-eq with no p ← (v ⟨ "y" := "x"⟩) ⟨ "x" := "y" ⟩ ≟λ v ⟨[ substs ]⟩ = p

infixl 0 _→ᵦ_

data _→ᵦ_ : Rel Lambda 0ℓ where
  β-base : ∀ {x M N} → (λ' x ⇒ M) [ N ] →ᵦ M ⟨ x := N ⟩
  β-compat₁ : ∀ {M N L} → M →ᵦ N → M [ L ] →ᵦ N [ L ]
  β-compat₂ : ∀ {M N L} → M →ᵦ N → L [ M ] →ᵦ L [ N ]
  β-compat₃ : ∀ {M N z} → M →ᵦ N → (λ' z ⇒ M) →ᵦ (λ' z ⇒ N)

infix 0 _→ᵦ[_]_

-- Multi-step β-reduction

data _→ᵦ[_]_ : Lambda → ℕ → Lambda → Set where
  β-refl : ∀ {x} → x →ᵦ[ 0 ] x
  β-one-step : ∀ {M N} → M →ᵦ N → M →ᵦ[ 1 ] N
  β-multi-step : ∀ {M N P m n} → M →ᵦ[ m ] N → N →ᵦ[ n ] P → M →ᵦ[ m + n ] P

term₁ : Lambda
term₁ = λ' "x" ⇒ "x"

term₂ : Lambda
term₂ = term₁ [ "y" ]

term₃ : Lambda
term₃ = term₂ [ "z" ]

term₄ : Lambda
term₄ = (λ' "x" ⇒ "x") [ (λ' "z" ⇒ "x") [ "y" ] ]

_ : term₂ →ᵦ "y"
_ = β-base

_ : term₃ →ᵦ "y" [ "z" ]
_ = β-compat₁ β-base

_ : term₁ →ᵦ[ 0 ] λ' "x" ⇒ "x"
_ = β-refl

p₁ : (λ' "x" ⇒ "x") [ (λ' "z" ⇒ "x") [ "y" ] ] →ᵦ[ 1 ] (λ' "x" ⇒ "x") [ "x" ]
p₁ = β-one-step (β-compat₂ β-base)

_ : term₄ →ᵦ[ 2 ] "x"
_ = β-multi-step p₁ (β-one-step β-base)

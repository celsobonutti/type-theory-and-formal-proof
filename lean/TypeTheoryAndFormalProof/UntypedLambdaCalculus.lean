import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.InferParam
import Batteries.Data.HashMap.Basic
import Batteries.Data.RBMap

open Set
open Batteries

inductive Lam : Type where
  | var : String → Lam
  | app : Lam → Lam → Lam
  | abs : String → Lam → Lam
  deriving Repr, BEq, DecidableEq

@[simp]
def Lam.size : Lam → Nat
  | var _ => 1
  | app f x => f.size + x.size
  | abs _ body => 1 + body.size

open Lam

#check Lam.var "x"

instance : Coe String Lam where
  coe := Lam.var

def Lam.free_variables (term : Lam) : Set String :=
  match term with
  | var x => {x}
  | app f x => f.free_variables ∪ x.free_variables
  | abs x body => body.free_variables \ {x}

def test : Set String := { "memes" }

instance decidableFreeVariable {a : String} {term : Lam} : Decidable (a ∈ free_variables term) := by
  cases term with
  | var x => simp [free_variables]; exact decEq a x
  | app f x => simp [free_variables];
               have _ : Decidable (a ∈ free_variables f) := decidableFreeVariable
               have _ : Decidable (a ∈ free_variables x) := decidableFreeVariable
               apply Or.decidable;
  | abs x body => simp [free_variables];
                  have _ : Decidable (a ∈ free_variables body) := decidableFreeVariable
                  apply And.decidable;

example : "x" ∈ (var "x").free_variables := by decide

inductive IsBinding : String → Lam → Prop where
  | is_binding (x : String) {term : Lam} : IsBinding x (abs x term)

variable {x a : String} {body : Lam}
theorem binding_means_eq : IsBinding x (abs a body) → a = x
  | IsBinding.is_binding x => rfl

instance decidableBinding {a : String} {t : Lam} : Decidable (IsBinding a t) := by
  cases t with
  | var _ =>
      apply Decidable.isFalse; intro; contradiction
  | app _ _ =>
      apply Decidable.isFalse; intro; contradiction
  | abs x body =>
    if is_eq : x = a then
      apply Decidable.isTrue; rw [is_eq]; exact IsBinding.is_binding a
    else
      apply Decidable.isFalse; intro h₁; have := binding_means_eq h₁; contradiction

@[simp]
def rename (x y : String)
           (original : Lam)
           (_ : y ∉ original.free_variables ∧ ¬IsBinding y original
             := by (first | assumption | decide | (constructor; assumption; assumption)))
           : Lam :=
  match original with
  | var z =>
    if x = z then var y else var z
  | app m n =>
    let new_m :=
      if _ : y ∉ m.free_variables ∧ ¬(IsBinding y m)
        then rename x y m
        else m
    let new_n :=
      if _ : y ∉ n.free_variables ∧ ¬(IsBinding y n)
        then rename x y n
        else n
    app new_m new_n
  | abs var_name body =>
    if _ : y ∉ body.free_variables ∧ ¬(IsBinding y body)
      then abs var_name (rename x y body)
      else abs var_name body

theorem rename_same_size (og new : String) (term : Lam)
           (p : new ∉ term.free_variables ∧ ¬IsBinding new term
             := by (first | assumption | decide | (constructor; assumption; assumption)))
 : (rename og new term).size = term.size := by
  induction term with
  | var _ => simp [rename, Lam.size]; split; repeat simp

  | abs var_name body ih_body =>
                         simp [rename, Lam.size]
                         split
                         case inl h =>
                           simp [Lam.size]
                           have eq := ih_body h
                           rw [eq]
                         case inr h =>
                           simp [Lam.size]

  | app f x ih_f ih_x => simp [rename, Lam.size]
                         split
                         case inl h =>
                           have same_size := ih_f h
                           rw [same_size]
                           split
                           case inl h =>
                             have same_size := ih_x h
                             rw [same_size]
                           case inr h => rfl
                         case inr h =>
                           split
                           case inl h =>
                             have same_size := ih_x h
                             rw [same_size]
                           case inr h => rfl

inductive α_eq : Lam → Lam → Prop where
  | α_renaming : ∀ {x y b₁ b₂}
                   (p₁ : y ∉ b₁.free_variables := by decide)
                   (p₂ : ¬(IsBinding y b₁)     := by decide)
                   (_ : b₂ = rename x y b₁     := by decide),
                   α_eq (abs x b₁) (abs y b₂)
  | α_compat₁  : ∀ {m n l}, α_eq m n → α_eq (app m l) (app n l)
  | α_compat₂  : ∀ {m n l}, α_eq m n → α_eq (app l m) (app l n)
  | α_compat₃  : ∀ {m n z}, α_eq m n → α_eq (abs z m) (abs z n)
  | α_refl     : ∀ {term}, α_eq term term

infix:50 "α=" => α_eq

open α_eq

example : abs "x" (app "x" (abs "z" "y")) α= abs "z" (app "z" (abs "z" "y")) := by
    constructor <;> repeat (first | simp | infer_param)

example : abs "x" (app "x" (abs "z" "y")) α= abs "z" (app "z" (abs "z" "y")) := by
  exact α_renaming

structure NameWithProofs (body : Lam) (new_value : Lam) : Type where
  name : String
  not_free_body : name ∉ body.free_variables
  not_bind_body : ¬ (IsBinding name body)
  not_free_new  : name ∉ new_value.free_variables

axiom exists_variable (seed binding_var subst_var : String) (body new_value : Lam) : ∃ (x : Nat),
  have new_var := s!"{seed}{x}"
  ((new_var ≠ binding_var) ∧ (new_var ≠ subst_var)) ∧ ((new_var ∉ body.free_variables ∧ ¬(IsBinding new_var body) ∧ new_var ∉ new_value.free_variables))


def new_binding_var
  (seed : String)
  (binding_var : String)
  (subst_var : String)
  (body : Lam)
  (new_value : Lam) :
  NameWithProofs body new_value :=
    let ⟨number, ⟨_, p⟩, _⟩ := Nat.findX (exists_variable seed binding_var subst_var body new_value)
    NameWithProofs.mk s!"{seed}{number}" p.left p.right.left p.right.right

theorem size_bigger_than_zero : ∀ (t : Lam), t.size > 0 := by
  intro t
  cases t with
  | var x => simp [Lam.size]
  | app m n => simp [Lam.size]
               have hₘ : 0 < m.size := size_bigger_than_zero m
               have hₙ : 0 < n.size := size_bigger_than_zero n
               apply Nat.add_lt_add hₘ hₙ
  | abs x t => simp [Lam.size, Nat.add_comm]


theorem left_smaller : ∀ {m n}, size m < size m + size n := by
  intro m n
  have hₙ := size_bigger_than_zero n
  apply Nat.lt_add_of_pos_right hₙ

def Lam.replace (original : Lam) (new_var : String) (new_term : Lam) : Lam :=
  match original with
  | var v => if v = new_var then new_term else var v
  | app p q => app (replace p new_var new_term) (replace q new_var new_term)
  | abs v t =>
    if v = new_var
    then abs v t
    else if v ∉ new_term.free_variables
    then abs v (replace t new_var new_term)
    else
      let fresh_name := new_binding_var "z" v new_var t new_term
      have l := fresh_name.not_bind_body
      have r := fresh_name.not_free_body
      abs (fresh_name.name) (replace (rename v fresh_name.name t) new_var new_term)
      termination_by original.size
      decreasing_by
        all_goals simp_wf
        . apply left_smaller
        . rw [Nat.add_comm]; apply left_smaller
        . rw [Nat.add_comm]; apply Nat.lt.base
        . rw [@rename_same_size, Nat.add_comm]; apply Nat.lt.base


namespace List
  def all_free_variables (x : List (String × Lam)) : Set String :=
    match x with
    | [] => ∅
    | (x :: xs) => free_variables x.snd ∪ all_free_variables xs

  theorem belongs_left {a : String} {term : Lam} {name : String} {other : List (String × Lam)} : a ∈ term.free_variables → a ∈ all_free_variables ((name, term) :: other) := by
    intro h
    simp [all_free_variables]
    apply Or.inl
    exact h

  theorem belongs_right {a : String} {term : Lam} {name : String} {other : List (String × Lam)} : a ∈ (all_free_variables other) → a ∈ all_free_variables ((name, term) :: other) := by
    intro h
    simp [all_free_variables]
    apply Or.inr
    exact h

  theorem belongs_to_one {a : String} {term : Lam} {name : String} {other : List (String × Lam)}
    :  a ∈ all_free_variables ((name, term) :: other)
    → a ∈ term.free_variables ∨ a ∈ all_free_variables other := by
    intro h
    cases h with
    | inl h₁ => apply Or.inl; exact h₁
    | inr h₂ => apply Or.inr; exact h₂

  instance decidableFreeVariables {a : String} {terms : List (String × Lam)} : Decidable (a ∈ all_free_variables terms) := by
    cases terms with
    | nil => apply isFalse; simp [all_free_variables]
    | cons x xs => by_cases h : a ∈ x.snd.free_variables
                   case pos =>
                    apply isTrue; apply belongs_left h
                   case neg =>
                    have := @decidableFreeVariables a xs
                    by_cases hs : a ∈ all_free_variables xs
                    case pos => apply isTrue; apply belongs_right hs
                    case neg => apply isFalse; intro h_both; cases belongs_to_one h_both <;> contradiction
end List

abbrev Map := RBMap String Lam compare

def all_free_variables (x : Map) : Set String :=
  x |> RBMap.toList |> List.all_free_variables

instance decidableMapFreeVariables₁ {a : String} {terms : Map} : Decidable (a ∈ all_free_variables terms) := by
  exact List.decidableFreeVariables

def names : Map → List String := List.map Prod.fst ∘ RBMap.toList

axiom exists_variable_multi (seed binding_var : String) (subst_vars : Map) (body : Lam) : ∃ (x : Nat),
  have new_var := s!"{seed}{x}"
  ((new_var ≠ binding_var ∧ new_var ∉ names subst_vars) ∧ new_var ∉ body.free_variables ∧ ¬(IsBinding new_var body) ∧ new_var ∉ all_free_variables subst_vars)

structure NameWithProofsMulti (body : Lam) (new_values : Map) : Type where
  name : String
  not_free_body : name ∉ body.free_variables
  not_bind_body : ¬ (IsBinding name body)
  not_free_new  : name ∉ all_free_variables new_values

def new_binding_var_multi
  (seed binding_var : String)
  (body : Lam)
  (subst_vars : Map) :
  NameWithProofsMulti body subst_vars :=
    let ⟨number, ⟨_, p⟩, _⟩ := Nat.findX (exists_variable_multi seed binding_var subst_vars body)
    NameWithProofsMulti.mk s!"{seed}{number}" p.left p.right.left p.right.right

def Lam.replace_multi (original : Lam) (subst_vars : Map) : Lam :=
  match original with
  | var x =>
    match subst_vars.find? x with
    | Option.none => var x
    | Option.some y => y
  | app p q => app (p.replace_multi subst_vars) (q.replace_multi subst_vars)
  | abs y m =>
    if y ∉ all_free_variables (subst_vars.erase y)
    then abs y (m.replace_multi (subst_vars.erase y))
    else
      let fresh_name := new_binding_var_multi "z" y m subst_vars
      have l := fresh_name.not_bind_body
      have r := fresh_name.not_free_body
      abs (fresh_name.name) ((rename y fresh_name.name m).replace_multi subst_vars)
      termination_by original.size
      decreasing_by
        all_goals simp_wf
        . apply left_smaller
        . rw [Nat.add_comm]; apply left_smaller
        . rw [Nat.add_comm]; apply Nat.lt.base
        . rw [@rename_same_size, Nat.add_comm]; apply Nat.lt.base

instance {α β : Type} [Ord α] : Coe (List (α × β)) (RBMap α β compare) where
  coe x := List.toRBMap x compare

example :
  (app "x" "y").replace_multi ([("y", var "x"), ("x", var "y")]) = app "y" "x" := rfl

inductive α_equiv : Lam → Lam → Prop where
  | term  : ∀ {x y}, x α= y → α_equiv x y
  | app   : ∀ {m₁ m₂ n₁ n₂}, α_equiv m₁ m₂ → α_equiv n₁ n₂ → α_equiv (app m₁ n₁) (app m₂ n₂)
  | abs   : ∀ {x m₁ m₂}, α_equiv m₁ m₂ → α_equiv (abs x m₁) (abs x m₂)
  | subst : ∀ {x m₁ m₂ n₁ n₂}, α_equiv m₁ m₂ → α_equiv n₁ n₂ → α_equiv (m₁.replace x n₁) (m₂.replace x n₂)

infix:50 "α≈" => α_eq

-- namespace Exercise
--   def U : Lam :=
--     app (abs "z" (app ))
-- end Exercise

example : ¬(∃ (x : Nat), ∀ (y : Nat), x > y) :=
  λ ⟨x, f⟩ =>
    have x_is_bigger_than_succ := f (Nat.succ x)
    have x_is_smaller_than_succ : ¬x > x.succ := Nat.not_lt_of_lt Nat.le.refl
    absurd x_is_bigger_than_succ x_is_smaller_than_succ

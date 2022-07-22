
example (p q r : Prop) (hp : p) : q ∨ p ∨ r :=
  by repeat (first |apply Or.inl; assumption | apply Or.inr | assumption)
 example (p q r : Prop) (hp : p)
         : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat(any_goals (first | apply And.intro | apply Or.inl; assumption | apply Or.inr | assumption))
 
variable (x y : Nat)

def double := x + x
#eval Lean.versionString

#check double y
#check Nat.succ_ne_zero

inductive Weekday where 
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

open Weekday

#eval sunday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl 
def next_previous (d : Weekday) : next (previous d) = d := by 
  cases d <;> rfl

def and1 ( a b : Bool) : Bool := 
  match a with 
  | true => b
  | false => false

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat ) p (fun b n => cond b (2 * n) (2*n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

def fst {α : Type u} {β : Type v} {p : Prod α β} : α := 
  match p with 
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β ) : β := 
  match p with 
  | Prod.mk a b => b

def sum_example (s : Sum Nat Nat) : Nat := 
Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)
namespace Hidden 
structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
inductive Sigma {α : Type u} ( β : α → Type v) where 
  | mk : (a : α) → β a → Sigma β 
inductive Option (α : Type u) where 
  | none : Option α 
  | some : α → Option α 

inductive False : Prop
end Hidden

structure Color where 
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0
#eval Color.red yellow

structure semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc
       0 + succ n = succ (0 + n) := rfl
                _ = succ n       := by rw [ih])
theorem add_assoc ( m n k : Nat) : m + n + k = m + (n + k) := 
  Nat.recOn (motive := fun k => m + n + k = m + (n + k) ) k 
    rfl 
    (fun k ih => by simp [Nat.add_succ, ih])

end Hidden

open Nat 
theorem zero_add (n : Nat) : 0 + n = n := 
  Nat.recOn (motive := fun x => 0 + x = x) n
  rfl 
  (fun n ih => by simp [add_succ, ih])
namespace hidden
theorem succ_add (m n : Nat) : succ n + m = succ (n + m) := 
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl 
    (fun m ih => by simp only [add_succ, ih])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    (fun m ih => by simp only [add_succ, succ_add, ih])
end hidden

namespace Hidden
inductive List (α : Type u) where
| nil : List α 
| cons : α → List α → List α 

namespace List
def append (as bs : List α) : List α := 
  match as with 
  | nil => bs 
  | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as := 
  rfl 

theorem cons_append (a : α) (as bs : List α)
          : append (cons a as) bs = cons a (append as bs) := 
          rfl 
#check @List.recOn
theorem append_nil (as : List α) : append as nil = as := 
  List.recOn  (motive := fun x => append x nil = x) as
    rfl 
    (fun a as ih => by simp [cons_append, ih]
    )
#print append_nil
theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn (motive := fun as => append (append as bs) cs = append as (append bs cs)) as
    rfl 
    (fun a as ih => by simp [cons_append, ih]) 
def length (as : List α) : Nat := 
  match as with
  | nil => 0
  | cons a as => 1 + length as

attribute [simp] append_nil
attribute [simp] append_assoc
attribute [simp] cons_append

theorem length_sum (as bs : List α) : length (append as bs) = length as + length bs :=
  List.recOn (motive := fun as => length (append as bs) = length as + length bs) as 
    (show length (append nil bs) = length nil + length bs from 
      calc length (append nil bs) = length bs := rfl
              _ = 0 + length bs := by rw[ Nat.zero_add]
              _ = length nil + length bs := rfl
    ) 
    (fun a as ih =>
    calc length (append (cons a as) bs) = length (cons a (append as bs)) := by rw[cons_append]
          _ = 1 + length ( append as bs) := rfl
          _ = 1 + (length as + length bs) := by simp[ih] 
          _ = (1 + length as) + length bs := by simp[Nat.add_assoc]
          _ = length (cons a as) + length bs := rfl
    )
inductive BinaryTree where 
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

inductive CBTree where
end List
end Hidden 

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : ℕ ⊢ p (succ a)

example (n : Nat) (h : n ≠  0) : succ (pred n) = n := by 
  cases n with 
  | zero =>
    apply absurd rfl h 
  | succ m => 
  rfl

def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl

def Tuple (α : Type) (n : Nat) := 
{ as : List α // as.length = n}
def fr {n :Nat} {t : Tuple α n} : Nat := by 
  cases n ; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
⟨ [0,1,2], rfl ⟩ 

inductive Foo where 
| bar1 : Nat → Nat → Foo
| bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by 
  cases x with 
  | bar2 c d e => exact e
  | bar1 a b => exact b

open Nat 
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n , p (succ n)) (m k : Nat) : p (m + 3 * k) := by 
  generalize m + 3 * k = n 
  cases n 
  exact hz 
  apply hs

example (p : Prop) (m n : Nat) (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by 
  cases Nat.lt_or_ge m n 
  case inl hlt => exact h₁ hlt 
  case inr glt => exact h₂ glt

  #check Nat.sub_self
  example (m n : Nat) : m - n = 0 ∨ m ≠ n := by 
    cases Decidable.em (m = n) with 
    | inl heq => rw [heq] ; apply Or.inl; exact Nat.sub_self n 
    | inr hne => apply Or.inr; exact hne 
namespace Hidden1
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
end Hidden1

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by 
  induction x, y using Nat.mod.inductionOn with 
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with 
    | Or.inl h₁ => exact absurd h h₁ 
    | Or.inr h₁ => 
      have hgt : y > x := Nat.gt_of_not_le h₁ 
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption


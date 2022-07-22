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

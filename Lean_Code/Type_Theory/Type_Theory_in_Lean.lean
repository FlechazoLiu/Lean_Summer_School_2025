import Mathlib

-- set_option pp.all true
#check (1 : Nat)

universe u
#check Type u

example : 641 = 641 := Eq.refl _

variable (A B C : Type u) (a : A) (b : B) (c : C) (p : A → B → C)
#check A → B → C
#check p
#check p a

def g : A → B :=
  fun _ => b

  -- Constructors
  -- Eliminators
  -- Computation rules

variable (x : ℝ )
example (a : ℝ) : (fun x ↦ x ^ 2) a = a ^ 2 := rfl

def h : ℕ → ℕ :=
  fun _ => 0

#print Prod.rec
variable (A B C : Type u) (f : A → B → C) (a : A) (b : B)
example : Prod.rec f (a, b) = f a b := rfl

#check (Prod.fst : A × B → A)


variable (P : Prop) (p : P)
example : P := p

theorem easy : 1 + 1 = 2 := by
  rfl

example : easy = by rfl := rfl

#check easy

universe v
variable (A : Type u) (B : Type v)
#check A → B

example : Π (n : ℕ), n = n := by
  intro n
  rfl

example : ∀ (n : ℕ), n = n := by
  intro n
  rfl


variable (P Q : Prop)
#check P → Q

example (p : P) (h : P → Q) : Q := h p

#check And.elim

#check And.intro

#check And.rec -- ?

#check Or.elim

#check Or.intro_right

#check Or.intro_left


#check True

example : True := by
  trivial

#check False.elim


#check mul_eq_zero

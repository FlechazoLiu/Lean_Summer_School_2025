/- In fact, in Lean's library, every concrete type other than the universes and every type constructor other than dependent arrows is an instance of a general family of type constructions known as inductive types.

Intuitively, an inductive type is built up from a specified list of `constructors`. In Lean, the syntax for specifying such a type is as follows:

inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo

The intuition is that each constructor specifies a way of building new objects of Foo, possibly from previously constructed values. The type Foo consists of nothing more than the objects that are constructed in this way.
 -/

inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
deriving Repr

inductive Weekday' where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday

#check Weekday'.sunday
#check Weekday.rec


open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday
#eval numberOfDay Weekday.monday
#eval numberOfDay Weekday.tuesday

-- set_option pp.all true
#print numberOfDay

/- When declaring an inductive datatype, you can use deriving Repr to instruct Lean to generate a function that converts Weekday objects into text. This function is used by the #eval command to display Weekday objects. If no Repr exists, #eval attempts to derive one on the spot. -/

namespace Weekday
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

#check sunday
#eval next (next tuesday)
#eval next (previous tuesday)
example : next (previous tuesday) = tuesday :=
  rfl
end Weekday

theorem next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

theorem next_previous' (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl


#print Prod.casesOn
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

def prod_example' (p : Bool × Nat) : Nat :=
  match p.fst with
  | true => 2 * p.snd
  | false => 2 * p.snd + 1

example (x : Bool × Nat) : prod_example x = prod_example' x := by rfl


/- This example simultaneously introduces the inductive type, Prod, its constructor, mk, the usual eliminators (rec and recOn), as well as the projections, fst and snd, as defined above. -/
namespace Hidden
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

#print Prod
end Hidden


/- The `cases` tactic works on elements of an inductively defined type, and does what the name suggests: it decomposes the element according to each of the possible constructors. In its most basic form, it is applied to an element x in the local context. It then reduces the goal to cases in which x is replaced by each of the constructions. -/
example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (Nat.succ n)) :
    ∀ n, p n := by
  intro n
  cases n
  . exact hz
  . apply hs

/- For one thing, cases allows you to choose the names for each alternative using a with clause. -/
open Nat
example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    apply absurd rfl h
  | succ m =>
    rfl

/- Notice that cases can be used to produce data as well as prove propositions. -/
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 10 = 7 := rfl

/- The syntax of the with is convenient for writing structured proofs. Lean also provides a complementary case tactic, which allows you to focus on goal assign variable names. -/
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
def silly (x : Foo) : Nat := by
  cases x
  case bar1 _ b => exact b
  case bar2 _ _ e => exact e


/- You can also use cases with an arbitrary expression.  -/
open Nat
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz
  apply hs


/-If the expression you case on does not appear in the goal, the cases tactic uses have to put the type of the expression into the context. Here is an example:-/
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge


namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
end Hidden

/-As a convenience, pattern-matching has been integrated into tactics such as intro and funext.-/
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]

/- We close this section with one last tactic that is designed to facilitate working with inductive types, namely, the `injection` tactic. -/

/-By design, the elements of an inductive type are freely generated, which is to say, the constructors are injective and have disjoint ranges. The injection tactic is designed to make use of this fact:-/
example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

/- The injection tactic also `detects contradictions` that arise when different constructors are set equal to one another, and uses them to close the goal. -/
example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction




-- inductive type
-- structue
-- class & instance

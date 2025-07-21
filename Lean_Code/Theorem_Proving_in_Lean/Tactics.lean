#check And.intro
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · apply hq
    · exact hp

#print test

theorem test₁ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

theorem test₄ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases h2 with h3 | h4
    · left; exact And.intro h1 h3
    · right; exact And.intro h1 h4
  · intro h
    rcases h with h1 | h2
    · exact And.intro h1.1 (Or.inl h1.2)
    · exact And.intro h2.1 (Or.inr h2.2)


example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁


example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  -- intro h
  -- rcases h with ⟨w, hpw, hqw⟩
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

#print Or.inl
#print Or
example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩


variable (x y z w : Nat)
example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
  -- apply h₃


variable (x y z w : Nat)
example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
#check Eq.trans

example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  symm
  exact h2
  exact h1
#print Eq.trans
#print Eq.symm

example (y : Nat) : (fun _ : Nat => 0) y = 0 := by
  rfl

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
  -- repeat assumption

-- Another tactic that is sometimes useful is the `revert` tactic, which is, in a sense, an inverse to intro:
example (x : Nat) : x = x := by
  revert x
  intro y
  rfl

-- Moving a hypothesis into the goal yields an implication:
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption

/-
But revert is even more clever, in that it will revert not only an element of the context but also all the subsequent elements of the context that depend on it. For example, reverting x in the example above brings h along with it:
-/
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  intro x₁ h
  apply Eq.symm
  assumption

-- You can also revert multiple elements of the context at once:
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption



example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

/-The mnemonic in the notation above is that you are generalizing the goal by setting 3 to an arbitrary variable x. Be careful: not every generalization preserves the validity of the goal. Here, generalize replaces a goal that could be proved using rfl with one that is not provable:-/

example : 2 + 3 = 5 := by
  generalize 3 = x
  sorry

/-To preserve the validity of the previous goal, the generalize tactic allows us to record the fact that 3 has been replaced by x. All you need to do is to provide a label, and generalize uses it to store the assignment in the local context:-/

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

#check Or.inl

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption


-- The (unstructured) cases is particularly useful when you can close several subgoals using the same tactic:
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption


-- You can combine the unstructured cases tactic with the case and . notation:
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption


/- The `cases` tactic can also be used to decompose a conjunction: -/
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  rcases h with ⟨hp, hq⟩
  constructor; exact hq; exact hp



example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro h
    cases h with
    | intro h₁ h₂ => cases h₂ with
      | inl h₂ => left; exact And.intro h₁ h₂
      | inr h₂ => right; exact And.intro h₁ h₂
  · intro h
    rcases h with h₁ | h₂
    · exact And.intro h₁.1 (Or.inl h₁.2)
    · exact And.intro h₂.1 (Or.inr h₂.2)


/- You will see in `Inductive Types` that these tactics are quite general. The cases tactic can be used to decompose any element of an inductively defined type; constructor always applies the first applicable constructor of an inductively defined type. For example, you can use cases and constructor with an existential quantifier: -/

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px


example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  rcases h with ⟨y, py⟩
  exact Exists.intro y (Or.inl py)

#check Exists.intro


example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x


/- These tactics can be used on data just as well as propositions. In the next example, they are used to define functions which swap the components of the product and sum types: -/
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_pair' : α × β → β × α := by
  intro p
  exact (p.snd, p.fst)

theorem h (p : α × β): swap_pair p = swap_pair' p := by
  rfl

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption


open Nat
example (P : Nat → Prop)
    (h₀ : P 0) (h₁ : ∀ n, P (succ n))
    (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'

/- The `contradiction` tactic searches for a contradiction among the hypotheses of the current goal: -/
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction


/- You can also use `match` in tactic blocks. -/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr


/- You can “combine” `intro` with `match` and write the previous examples as follows: -/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption
#print Iff.intro

/- ## Structuring Tactic Proofs
Tactics often provide an efficient way of building a proof, but long sequences of instructions can obscure the structure of the argument. In this section, we describe some means that help provide structure to a tactic-style proof, making such proofs more readable and robust.

One thing that is nice about Lean's proof-writing syntax is that it is possible to mix term-style and tactic-style proofs, and pass between the two freely. For example, the tactics apply and exact expect arbitrary terms, which you can write using have, show, and so on. Conversely, when writing an arbitrary Lean term, you can always invoke the tactic mode by inserting a by block. The following is a somewhat toy example: -/
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

/- In fact, there is a show tactic, which is similar to the show expression in a proof term. It simply declares the type of the goal that is about to be solved, while remaining in tactic mode. -/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩


/- The show tactic can actually be used to rewrite a goal to something definitionally equivalent: -/
example (n : Nat) : n + 1 = Nat.succ n := by
  -- show Nat.succ n = Nat.succ n
  rfl


/- As with proof terms, you can omit the label in the have tactic, in which case, the default label this is used: -/
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this

/- The types in a have tactic can be omitted, so you can write have hp := h.left and have hqr := h.right. In fact, with this notation, you can even omit both the type and the label, in which case the new fact is introduced with the label this: -/
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this

/- It is useful to use `indentation` to structure proof: every time a tactic leaves more than one subgoal, we separate the remaining subgoals by enclosing them in blocks and indenting. Thus if the application of theorem foo to a single goal produces four subgoals, one would expect the proof to look like this:

  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
or

  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
or

  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  } -/


/- ## Tactic Combinators
In t₁ <;> t₂, the <;> operator provides a parallel version of the sequencing operation: t₁ is applied to the current goal, and then t₂ is applied to all the resulting subgoals: -/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption


/- The `first | t₁ | t₂ | ... | tₙ` applies each tᵢ until one succeeds, or else fails: -/
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption



example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)


/- The `try` combinator builds a tactic that always succeeds, though possibly in a trivial way: `try t` executes t and reports success, even if t fails. It is equivalent to `first| t |skip`, where `skip` is a tactic that does nothing (and succeeds in doing so). -/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
/- Be careful: `repeat (try t)` will loop forever, because the inner tactic never fails. -/


/- `all_goals t` applies t to all open goals: -/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

/- The `any_goals` tactic provides a more robust solution. It is similar to all_goals, except it succeeds if its argument succeeds on `at least one` goal: -/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

/- The first tactic in the by block below repeatedly splits conjunctions: -/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))


/- The simp tactic, instead, rewrites the goal by applying the given identities repeatedly, in any order, anywhere they are applicable in a term. It also uses other rules that have been previously declared to the system, and applies commutativity wisely to avoid looping. As a result, we can also prove the theorem as follows: -/
variable (a b c d e : Nat)
variable (a b c d e : Nat)
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]



theorem add_zero (n : Nat) : n + Nat.zero = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.add_succ, ih]


example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption



/- The rw tactic is not restricted to propositions. In the following example, we use rw [h] at t to rewrite the hypothesis t : Tuple α n to t : Tuple α 0. -/
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

/-  A number of identities in Lean's library have been tagged with the [simp] attribute, and the simp tactic uses them to iteratively rewrite subterms in an expression. -/
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption



open List
example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp
example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]


example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption


attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption


instance {i : Int} {_ : i ≥ 0} : CoeDep Int i Nat where
  coe := i.toNat

variable (i : Int) (h : i ≥ 0)



#eval Int.negSucc 0


example (w x y z : Nat) (_ : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption


/- As with rw, you can send simp a list of facts to use, including general lemmas, local hypotheses, definitions to unfold, and compound expressions. The simp tactic also recognizes the ←t syntax that rewrite does. In any case, the additional rules are added to the collection of identities that are used to simplify a term. -/

def f (m n : Nat) : Nat :=
  m + n + m
example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]


variable (k : Nat) (f : Nat → Nat)
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]

/- To use all the hypotheses present in the local context when simplifying, we can use the wildcard symbol, *: -/
variable (k : Nat) (f : Nat → Nat)
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
  -- simp only [h₂, h₁]


example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  -- simp only [Nat.add_comm, Nat.add_left_cancel_iff, h₂, h₁]
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/- The simplifier will also do propositional rewriting. For example, using the hypothesis p, it rewrites p ∧ q to q and p ∨ q to True, which it then proves trivially. Iterating such rewrites produces nontrivial propositional reasoning. -/
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]


example (x x' y y' : Nat) (_ : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]


/- One thing that makes the simplifier especially useful is that its capabilities can grow as a library develops. For example, suppose we define a list operation that symmetrizes its input by appending its reversal: -/
def mk_symm (xs : List α) :=
  xs ++ xs.reverse

theorem reverse_mk_symm (xs : List α) : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption

/- But using reverse_mk_symm is generally the right thing to do, and it would be nice if users did not have to invoke it explicitly. You can `achieve` that by marking it as a simplification rule when the theorem is defined: -/
@[simp] theorem reverse_mk_symm' (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

/- The notation @[simp] declares reverse_mk_symm to have the [simp] attribute, and can be spelled out more explicitly: -/
attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

/- Once the attribute is applied, however, there is no way to permanently remove it; it persists in any file that imports the one where the attribute is assigned. As we will discuss further in Attributes, one can limit the scope of an attribute to the current file or section using the local modifier: -/
section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end
/- Outside the section, the simplifier will no longer use reverse_mk_symm by default. -/


/- There are two additional modifiers that are useful. By default, simp includes all theorems that have been marked with the attribute [simp]. Writing simp only excludes these defaults, allowing you to use a more explicitly crafted list of rules. In the examples below, the minus sign and only are used to block the application of reverse_mk_symm. -/
example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption

/- The simp tactic has many configuration options. For example, we can enable contextual simplifications as follows: -/
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual

/- With +contextual, the simp tactic uses the fact that x = 0 when simplifying y + x = y, and x ≠ 0 when simplifying the other branch. Here is another example: -/
example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp +contextual

/- Another useful configuration option is +arith which enables arithmetical simplifications. -/
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp +arith

/- # Split Tactic
The split tactic is useful for breaking nested if-then-else and match expressions in cases. For a match expression with n cases, the split tactic generates at most n subgoals. Here is an example:-/
def f₅ (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f₅ x y w = 1 := by
  intros
  simp [f₅]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

example (x y z : Nat) :
  x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w →
  f₅ x y w = 1 := by
  intros; simp [f₅]; split <;> first | contradiction | rfl

example (x y z : Nat) :
  x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w →
  f₅ x y w = 1 := by
  intros; simp [f₅]; split <;> first | contradiction | rfl


/- Like simp, we can apply split to a particular hypothesis: -/
def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, c] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp +arith at h


/- # Extensible Tactics
In the following example, we define the notation triv using the command syntax. Then, we use the command macro_rules to specify what should be done when triv is used. -/
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p ∧ p ∧ p ∧ p := by
  triv


example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> try constructor <;> simp [*]

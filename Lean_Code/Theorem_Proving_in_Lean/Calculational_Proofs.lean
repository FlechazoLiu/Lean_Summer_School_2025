variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4


/- This style of writing proofs is most effective when it is used in conjunction with the `simp` and `rw` tactics, which are discussed in greater detail in the next chapter. For example, using rw for rewrite, the proof above could be written as follows: -/

variable (a b c d e : Nat)
theorem T'
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]


/- The calc command can be configured for any relation that supports some form of `transitivity`. It can even combine different relations. -/
variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

/- You can `“teach” calc new transitivity theorems` by adding new instances of the `Trans type class`. Type classes are introduced later, but the following small example demonstrates how to extend the calc notation using new Trans instances. -/
def divides (x y : Nat) : Prop :=
  ∃ k, k * x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k * x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2 * z) := divides_mul ..

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2 * z := divides_mul ..

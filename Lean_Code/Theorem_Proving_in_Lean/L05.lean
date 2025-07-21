import Mathlib

/-# Overview
- Reference: lean manual, mathematics in lean C04
- Notes about `Subtype` and `Set` in Lean 4
-/

/-# Subtype
- Just as sets and subsets in Set theory, there are corresponding analogues in the type theory, namely `Subtype`
- Syntactically, an element of a `Subtype` resembles a tuple of the base type's element and the proof that it satisfies the proposition.
-/

section Subtype

#check Subtype

universe u
variable (α : Type u) (p : α → Prop)

/- Syntax for `Subtype`-/
-- do not confuse with {x : α | p x}
variable (a : {x : α // p x}) (b : {x // p x})

#check { n : Nat // n % 2 = 0 }
def TwoofEven : { n : Nat // n % 2 = 0 } := ⟨2, by norm_num⟩
#check TwoofEven.1
#check TwoofEven.val
#check TwoofEven.2
#check TwoofEven.property


#check Sigma
#check Exists

#check Subtype.val          -- Subtype.val.{u} {α : Sort u} {p : α → Prop} (self : Subtype p) : α
#check Subtype.property
/- Example: Definitional Equality of Subtypes-/
-- The non-empty strings s1 and s2 are definitionally equal despite the fact that their embedded proof terms are different.

def NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property := fun h => List.cons_ne_nil _ _ (String.data_eq_of_eq h)

theorem s1_eq_s2 : s1 = s2 := by rfl

/- Coercion from a subtype to its base type (类型转换)-/
abbrev DivBy3 := { x : Nat // x % 3 = 0 }

def nine : DivBy3 := ⟨9, by rfl⟩

set_option eval.type true in
#eval Nat.succ nine

/- General conversion-/
#check 1
#check (1 : ℚ)
#check (1 : ℝ)
#check ((1 : ℚ) : ℝ)

/- Nested Subtype-/

-- Exercise: Thinking how it works?
#check ℝ
#check {x : ℝ // x ≥ 0}

variable (y : {x : ℝ // x ≥ 0})

#check y.val
#check y.property

#check {x : {x : ℝ // x ≥ 0} // (x : ℝ) > 0} -- 强制类型转换
variable (z : {x : {x : ℝ // x ≥ 0} // x.val > 0}) -- 直接取value

#check z.val
#check z.property

#check z.val.val
#check z.val.property

end Subtype


/-# Set-/

section Set

variable (α : Type)
#check Set α
#print Set

variable (s : Set α) (a : α)

/- Syntax-/
variable (p : α → Prop)

#check {x : α | p x}          -- {x | p x} : Set α

#check {x | ∃ n, 2 * n = x}   -- {x | ∃ n, 2 * n = x} : Set ℕ
#check {2 * n | n}

/- Membership-/
#check a ∈ s

example : (a ∈ s) = (s a) := by rfl

#check a ∉ s

example : (a ∉ s) = ¬(a ∈ s) := by rfl

/- Subset-/
variable (t : Set α)

#check s ⊆ t

example : (s ⊆ t) = (∀ ⦃x : α⦄, x ∈ s → x ∈ t) := by rfl

example (h₁ : s ⊆ t) (x : α) (h₂ : x ∈ s) : x ∈ t := by
  exact h₁ h₂

/- Intersection-/
#check s ∩ t      -- s ∩ t : Set α

example : (s ∩ t) = (fun x => x ∈ s ∧ x ∈ t) := by rfl
-- example : (s ∩ t) = (fun x => x ∈ t ∧ x ∈ s) := by rfl

example : (a ∈ s ∩ t) = (a ∈ s ∧ a ∈ t) := by rfl

example (h : a ∈ s ∩ t) : a ∈ s := by
  rcases h with ⟨mem_s, mem_t⟩
  exact mem_s

example (h₁ : a ∈ s) (h₂ : a ∈ t) : a ∈ s ∩ t := by
  constructor
  · exact h₁
  · exact h₂

example (h₁ : a ∈ s) (h₂ : a ∈ t) : a ∈ s ∩ t := by
  apply And.intro
  · exact h₁
  · exact h₂

example (h₁ : a ∈ s) (h₂ : a ∈ t) : a ∈ s ∩ t := by
  exact ⟨h₁, h₂⟩

-- Exercise
example (h : a ∈ s ∩ t) : a ∈ t ∩ s := by
  exact ⟨h.2, h.1⟩

/- Union-/
#check s ∪ t      -- s ∪ t : Set α

example : (s ∪ t) = (fun x => x ∈ s ∨ x ∈ t) := by rfl

example : (a ∈ s ∪ t) = (a ∈ s ∨ a ∈ t) := by rfl

example (r : Set α) (h : a ∈ s ∪ t) (h₁ : s ⊆ r) (h₂ : t ⊆ r) : a ∈ r := by
  rcases h with mem_s | mem_t
  · exact h₁ mem_s
  · exact h₂ mem_t

example (r : Set α) (h : a ∈ s ∪ t) (h₁ : s ⊆ r) (h₂ : t ⊆ r) : a ∈ r := by
  cases h with
  | inl h => exact h₁ h
  | inr h => exact h₂ h

/- Difference-/

#check s \ t      -- s \ t : Set α

example : (s \ t) = (fun x => x ∈ s ∧ x ∉ t) := by rfl

example : (a ∈ s \ t) = (a ∈ s ∧ a ∉ t) := by rfl

example (h : a ∈ s \ t) : a ∉ t := by
  exact h.right

example (h₁ : a ∈ s) (h₂ : a ∉ t) : a ∈ s \ t := by
  exact ⟨h₁, h₂⟩

/- Complement-/
#check sᶜ         -- sᶜ : Set α

example : sᶜ = (fun x => x ∉ s) := by rfl

example : (a ∈ sᶜ) = (a ∉ s) := by rfl

example (h₁ : a ∈ s) (h₂ : a ∈ sᶜ) : 1 = 2 := by
  exfalso
  exact h₂ h₁

example (h : a ∉ t) (h₂ : s ⊆ t) : a ∈ sᶜ := by
  intro mem_s
  apply h
  exact h₂ mem_s

/- Empty Set and Universal Set-/
#check Set.univ

example : ∀ x : α, x ∈ Set.univ := by
  intro x
  trivial

#check ∅              -- ∅ : ?m.3167
#check (∅ : Set α)    -- ∅ : Set α
example : ∀ x : α, x ∉ (∅ : Set α) := by
  intro x mem_empty
  exact mem_empty

/- `ext` tactcic (外延性) -/
example (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x'
  exact h x'

#check Set.ext

-- Exercise
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨h₁, h₂⟩
  exact And.intro (h h₁) h₂

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨h₁, h₂⟩ => ⟨h h₁, h₂⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by

  sorry

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

example : s ∩ (s ∪ t) = s := by
  apply Set.Subset.antisymm_iff.mpr
  constructor
  · intro _ h
    exact h.1
  · intro x h
    exact And.intro h (Or.inl h)

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro h
    exact And.intro h (Or.inl h)

#check Set.Subset.antisymm_iff

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

/- index union and intersection-/
variable {α I : Type*}

variable (A B : I → Set α)

variable (s : Set α)

#check Set.mem_iUnion
#check Set.mem_iInter

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  sorry

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry

end Set



@[ext]
structure Point where new ::
  x : Nat
  y : Nat
  z : Nat

#print Point
#check Point.new.injEq
#print And


-- 定义SpecialPoint类型，包含点和该点满足的特定性质
structure SpecialPoint where
  val : Point          -- 点对象
  property : Point → Prop  -- 该点需要满足的性质
  satisfies : property val -- 证明点满足性质

#print Group

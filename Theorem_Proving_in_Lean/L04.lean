import Mathlib

/-# Overview
- Reference: mathematics in lean C03, theorem proving in lean Chapter 3
-/

/-# Conjunction-/

section Conjuction

variable {P Q R : Prop}

-- P ∧ R → Q ∨ R ∧ P means (P ∧ R) → (Q ∨ (R ∧ P))
#check P ∧ R → Q ∨ R ∧ P

-- `constructor` tactic for constructing conjunctions
example (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  · exact q

#check And.intro

example (p : P) (q : Q) : P ∧ Q := And.intro p q

-- `⟨⟩` for constructing conjunctions
example (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

-- (doge
example : ∃ x : ℕ, 1 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num
-- <;> is for using the tactic on all subgoals before
#print norm_num

-- #eval 1 / 0
#check Nat.instDiv

-- `rcases` and `rintro` for using conjunctions
example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  intro h
  rcases h with ⟨z, xltz, zlty⟩
  -- rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  -- intro h
  -- rcases h with ⟨z, xltz, zlty⟩
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_, xltz, zlty⟩ ↦ lt_trans xltz zlty
  -- fun ⟨_, h⟩ ↦ lt_trans h.1 h.2


-- In Lean, `A ↔ B` is not defined to be `(A → B) ∧ (B → A)`, but it behaves roughly the same way.
example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx  {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 0) : a = 0 ∧ b = 0 := by
      constructor
      · apply le_antisymm _ ha
        rw [← hab] at ⊢
        exact le_add_of_nonneg_right hb
      · apply le_antisymm _ hb
        rw [add_comm] at hab
        rw [← hab]
        exact le_add_of_nonneg_right ha
    have h₁ : x ^ 2 = 0 ∧ y ^ 2 = 0 := hx (sq_nonneg x) (sq_nonneg y) h
    rw [pow_two, pow_two] at h₁
    exact And.intro (mul_self_eq_zero.mp h₁.1) (mul_self_eq_zero.mp h₁.2)
  · intro h
    rw [h.1, h.2]
    simp


#check le_antisymm
#check le_add_of_nonneg_right

#check add_nonneg
#check sq_nonneg
#check sq_eq_zero_iff
#check add_eq_zero
#check mul_self_eq_zero
#check pow_two
#leansearch "pow_two."

variable (h : P ∧ Q)
#check h.1 -- P
#check h.2 -- Q

-- since iff is an equivalence relation, we can use `rw`
#check abs_lt
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

end Conjuction

/-# Disjunction-/

section Disjunction

variable {P Q : Prop}

-- `left` and `right` for constructing disjunctions
example {p : P} : P ∨ Q := by
  left
  exact p

example {q : Q} : P ∨ Q := by
  right
  exact q

-- `Or.inl` and `Or.inr` for constructing disjunctions
#check Or.inl

example {y : ℝ} (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example {y : ℝ} (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

-- `rcases` for using disjunctions
#check le_or_gt
example {x y : ℝ} : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

-- Exercise
namespace MyAbs

theorem lt_abs {x y : ℝ} : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt {x y : ℝ} : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

-- Exercise
example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end Disjunction

section Negation

/-# Negation
- Negation, `¬p`, is actually defined to be `p → False`, so we obtain `¬p` by deriving a contradiction from `p`
-/
variable {P Q : Prop}
#check Not

/- Similarly, the expression `hnp hp` produces a proof of `False` from `hp : p` and `hnp : ¬p`-/
example (hpq : P → Q) (hnq : ¬Q) : ¬P := by
  intro hp
  apply hnq
  apply hpq
  exact hp

example (hpq : P → Q) (hnq : ¬Q) : ¬P :=
  fun hp : P => hnq (hpq hp)

variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

#check lt_irrefl

-- Exericise, notice that `x ≠ y` is just `¬ x = y`
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  sorry

variable {P : ℝ → Prop}

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

-- `by contra` tactic -- 反证法
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

-- `contrapose` tactic -- 逆否命题
example {P Q : Prop} (h : ¬ Q → ¬ P) : P → Q := by
  contrapose!
  exact h

-- `exfalso` tactic -- change the goal to `False` -- 爆炸律
example (h : 0 < 0) : a > 37 := by
  -- tauto
  exfalso
  apply lt_irrefl 0 h

end Negation

/-# cheetsheet
- `→` `∀` : `apply`, `intro`
- `∃` : `use`, `rcases`
- `∧` (`↔`): `constructor`, `⟨⟩`, `rcases`
- `∨` : `left`, `right`, `rcases`
- `¬` : `by_contra`, `contrapose!`, `push_neg`
-/


#leansearch "a < b, b ≤ c -> a < c."
#check le_of_lt
#check lt_of_le_of_lt
#check lt_of_lt_of_le
#check le_of_lt_or_eq
example {a b c : ℕ} (h₁ : a < b) (h₂ : c ≥ b) : a ≤ b ∧ a < c := by
  constructor
  · exact le_of_lt h₁
  · exact lt_of_lt_of_le h₁ h₂

example (P Q : Prop) : (P → Q) ↔ (¬P ∨ Q) := by
  constructor
  · intro h
    by_cases p : P  -- 使用排中律考虑P成立与否
    · right  -- 若P成立
      exact h p
    · left  -- 若P不成立，则¬P成立，因此选择左侧
      exact p
  · intro h   -- 假设 ¬P ∨ Q
    intro p   -- 假设P成立
    cases h with  -- 分解¬P ∨ Q的两种情况
    | inl np =>  -- 若¬P成立，则与p(P)矛盾
        contradiction
    | inr q =>   -- 若Q成立，直接返回Q
        exact q


variable {P : ℝ → Prop}
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x, h''⟩


variable {P : ℝ → Prop}
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x
  by_contra h'
  apply h
  use x


namespace Exercise
#check abs_of_nonneg
#check abs_of_neg
theorem lt_abs {x y : ℝ} : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      intro h'
      left
      exact h'
    · rw [abs_of_neg h]
      intro h'
      right
      exact h'
  · intro h
    rcases h with (h' | h')
    · exact lt_of_lt_of_le h' (le_abs_self y)
    · have h'' := le_abs_self (-y)
      rw [abs_neg] at h''
      exact lt_of_lt_of_le h' h''

theorem abs_lt {x y : ℝ} : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    rcases le_or_gt 0 y with h' | h'
    · refine And.intro ?_ (lt_of_le_of_lt (le_abs_self x) h)
      · have h'' := le_abs_self (-x)
        rw [abs_neg] at h''
        exact neg_lt.mp (lt_of_le_of_lt h'' h)
    · apply lt_trans h at h'
      have h'' := abs_nonneg x
      exfalso
      exact not_lt.mpr h'' h' -- 0 ≤ |x| 和 |x| < 0 矛盾
  · intro h
    rcases h with ⟨h₁, h₂⟩
    rcases le_or_gt 0 x with h₃ | h₃
    · apply abs_of_nonneg at h₃
      rw [h₃]
      exact h₂
    · apply abs_of_neg at h₃
      rw [h₃]
      exact neg_lt.mp h₁



#check lt_trans
#check abs_neg
#check le_abs_self
#check abs_nonneg
#check not_lt

end Exercise

#check lt_of_le_of_lt
#check EReal.neg_le
#check abs_of_pos
#check EReal.neg_lt_comm
#check neg_lt_neg_iff
#leansearch "a > 0 → |a| = a."

#check neg_lt_neg_iff
#check neg_lt


example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with h₁ | h₂
  · rcases h₁ with ⟨a, ha⟩
    use a * k
    rw [ha, mul_assoc]
  · rcases h₂ with ⟨b, hb⟩
    use n * b
    rw [hb, ← mul_assoc, mul_comm n _, ← mul_assoc]



-- theorem sqrt2_irrational : Irrational (Real.sqrt 2) := by
--   -- 假设 √2 是有理数
--   by_contra h_rat
--   rw [Irrational] at h_rat
--   push_neg at h_rat

--   obtain ⟨q, hq⟩ := h_rat



theorem sqrt2_irrational : Irrational (Real.sqrt 2) := by
  sorry

#check Irrational
#check Set.range Rat.cast

#check Rat.exists
#print Rat.num
#print Rat.den

#eval Rat.num 1.15

#eval Rat.den 1.15

import Mathlib
#check one_add_one_eq_two
#check add_mul
#check one_mul


#check add_neg_cancel_right

#check sub_pow_two
#check add_zero
#check add_assoc
#check add_sub_left_comm
#check sub_self
example (x y : ℝ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by
  rw [sub_pow_two] at h
  rw [← add_zero (2 * x * y)]
  rw [← h]
  rw [← add_assoc]
  rw [add_sub_left_comm]
  rw [sub_self]
  rw [add_zero]


#check mul_comm
#check mul_assoc
#check two_mul
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, mul_comm, hyp', ← two_mul, mul_assoc]

universe u
def F (α : Type u) : Type u := Prod α α
def β : Type := Nat
#check F β


#check (fun (x : Nat) => x + 5) 10
#check λ (x : Nat) => x + 5
#check ℕ → ℕ

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2


#check (fun x : Nat => x) 1
#check (fun _ : Nat => true) 1
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#eval(fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0

def double (x : Nat) : Nat :=
  x + x

def double' : Nat → Nat :=
  fun x => x + x

#eval double 3


def doTwice (f : Nat → Nat) (x : Nat) :=
  f (f x)

#eval doTwice double 2

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat (doTwice double) square 3

variable (α : Type u) (n : Nat)
#check Vector α n

namespace SummerClassProject
universe v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5


def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs

#print Lst
#print Lst.cons
#print Lst.nil
#print Lst.append

#check Nat.succ


#check @id
#check id
#check @id Nat
#check @id Bool
#check @id Nat 1
#check @id Bool true

#check Nat.add

#check norm_num

open Nat
example (n : ℕ) : ∃ (p : ℕ), p.Prime ∧ n < p := by
  let N := n ! + 1
  let p := minFac N
  have hp : p.Prime := by
    refine minFac_prime ?_
    by_contra! HN
    simp [N] at HN
    have : n ! ≠ 0 := factorial_ne_zero n
    contradiction
  use p
  constructor
  assumption
  by_contra! H
  have H1 : p ∣ N := minFac_dvd N
  have H2 : p ∣ n ! := (Prime.dvd_factorial hp).mpr H
  have H3 : p ∣ 1 := (Nat.dvd_add_iff_right H2).mpr H1
  have H4 : ¬(p ∣ 1) := Nat.Prime.not_dvd_one hp
  contradiction


#check abs_le_of_sq_le_sq
example (a b : ℝ) (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := by
  exact abs_le_of_sq_le_sq h hb


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

example : a = d := (hab.trans hcb.symm).trans hcd

variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl a
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2


variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁


example : f a = f b := by
  rw [h₁]


variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

#check Nat.add_assoc

example (x y : Nat) :
    (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  -- h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
  rw [← Nat.add_assoc (x * x + y * x) (x * y) (y * y)] at h2
  exact h2

-- set_option pp.all true
#check (1 : Nat)
#check Type u


example (n : ℕ) : 3 ∣ n ^ 3 + 3 * n ^ 2 + 2 * n := by
  induction n
  case zero =>
    simp
  case succ n h =>
    rcases h with ⟨d, f⟩
    ring
    use (d + n ^ 2 + 3 * n + 2)
    ring
    rw [mul_comm d]
    rw [← f]
    ring


#print Dvd


example (n : ℕ) : 3 ∣ n ^ 3 + 3 * n ^ 2 + 2 * n := by
  induction n
  case zero =>  -- 基础情况：n=0
    simp
  case succ n ih =>  -- 归纳步骤：假设对n成立，证明对n+1成立
    -- 展开 (n+1)^3 + 3*(n+1)^2 + 2*(n+1)
    have : (n+1)^3 + 3*(n+1)^2 + 2*(n+1) =
           (n^3 + 3*n^2 + 2*n) + 3*(n^2 + 3*n + 2) := by
      ring  -- 用ring证明代数恒等式

    -- 应用归纳假设和代数恒等式
    rw [this]
    -- 3整除第一项（归纳假设）
    apply dvd_add
    · exact ih  -- 归纳假设
    · -- 3整除第二项（显式倍数）
      apply dvd_mul_of_dvd_left
      norm_num  -- 证明3整除3





example (R : Type) [Ring R] (a : R) (h : a ^ 2 = 0) : ∀ x : R, Commute (a * x + x * a) a := by
  intro x
  rw [Commute]
  rw [SemiconjBy]
  rw [add_mul, mul_add a _]


  sorry



example {R : Type*} [Ring R] : (∀ x : R, ∀ k : ℕ, x ≠ 0 → x ^ k ≠ 0) ↔ (∀ x : R, x ^ 2 = 0 → x = 0) := by
  constructor
  · intro h
    by_contra!
    rcases this with ⟨t, p⟩
    have w := h t 2 (p.2)
    replace p := p.1
    tauto
  · intro h
    intro x k
    induction k
    · by_contra!
      have s := this.2
      have o : x = 0 := by
        rw [← pow_one x, ← add_zero 1, pow_add, s, mul_zero]
      tauto
    ·
      sorry



#check Nat.even_or_odd

#print Even
#check pow_mul
#check pow_add
#check pow_one
#check pow_zero
#check Nat.instOrd_mathlib
#check Nat.strong_induction_on


-- 63
example {R : Type*} [Ring R] : (∀ x : R, ∀ k : ℕ, x ≠ 0 → x ^ k ≠ 0) ↔ (∀ x : R, x ^ 2 = 0 → x = 0) := by
  constructor
  · intro h x hx2
    by_contra hx
    exact h x 2 hx hx2
  · intro h x k hx
    by_contra hxk
    let S := { n : ℕ | x ^ (n + 1) = 0 }
    have S_nonempty : S.Nonempty := by
      cases' k with k
      · have o : x = 0 := by
          rw [← pow_one x, ← add_zero 1, pow_add, hxk, mul_zero]
        tauto
      · use k
        exact hxk
    have wf : WellFounded (· < · : ℕ → ℕ → Prop) := IsWellFounded.wf
    set m := WellFounded.min wf S S_nonempty with m_def
    have hm : m ∈ S := WellFounded.min_mem wf S S_nonempty
    have hm_min : ∀ k < m, k ∉ S := by
      intro k hk
      by_contra!
      exact WellFounded.not_lt_min wf S S_nonempty this hk

    have : x ^ (m + 1) = 0 := hm
    have m_pos : m > 0 ∨ m = 0 := by cases m <;> simp
    cases' m_pos with m_pos m_zero
    · let k := m - 1
      have m_eq : m = k + 1 := (Nat.succ_pred_eq_of_pos m_pos).symm
      have x_pow_k1_ne_zero : x^(k+1) ≠ 0 := by
        intro h_contra
        have k_in_S : k ∈ S := h_contra
        have k_lt_m : k < m := by rw [m_eq]; exact Nat.lt_succ_self k
        exact hm_min k k_lt_m k_in_S
      have m' : m * 2 = (m - 1) + (m + 1) := by linarith
      have sq_eq_zero : (x ^ (k + 1) ) ^ 2 = 0 := by
        rw [← pow_mul]
        rw [← m_eq, m', pow_add, this]
        simp
      have op := h (x ^ (k + 1)) sq_eq_zero
      tauto
    · rw [m_zero] at this
      simp at this
      exact hx this


#leansearch "自然数的良序性."


#print Ord

#check Nat.find_min

#check Nat.find_spec




example {G : Type*} [Group G] {A B : Subgroup G} : (∃ C : Subgroup G , C.carrier = (A.carrier ∪ B.carrier)) ↔ A ≤ B ∨ B ≤ A := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra h
    rw [not_or] at h
    obtain ⟨hAB, hBA⟩ := h
    obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.mp hAB
    obtain ⟨b, hbB, hbA⟩ := SetLike.not_le_iff_exists.mp hBA
    have ha : a ∈ A.carrier ∪ B.carrier := by simp [haA]
    have hb : b ∈ A.carrier ∪ B.carrier := by simp [hbB]
    rw [← hC] at ha hb
    have hab : a * b ∈ C.carrier := C.mul_mem ha hb
    rw [hC] at hab
    cases' hab with habA habB
    · have : a⁻¹ * (a * b) ∈ A := A.mul_mem (A.inv_mem haA) habA
      rw [inv_mul_cancel_left] at this
      contradiction
    · have : (a * b) * b⁻¹ ∈ B := B.mul_mem habB (B.inv_mem hbB)
      rw [mul_inv_cancel_right] at this
      contradiction
  · intro h
    rcases h with h | h
    · use B; ext x; constructor
      · intro hxA; right; exact hxA
      · intro hx; cases' hx with hxA hxB
        · exact h hxA
        · exact hxB
    · use A; ext x; constructor
      · intro e; left; exact e
      · intro hx; rcases hx with hx | hx
        · trivial
        · exact h hx



#print IsWellFounded.wf
#check Nat.add_lt_add_left
#check mul_pow


#leansearch "m > 0 → m + m > m."

import Mathlib

/-!
This file provides a series of problems for the mock final exam of RUC Summer School 2025.

The lemmas involved will be quite useful in the final exam.

You **ARE** supposed to fill in all the `sorry`s. Some helpful lemmas are listed using `#check` command between the problems.
-/

namespace Neukirch

/-- The natural explanation of this arithmetic law is found in the larger domain of the guassian integers. So let's first define Gaussian integers as follows in Lean. -/
@[ext] structure MyGaussian where
  re : ℤ
  im : ℤ

#check MyGaussian.ext_iff

namespace MyGaussian

/-!
Here are some easy but somehow useful lemmas to help simply the goals.
-/
lemma eq_def (x : MyGaussian) : x = ⟨x.re, x.im⟩ :=
  rfl

lemma re_eq {x y : MyGaussian} (h : x = y) : x.re = y.re := by
  rw [h]

lemma im_eq {x y : MyGaussian} (h : x = y) : x.im = y.im := by
  rw [h]

/-!
In this section, we endow `MyGaussian` the canonical commutative ring structure.

We also teach the definition of something like `add`, `mul`, `neg`, `sub`, and so on, to the simplifier, so `simp` becomes more powerful. As a result, in most circumstances, you can simply use `simp` and `ring` to help prove the annoying and boring propositions about definitions and arithmetic.
-/
section RingStructure

/-- The canonical addition on `MyGaussian`, i.e.,
  `(a + b i) + (c + d i) = (a + c) + (b + d) i`. -/
instance : Add MyGaussian where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

@[simp] lemma add_def (x y : MyGaussian) :
    x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

@[simp] lemma add_def' (a b c d : ℤ) :
    (⟨a, b⟩ : MyGaussian) + ⟨c, d⟩ = ⟨a + c, b + d⟩ :=
  rfl

@[simp] lemma re_add (x y : MyGaussian) :
    (x + y).re = x.re + y.re :=
  rfl

@[simp] lemma im_add (x y : MyGaussian) :
    (x + y).im = x.im + y.im :=
  rfl

/-- The canonical multiplication on `MyGaussian`, i.e.,
  `(a + b i) * (c + d i) = (a * c - b * d) + (a * d + b * c) i`. -/
instance : Mul MyGaussian where
  mul x y := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

@[simp] lemma mul_def (x y : MyGaussian) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl

@[simp] lemma mul_def' (a b c d : ℤ) :
    (⟨a, b⟩ : MyGaussian) * ⟨c, d⟩ = ⟨a * c - b * d, a * d + b * c⟩ :=
  rfl

@[simp] lemma re_mul (x y : MyGaussian) :
    (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp] lemma im_mul (x y : MyGaussian) :
    (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

/-- The canonical negation on `MyGaussian`, i.e.,
  `-(a + b i) = (-a) + (-b) i`. -/
instance : Neg MyGaussian where
  neg x := ⟨-x.re, -x.im⟩

@[simp] lemma neg_def (x : MyGaussian) :
    -x = ⟨-x.re, -x.im⟩ :=
  rfl

@[simp] lemma neg_def' (a b : ℤ) :
    -(⟨a, b⟩ : MyGaussian) = ⟨-a, -b⟩ :=
  rfl

/-- The canonical subtraction on `MyGaussian`, i.e.,
  `(a + b i) - (c + d i) = (a + (-c)) + (b + (-d)) i`. -/
instance : Sub MyGaussian where
  sub x y := x + -y

@[simp] lemma sub_def (x y : MyGaussian) :
    x - y = ⟨x.re - y.re, x.im - y.im⟩ := by
  rw [show x - y = x + -y from rfl]
  ext <;> simp <;> ring

@[simp] lemma sub_def' (a b c d : ℤ) :
    (⟨a, b⟩ : MyGaussian) - ⟨c, d⟩ = ⟨a - c, b - d⟩ := by
  ext <;> simp

/-- The canonical null element on `MyGaussian`, i.e.,
  `0 + 0 i`. -/
instance : Zero MyGaussian where
  zero := ⟨0, 0⟩

@[simp] lemma zero_def : (0 : MyGaussian) = ⟨0, 0⟩ :=
  rfl

/-- The canonical identity element on `MyGaussian`, i.e.,
  `1 + 0 i`. -/
instance : One MyGaussian where
  one := ⟨1, 0⟩

@[simp] lemma one_def : (1 : MyGaussian) = ⟨1, 0⟩ :=
  rfl

/-- This is an easy tactic that helps build the canonical commutative ring structure of `MyGaussian`. It should be only useful in the definition of the instance below. -/
macro "quick_proof" : tactic =>
  `(tactic|
  focus
    intros
    ext <;> simp <;> try ring)

/-- The canonical commutative ring structure on `MyGaussian`. -/
instance : CommRing MyGaussian where
  add := (· + ·)
  add_assoc := by
    quick_proof
  zero := 0
  zero_add := by
    quick_proof
  add_zero := by
    quick_proof
  add_comm := by
    quick_proof
  mul := (· * ·)
  left_distrib := by
    quick_proof
  right_distrib := by
    quick_proof
  zero_mul := by
    quick_proof
  mul_zero := by
    quick_proof
  mul_assoc := by
    quick_proof
  one := 1
  one_mul := by
    quick_proof
  mul_one := by
    quick_proof
  neg := (- ·)
  sub := (· - ·)
  sub_eq_add_neg := by
    quick_proof
  neg_add_cancel := by
    quick_proof
  mul_comm := by
    quick_proof
  nsmul := nsmulRec   -- Ignore this.
  zsmul := zsmulRec   -- Ignore this.
  natCast n := ⟨n, 0⟩  -- Here, we give the canonical type coercion from `ℕ` to `MyGaussian`, i.e., `n := n + 0 i`.
  intCast z := ⟨z, 0⟩  -- Here, we give the canonical type coercion from `ℤ` to `MyGaussian`, i.e., `z := z + 0 i`.
@[simp] lemma two_def : (2 : MyGaussian) = ⟨2, 0⟩ :=
  rfl

@[simp] lemma natCast_def (n : ℕ) : (n : MyGaussian) = ⟨n, 0⟩ :=
  rfl

@[simp] lemma intCast_def (z : ℤ) : (z : MyGaussian) = ⟨z, 0⟩ :=
  rfl
end RingStructure

theorem eq_zero_of_two_mul_eq_zero (x : MyGaussian) :
    2 * x = 0 → x = 0 := by
  intro h
  simp at h
  rcases h with ⟨hl, hr⟩
  ext
  · exact hl
  · exact hr

theorem ex₁ (a : MyGaussian) (h : a ≠ 0) : a * ⟨-1, 0⟩ ≠ a := by
  intro p
  rcases a with ⟨m, n⟩
  simp at p
  have m0 : m = 0 := by linarith
  have n0 : n = 0 := by linarith
  rw [m0, n0] at h
  simp at h

theorem ex₂ (a : MyGaussian) (h : a ≠ 0) : a * ⟨0, 1⟩ ≠ a := by
  intro p
  rcases a with ⟨m, n⟩
  simp at p
  have m0 : m = 0 := by linarith
  have n0 : n = 0 := by linarith
  rw [m0, n0] at h
  contradiction

theorem ex₃ (a : MyGaussian) (h : a ≠ 0) : a * ⟨0, -1⟩ ≠ a := by
  intro p
  rcases a with ⟨m, n⟩
  simp at p
  have m0 : m = 0 := by linarith
  have n0 : n = 0 := by linarith
  rw [m0, n0] at h
  contradiction

section
open Nat
#check ZMod.one_eq_zero_iff
#check ZMod.val_natCast
theorem neg_one_eq_factorial_mod_prime (p : ℕ) (h : Nat.Prime p) :
    p - 1 = (p - 1)! % p := by
  sorry
end

theorem ex₅ (a b : ℤ) (h : a ^ 2 + b ^ 2 = 1) : |a| ≤ 1 := by
  have : a ^ 2 ≤ 1 := by
    have p : 1 - a ^ 2 ≥ 0:= by
      rw [← h]; simp
      exact sq_nonneg b
    linarith
  exact (sq_le_one_iff_abs_le_one a).mp this

#check sq_le_one_iff_abs_le_one
#check sq_nonneg
#check sub_le_self
#check Nat.Prime.one_lt
theorem ex₆ (p : ℕ) (x : ℤ) (h : Nat.Prime p) : ¬(p : MyGaussian) ∣ ⟨x, 1⟩ := by
  intro r
  rcases r with ⟨n, r⟩
  simp at r
  rcases r with ⟨_, r⟩
  have t : p > 1 := Nat.Prime.one_lt h
  rcases n with ⟨a, b⟩
  simp at r
  symm at r
  apply Int.mul_eq_one_iff_eq_one_or_neg_one.mp at r
  rcases r with r | r
  · rcases r with ⟨r, _⟩
    simp at r
    rw [r] at t
    contradiction
  · rcases r with ⟨r, _⟩
    simp at r

theorem ex₇ (a b : ℤ) (n : ℕ) (h : a ^ 2 + b ^ 2 = n) :
    a.natAbs ^ 2 + b.natAbs ^ 2 = n := by
  rw [← Int.natAbs_sq a, ← Int.natAbs_sq b] at h
  norm_cast at h

#check Int.cast_add
#check Int.ofNat
#check Int.cast_pow
#check Int.natAbs_sq
lemma four_eq_two_mul_two : 4 = 2 * 2 :=
  rfl

#check Nat.mod_def
lemma not_odd_of_mod_four_eq_zero_or_two {n : ℕ} :
    n % 4 = 0 ∨ n % 4 = 2 → ¬Odd n := by
  intro h
  intro t
  rcases t with ⟨a, t⟩
  rw [t] at h
  rcases h with h | h
  · rw [Nat.mod_def, four_eq_two_mul_two] at h
    have mod_left : (2 * a + 1 - 2 * 2 * ((2 * a + 1) / (2 * 2))) % 2 = 1 := by sorry
    have mod_right : 0 % 2 = 0 := by simp
    have : 0 % 2 = 0 % 2 := rfl
    nth_rewrite 1 [← h] at this
    rw [mod_left, mod_right] at this
    tauto
  · rw [Nat.mod_def, four_eq_two_mul_two] at h
    have mod_left : (2 * a + 1 - 2 * 2 * ((2 * a + 1) / (2 * 2))) % 2 = 1 := by sorry
    have mod_right : 2 % 2 = 0 := by simp
    have : 2 % 2 = 0 % 2 := rfl
    nth_rewrite 1 [← h] at this
    rw [mod_left, mod_right] at this
    tauto

#print Odd
#check Int.even_iff
#check dvd_trans


/- Hint: Discussion by the parity of `a` and `b`. -/
theorem ex₈ (n a b : ℕ) (h : n = a ^ 2 + b ^ 2) (h' : Odd n):
    n % 4 = 1 := by
  have square_mod4 : ∀ x : ℕ, x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
    intro x
    have h₁ : x % 4 ≥ 0 := by simp
    have : 4 > 0 := by simp
    have h₂ : x % 4 < 4 := (Nat.mod_lt x) this
    interval_cases (x % 4)
    · sorry
    · sorry
    · sorry
    · sorry
  rw [h, Nat.add_mod]
  rcases square_mod4 a with (ha0 | ha1)
  rcases square_mod4 b with (hb0 | hb1)
  · have : n % 4 = 0 := by
      rw [h]
      rw [Nat.add_mod, ha0, hb0]
    rcases h' with ⟨q, h'⟩
    rw [h'] at this
    sorry
  · sorry
  sorry

end MyGaussian
#check Nat.mod_lt
end Neukirch

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
  · simp at h
    ext
    · exact h.left
    · exact h.right

theorem ex₁ (a : MyGaussian) (h : a ≠ 0) : a * ⟨-1, 0⟩ ≠ a := by
  contrapose! h
  simp at h
  rw [← neg_def', ← eq_def, neg_eq_iff_add_eq_zero, ← two_mul] at h
  exact eq_zero_of_two_mul_eq_zero _ h

theorem ex₂ (a : MyGaussian) (h : a ≠ 0) : a * ⟨0, 1⟩ ≠ a := by
  contrapose! h
  rw [MyGaussian.ext_iff] at *
  simp at h
  rcases h with ⟨h₁, h₂⟩
  have hre : a.re = 0 := by
    rw [← h₂, neg_eq_self ℤ] at h₁
    exact h₁
  have him : a.im = 0 := by
    rw [← h₁, neg_eq_self ℤ] at h₂
    exact h₂
  exact ⟨hre, him⟩

theorem ex₃ (a : MyGaussian) (h : a ≠ 0) : a * ⟨0, -1⟩ ≠ a := by
  contrapose! h
  rw [MyGaussian.ext_iff] at *
  simp at h
  rcases h with ⟨h₁, h₂⟩
  have hre : a.re = 0 := by
    rw [← h₂, neg_eq_self ℤ] at h₁
    exact h₁
  have him : a.im = 0 := by
    rw [← h₁, neg_eq_self ℤ] at h₂
    exact h₂
  exact ⟨hre, him⟩

section
open Nat
#check ZMod.one_eq_zero_iff
#check ZMod.val_natCast
-----------------------------------------------------------
theorem neg_one_eq_factorial_mod_prime (p : ℕ) (h : Nat.Prime p) :
    p - 1 = (p - 1)! % p := by
  have hp : 1 < p := by
    exact Nat.Prime.one_lt h
  rw [Nat.prime_iff_fac_equiv_neg_one (by omega)] at h
  apply_fun fun (x : ZMod p) => x.val at h
  haveI _ : NeZero p := {
    out := by omega
  }
  rw [ZMod.val_natCast, ZMod.neg_val] at h
  have one_ne_zero : ¬(1 : ZMod p) = 0 := by
    rw [ZMod.one_eq_zero_iff]
    omega
  rw [if_neg one_ne_zero, ZMod.val_one'' (by omega)] at h
  exact h.symm
end
#check Nat.prime_iff_fac_equiv_neg_one
-- apply?
-- exact?

theorem ex₅ (a b : ℤ) (h : a ^ 2 + b ^ 2 = 1) : |a| ≤ 1 := by
  refine abs_le_of_sq_le_sq ?_ ?_
  · rw [one_pow, ← h]
    refine le_add_of_nonneg_right ?_
    exact sq_nonneg _
  · linarith
#check abs_le_of_sq_le_sq
#check Nat.Prime.one_lt
theorem ex₆ (p : ℕ) (x : ℤ) (h : Nat.Prime p) : ¬(p : MyGaussian) ∣ ⟨x, 1⟩ := by
  intro hp
  rcases hp with ⟨y, hp⟩
  simp at hp
  replace hp := hp.right
  rw [eq_comm, Int.mul_eq_one_iff_eq_one_or_neg_one] at hp
  rcases hp with hp | hp <;> linarith [Nat.Prime.one_lt h]

theorem ex₇ (a b : ℤ) (n : ℕ) (h : a ^ 2 + b ^ 2 = n) :
    a.natAbs ^ 2 + b.natAbs ^ 2 = n := by
  have aux : (n : ℤ) = a.natAbs ^ 2 + b.natAbs ^ 2 := by
    rw [Int.natAbs_sq, Int.natAbs_sq]
    exact h.symm
  norm_cast at aux
  exact aux.symm
-- push_cast
lemma four_eq_two_mul_two : 4 = 2 * 2 :=
  rfl

#check Nat.mod_def
#check Nat.not_odd_iff_even
#check Nat.dvd_iff_mod_eq_zero
#check Nat.mul_div_le
lemma not_odd_of_mod_four_eq_zero_or_two {n : ℕ} :
    n % 4 = 0 ∨ n % 4 = 2 → ¬Odd n := by
  intro h
  rw [Nat.not_odd_iff_even]
  rcases h with h | h
  · rw [← Nat.dvd_iff_mod_eq_zero] at h
    rcases h with ⟨w, h⟩
    rw [four_eq_two_mul_two, mul_assoc] at h
    use 2 * w
    linarith
  · rw [Nat.mod_def, Nat.sub_eq_iff_eq_add] at h
    · use 1 + 2 * (n / 4)
      linarith
    · exact Nat.mul_div_le _ _

/- Hint: Discussion by the parity of `a` and `b`. -/
theorem ex₈ (n a b : ℕ) (h : n = a ^ 2 + b ^ 2) (h' : Odd n) :
    n % 4 = 1 := by
  by_cases ha : Even a <;> by_cases hb : Even b
  · rcases ha with ⟨k, hk⟩
    rcases hb with ⟨l, hl⟩
    rw [hk, hl] at h
    ring_nf at h
    apply_fun fun (x : ℕ) => x % 4 at h
    simp at h
    exfalso
    refine not_odd_of_mod_four_eq_zero_or_two ?_ <| h'
    exact Or.inl h
  · rw [Nat.not_even_iff_odd] at hb
    rcases ha with ⟨k, hk⟩
    rcases hb with ⟨l, hl⟩
    rw [hk, hl] at h
    ring_nf at h
    apply_fun fun (x : ℕ) => x % 4 at h
    simp at h
    exact h
  · rw [Nat.not_even_iff_odd] at ha
    rcases ha with ⟨k, hk⟩
    rcases hb with ⟨l, hl⟩
    rw [hk, hl] at h
    ring_nf at h
    apply_fun fun (x : ℕ) => x % 4 at h
    simp at h
    exact h
  · rw [Nat.not_even_iff_odd] at ha hb
    rcases ha with ⟨k, hk⟩
    rcases hb with ⟨l, hl⟩
    rw [hk, hl] at h
    ring_nf at h
    apply_fun fun (x : ℕ) => x % 4 at h
    simp at h
    exfalso
    refine not_odd_of_mod_four_eq_zero_or_two ?_ <| h'
    exact Or.inr h

end MyGaussian

end Neukirch

import Mathlib.Tactic

noncomputable section --ignore this line

/-!

# How to use this file
This file contains various definition an theorems, some of them are proved other are sorried.
You are *not* supposed to do all the `sorry` (some are very similar and not interesting). Only do
those that are called ` theorem ex_1`, `theorem ex_2` and so on. On the other hand it is surely a
good idea to read all the file. There are also questions you are supposed to answer only on paper,
not in Lean.

Here is a short list of lemmas you may use (check their statement!):
`sq_nonneg`
`pow_two`
`MyComplex.ext_iff` (it works after line 38)
`MyGaussian.ext_iff` (it works after line 143)
-/

/-!
## The definition of complex numbers
We define complex numbers as pairs of real numbers (we don't use `ℝ × ℝ` for technical reasons).
If `a b : ℝ` you can use `⟨a, b⟩` to obtain the complex number given by `a` and `b`
(sometimes you have to write `⟨a, b⟩ : MyComplex` if Lean is to able to guess that you want a complex
number).

If `x : MyComplex`, you can write `rcases x with ⟨a, b⟩` to get the two components.

Note that we use `ℝ` instead of `MyReal` so we don't have to bother with importing our repo,
but everything would work for `MyReal`.
-/
@[ext]
structure MyComplex where
  re : ℝ
  im : ℝ

namespace MyComplex

/-- If `x : MyComplex`, you can access the two real numbers, called the *real part* and the
*imaginary part* as `x.re` and `x.im`. Two complex numbers `x` and `y` are equal if `x.re = y.re`
and `x.im = y.im`. To use this fact you can use the `ext` tactic, that will turn a goal `x = y` into
the *two* goals `x.re = y.re` and `x.im = y.im`, as in the following example, -/
example {x y : MyComplex} (hre: x.re = y.re) (him : x.im = y.im) : x = y := by
  ext
  · exact hre
  · exact him

/-- Let's define an addition and a multiplication on complex numbers. -/
instance : Add MyComplex where
  add x y := ⟨x.re + y.re, x.im + y.im⟩
instance : Mul MyComplex where
  mul x y := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩


/-- And let's teach `simp` the definitions in term of real and imaginary part. -/
@[simp]
lemma add_re (x y : MyComplex) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : MyComplex) : (x + y).im = x.im + y.im := rfl
@[simp] lemma mul_re (x y : MyComplex) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma mul_im (x y : MyComplex) : (x * y).im = x.re * y.im + x.im * y.re := rfl

/-- One can endow `MyComplex` with a negation, `0`, `1`... and obtain a ring structure,
similarly to what we did for `MyReal`. -/
instance : Zero MyComplex where
  zero := ⟨0, 0⟩
@[simp] lemma zero_re : (0 : MyComplex).re = 0 := rfl
@[simp] lemma zero_im : (0 : MyComplex).im = 0 := rfl
instance : One MyComplex where
  one := ⟨1, 0⟩
@[simp] lemma one_re : (1 : MyComplex).re = 1 := rfl
@[simp] lemma one_im : (1 : MyComplex).im = 0 := rfl
instance : Neg MyComplex where
  neg x := ⟨-x.re, -x.im⟩
@[simp] lemma neg_re (x : MyComplex) : (-x).re = -x.re := rfl
@[simp] lemma neg_im (x : MyComplex) : (-x).im = -x.im := rfl


/-- Can you prove that multiplication on `MyComplex` is distributive with respect to
addition? -/
theorem ex_1 (x y z : MyComplex) : x * (y + z) = x * y + x * z := by
  -- rcases x with ⟨a₁, b₁⟩
  -- rcases y with ⟨a₂, b₂⟩
  -- rcases z with ⟨a₃, b₃⟩
  ext
  · simp
    ring
  · simp
    ring

/-- Let's put a `CommRing` structure on `MyComplex` (don't prove all the `sorry`, but they're
identical to `ex_1`). -/

instance commRing : CommRing MyComplex where
  add := (· + ·)
  add_assoc := sorry
  zero := 0
  zero_add := by sorry
  add_zero := by sorry
  add_comm := by sorry
  mul := (· * ·)
  left_distrib := ex_1
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  one := 1
  one_mul := by sorry
  mul_one := by sorry
  neg := (- ·)
  mul_comm := by sorry
  neg_add_cancel := by sorry
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this

/-- Can you prove that there is no `x : ℝ` such that `x ^ 2 = -1`?
Remember that if you write numbers Lean will automatically think they're natural numbers unless it
can guess otherwise by the rest of the statement. In particular, if you want to write `37 = 37` in
`ℝ` you have to write `(37 : ℝ) = 37` (the second `37` is forced to be in `ℝ`). -/
theorem ex_2 : ¬ ∃ (x : ℝ), x ^ 2 = -1 := by
  intro h
  rcases h with ⟨y, hy⟩
  have h₁ := sq_nonneg y
  rw [hy] at h₁
  linarith


/-- Is there a complex number `x` such that `x ^ 2 = -1`? -/
theorem ex_3 : ∃ (x : MyComplex), x ^ 2 = -1 := by
  use ⟨0, 1⟩
  rw [pow_two]
  ext
  · simp
  simp

/-- We are going to prove that there is no order in `MyComplex` that is compatible with the ring
structure, so we suppose its existence and we have to dedue a contradiction. -/
theorem ex_4 [LinearOrder MyComplex] [IsStrictOrderedRing MyComplex] : False := by

  sorry
end MyComplex
#check zero_lt_one
#print LinearOrder
#print IsStrictOrderedRing

/-!
## The gaussian integers
We now move on to a new type type of numbers, the *gaussian integers*. These are essentially complex
numbers with the real and imaginary part that are integers rather then reals.

Instead of defining them as a subring of `MyComplex` we redo everything from scratch, ignoring the
connection with `MyComplex`. Gaussian integers will again have a real and imaginary part, and all the
basics is as for `MyComplex`.

Since we need to use some results about the integers, we use mathlib's `ℤ` instead of `MyInt`.
(We don't want to rebuild a huge library!)
-/

@[ext]
structure MyGaussian where
  re : ℤ
  im : ℤ

namespace MyGaussian
#leansearch " a < b →  -b < -a"
section basic


/-- Read but don't do any `sorry` in this section, all the material is preparatory. -/

instance : Add MyGaussian where
  add x y := ⟨x.re + y.re, x.im + y.im⟩
instance : Mul MyGaussian where
  mul x y := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
@[simp]
lemma add_re (x y : MyGaussian) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : MyGaussian) : (x + y).im = x.im + y.im := rfl
@[simp] lemma mul_re (x y : MyGaussian) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma mul_im (x y : MyGaussian) : (x * y).im = x.re * y.im + x.im * y.re := rfl
instance : Zero MyGaussian where
  zero := ⟨0, 0⟩
@[simp] lemma zero_re : (0 : MyGaussian).re = 0 := rfl
@[simp] lemma zero_im : (0 : MyGaussian).im = 0 := rfl
instance : One MyGaussian where
  one := ⟨1, 0⟩
@[simp] lemma one_re : (1 : MyGaussian).re = 1 := rfl
@[simp] lemma one_im : (1 : MyGaussian).im = 0 := rfl
instance : Neg MyGaussian where
  neg x := ⟨-x.re, -x.im⟩
@[simp] lemma neg_re (x : MyGaussian) : (-x).re = -x.re := rfl
@[simp] lemma neg_im (x : MyGaussian) : (-x).im = -x.im := rfl
instance commRing : CommRing MyGaussian where
  add := (· + ·)
  add_assoc := sorry
  zero := 0
  zero_add := by sorry
  add_zero := by sorry
  add_comm := by sorry
  mul := (· * ·)
  left_distrib := sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  one := 1
  one_mul := by sorry
  mul_one := by sorry
  neg := (- ·)
  mul_comm := by sorry
  neg_add_cancel := by sorry
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this

end basic

/-- Let's define a function `MyGaussian → ℤ`, called the *norm*, that sends `(a,b)` to
`a^2+b^2`. -/

def norm : MyGaussian → ℤ := fun x ↦ x.re^2+x.im^2
@[simp] lemma norm_apply (a b : ℤ) : norm ⟨a, b⟩ = a^2+b^2 := rfl

/-- Can you prove that `norm (x * y) = norm x * norm y`?

You may find it useful to write a preliminary `simp` lemma to teach `simp` the multiplication of
two gaussian integers.
 -/

theorem ex_5 (x y : MyGaussian) : norm (x * y) = norm x * norm y := by
  repeat rw [norm]
  simp
  ring

alias norm_mul := ex_5 --so we also have a theorem called `norm_mul`

/-- Can you prove that the norm is always nonnegative? -/
theorem ex_6 (x : MyGaussian) : 0 ≤ norm x := by
  rw [norm]
  have h₁ : 0 ≤ x.re ^ 2 := sq_nonneg x.re
  have h₂ : 0 ≤ x.im ^ 2 := sq_nonneg x.im
  exact add_nonneg h₁ h₂

alias norm_nonneg := ex_6

/-- We say that `IsUnit x` if there exists `y` such that `x * y = 1`. -/
abbrev IsUnit (x : MyGaussian) := ∃ y, x * y = 1

/-- Can you prove *on paper, not in Lean*, the following?

It also holds in Lean, but the proof is slightly annoying and we are skipping it. -/
theorem ex_7 (x : MyGaussian) :
    norm x = 1 ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩ ∨ x = ⟨0, 1⟩ ∨ x = ⟨0, -1⟩ := by
  sorry
alias norm_eq_one_iff_eq := ex_7
#check norm_eq_one_iff_eq


/-- You can now prove the following. -/
theorem ex_8 (x : MyGaussian) : IsUnit x ↔ norm x = 1 := by
  constructor
  · intro h
    rcases h with ⟨y, g⟩
    have s : norm 1 = norm 1 := by rfl
    nth_rewrite 1 [← g] at s
    rw [norm_mul] at s
    have t : norm 1 = 1 := by rfl
    rw [t] at s
    apply Int.mul_eq_one_iff_eq_one_or_neg_one.mp at s
    rcases s with h | h
    · exact h.1
    · rcases h with ⟨a, b⟩
      have s := norm_nonneg x
      rw [a] at s
      linarith
  · intro h
    apply (norm_eq_one_iff_eq x).mp at h
    rcases h with h₁ | h₂ | h₃ | h₄
    · use ⟨1, 0⟩
      rw [h₁]
      ext
      · simp
      simp
    · use ⟨-1, 0⟩
      rw [h₂]
      ext
      · simp
      simp
    · use ⟨0, -1⟩
      rw [h₃]
      ext
      · simp
      simp
    · use ⟨0, 1⟩
      rw [h₄]
      ext
      · simp
      simp

#check Int.mul_eq_one_iff_eq_one_or_neg_one
alias isUnit_iff_norm_eq_one := ex_8
#print Iff
#check mul_eq_one
/-- We define a *prime gaussian integers* as a gaussian integers `x` such that:
* `x ≠ 0`
* `x` is not a unit
* if `x = a * b` then `IsUnit a` or `IsUnit b`.

This generalizes the usual definition of a prime number.
-/
abbrev IsPrime (x : MyGaussian) :=
  x ≠ 0 ∧
  ¬ (IsUnit x) ∧
  ∀ a b, x = a * b → IsUnit a ∨ IsUnit b

/-- Applying the following lemma to prove that a given `x` is prime (via `apply isPrime_def`) will
give the three goals. -/
lemma isPrime_def {x : MyGaussian} (h0 : x ≠ 0) (hunit : ¬ (IsUnit x))
    (h : ∀ a b, x = a * b → IsUnit a ∨ IsUnit b) : IsPrime x :=
  ⟨h0, hunit, h⟩

/-- Our final goal is give some examples and non examples of prime elements in `MyGaussian`.
We will consider small numbers, like `3` and `5`.

First of all you may find the following trivial lemmas useful. -/

lemma three_def : (3 : MyGaussian) = ⟨3, 0⟩ := rfl
lemma three_eq : (3 : ℤ) ^ 2 = 9 := rfl
lemma prime_three : Prime (3 : ℤ) := by norm_num
lemma five_def : (5 : MyGaussian) = ⟨5, 0⟩ := rfl

/-- We will also need the following two results (no need to prove it in Lean, but do you understand
why they are true?). -/
lemma eq_of_mul_eq_sq_of_prime (n m p : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m) (hp : Prime p)
  (h : n * m = p ^ 2) :
    (n = 1 ∧ m = p ^ 2) ∨
    (n = p ∧ m = p) ∨
    (n = p ^ 2 ∧ m = 1) := by sorry
lemma sq_add_sq_not_congruent_neg_one_mod_four (a b n : ℤ) : a^2+b^2 ≠ 4*n-1 := by
  sorry

/-- We can now prove that `(3 : MyGaussian)` is prime. -/

theorem ex_9 : IsPrime 3 := by
  apply isPrime_def
  · intro h
    cases h
  · rw [ex_8]
    rw [three_def, norm_apply]
    norm_num

  · sorry


#check Nat.one_le_iff_ne_zero
#leansearch "¬ a = b → a ≠ b."

@[simp] lemma mul_def (a b c d : ℤ) :
  (⟨a, b⟩ : MyGaussian) * ⟨c, d⟩ = ⟨a* c - b * d, a * d + b * c⟩ := rfl


/-- We can now prove that `5 : MyGaussian` is not prime. -/
theorem ex_10 : ¬IsPrime 5 := by
  have h_factor : (5 : MyGaussian) = ⟨1, 2⟩ * ⟨1, -2⟩ := by
    rw [five_def, mul_def]
    ext <;> simp

  have h1 : (⟨1, 2⟩ : MyGaussian) ≠ 0 := by
    intro h
    injection h with h_re h_im
    norm_num at h_re

  have h2 : (⟨1, -2⟩ : MyGaussian) ≠ 0 := by
    intro h
    injection h with h_re h_im
    norm_num at h_re

  have not_unit1 : ¬ IsUnit ⟨1, 2⟩ := by
    rw [ex_8, norm_apply]
    norm_num

  have not_unit2 : ¬ IsUnit ⟨1, -2⟩ := by
    rw [ex_8, norm_apply]
    norm_num

  rintro ⟨_, _, h_prime⟩

  have h_or := h_prime ⟨1, 2⟩ ⟨1, -2⟩ h_factor

  rcases h_or with h₁ | h₂
  · exact not_unit1 h₁
  · exact not_unit2 h₂


/-!
Here are a couple of questions, to be answered only on paper:
* what happens for a number that is composite in `ℤ`?
* is `(2 : MyGaussian)` prime?
* are `7` and `11` primes in `MyGaussian`? Can you formulate a conjecture? (There is a very easy
characterization of primes in `MyGaussian`, but one of the two directions is not easy to prove.)

-/

end MyGaussian

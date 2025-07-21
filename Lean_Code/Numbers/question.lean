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
  ext <;> dsimp <;> ring

/-- Let's put a `CommRing` structure on `MyComplex` (don't prove all the `sorry`, but they're
identical to `ex_1`). -/

instance commRing : CommRing MyComplex where
  add := (· + ·)
  add_assoc := by
    intros
    ext <;> dsimp <;> ring
  zero := 0
  zero_add := by
    intros
    ext <;> dsimp <;> ring
  add_zero := by
    intros
    ext <;> dsimp <;> ring
  add_comm := by
    intros
    ext <;> dsimp <;> ring
  mul := (· * ·)
  left_distrib := ex_1
  right_distrib := by
    intros
    ext <;> dsimp <;> ring
  zero_mul := by
    intros
    ext <;> dsimp <;> ring
  mul_zero := by
    intros
    ext <;> dsimp <;> ring
  mul_assoc := by
    intros
    ext <;> dsimp <;> ring
  one := 1
  one_mul := by
    intros
    ext <;> dsimp <;> ring
  mul_one := by
    intros
    ext <;> dsimp <;> ring
  neg := (- ·)
  mul_comm := by
    intros
    ext <;> dsimp <;> ring
  neg_add_cancel := by
    intros
    ext <;> dsimp <;> ring
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this

/-- Can you prove that there is no `x : ℝ` such that `x ^ 2 = -1`?
Remember that if you write numbers Lean will automatically think they're natural numbers unless it
can guess otherwise by the rest of the statement. In particular, if you want to write `37 = 37` in
`ℝ` you have to write `(37 : ℝ) = 37` (the second `37` is forced to be in `ℝ`). -/
theorem ex_2 : ¬ ∃ (x : ℝ), x ^ 2 = -1 := by
  intro ⟨x, hx⟩
  linarith [sq_nonneg x]

/-- Is there a complex number `x` such that `x ^ 2 = -1`? -/
theorem ex_3 : ∃ (x : MyComplex), x ^ 2 = -1 := by
  use ⟨0, 1⟩
  rw [pow_two]
  ext <;> dsimp <;> ring

/-- We are going to prove that there is no order in `MyComplex` that is compatible with the ring
structure, so we suppose its existence and we have to dedue a contradiction. -/
theorem ex_4 [LinearOrder MyComplex] [IsStrictOrderedRing MyComplex] : False := by
  obtain ⟨x, hx⟩ := ex_3
  rw [pow_two] at hx
  have nezero : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  rcases LinearOrder.le_total x 0 with h | h
  · have ineq1 : x < 0 := by exact lt_of_le_of_ne h nezero
    have ineq2 : 0 < -x := by exact Left.neg_pos_iff.mpr ineq1
    have := IsStrictOrderedRing.mul_lt_mul_of_pos_left x 0 (-x) ineq1 ineq2
    rw [HasDistribNeg.neg_mul x x, mul_zero] at this
    linarith
  have ineq : x > 0 := by exact lt_of_le_of_ne h (id (Ne.symm nezero))
  have := IsStrictOrderedRing.mul_lt_mul_of_pos_left 0 x x ineq ineq
  rw [hx, mul_zero] at this
  linarith


end MyComplex

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
  add_assoc := by intros; ext <;> dsimp <;> ring
  zero := 0
  zero_add := by intros; ext <;> dsimp <;> ring
  add_zero := by intros; ext <;> dsimp <;> ring
  add_comm := by intros; ext <;> dsimp <;> ring
  mul := (· * ·)
  left_distrib := by intros; ext <;> dsimp <;> ring
  right_distrib := by intros; ext <;> dsimp <;> ring
  zero_mul := by intros; ext <;> dsimp <;> ring
  mul_zero := by intros; ext <;> dsimp <;> ring
  mul_assoc := by intros; ext <;> dsimp <;> ring
  one := 1
  one_mul := by intros; ext <;> dsimp <;> ring
  mul_one := by intros; ext <;> dsimp <;> ring
  neg := (- ·)
  mul_comm := by intros; ext <;> dsimp <;> ring
  neg_add_cancel := by intros; ext <;> dsimp <;> ring
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
  unfold norm
  repeat rw [pow_two]
  dsimp
  ring

alias norm_mul := ex_5 --so we also have a theorem called `norm_mul`

/-- Can you prove that the norm is always nonnegative? -/
theorem ex_6 (x : MyGaussian) : 0 ≤ norm x := by
  unfold norm
  linarith [sq_nonneg x.re, sq_nonneg x.im]

alias norm_nonneg := ex_6

/-- We say that `IsUnit x` if there exists `y` such that `x * y = 1`. -/
abbrev IsUnit (x : MyGaussian) := ∃ y, x * y = 1

/-- Can you prove *on paper, not in Lean*, the following?

It also holds in Lean, but the proof is slightly annoying and we are skipping it. -/
theorem ex_7 (x : MyGaussian) :
    norm x = 1 ↔ x = ⟨1, 0⟩ ∨ x = ⟨-1, 0⟩ ∨ x = ⟨0, 1⟩ ∨ x = ⟨0, -1⟩ := by
  constructor
  · intro hx
    unfold norm at hx
    rcases eq_or_ne x.re 0 with h1 | h1
    · rw [h1, pow_two, mul_zero, zero_add] at hx
      have : x.im ≠ 0 := by
        intro h2
        rw [pow_two, h2, mul_zero] at hx
        exact Int.zero_ne_one hx
      rcases sq_eq_one_iff.mp hx with h2 | h2
      · right; right; left
        exact MyGaussian.ext h1 h2
      · right; right; right
        exact MyGaussian.ext h1 h2
    have h2 : x.im ^ 2 = 0 := by
      by_contra h2
      have l1 {x : Int} (hx : x > 0) : x ≥ 1 := by exact hx
      have : x.re ^ 2 > 0 := by exact pow_two_pos_of_ne_zero h1
      have : x.im ^ 2 > 0 := lt_of_le_of_ne (sq_nonneg x.im) fun a => h2 a.symm
      linarith
    rw [h2, add_zero] at hx
    rcases sq_eq_one_iff.mp hx with h1 | h1
    · left
      exact MyGaussian.ext h1 (pow_eq_zero h2)
    · right; left
      exact MyGaussian.ext h1 (pow_eq_zero h2)
  intro h
  rcases h with h | h | h | h
  all_goals
    unfold norm
    rw [pow_two, pow_two, congrArg re h, congrArg im h]
  · show 1 * 1 + 0 * 0 = 1
    norm_num
  · show -1 * -1 + 0 * 0 = 1
    norm_num
  · show 0 * 0 + 1 * 1 = 1
    norm_num
  · show 0 * 0 + -1 * -1 = 1
    norm_num

alias norm_eq_one_iff_eq := ex_7

/-- You can now prove the following. -/
theorem ex_8 (x : MyGaussian) : IsUnit x ↔ norm x = 1 := by
  rw [IsUnit]
  constructor
  · intro ⟨y, hy⟩
    have hnorm := norm_mul x y
    rw [hy, show norm 1 = 1 by decide] at hnorm
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hnorm.symm with h | h
    · exact h
    exfalso
    have := norm_nonneg x
    linarith
  intro h
  rcases (ex_7 x).mp h with h | h | h | h
  · use ⟨1, 0⟩
    ext; all_goals simp [congrArg re h, congrArg im h]
  · use ⟨-1, 0⟩
    ext; all_goals simp [congrArg re h, congrArg im h]
  · use ⟨0, -1⟩
    ext; all_goals simp [congrArg re h, congrArg im h]
  · use ⟨0, 1⟩
    ext; all_goals simp [congrArg re h, congrArg im h]

alias isUnit_iff_norm_eq_one := ex_8

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
  have hnorm : norm 3 = 9 := by
    unfold norm
    show 3 ^ 2 + 0 ^ 2 = 9
    norm_num
  apply isPrime_def
  · intro h
    have := congrArg re h
    have : (3 : ℤ) = 0 := by exact this
    linarith
  · intro h
    rw [ex_8] at h
    linarith
  intro a b hab
  have normab := norm_mul a b
  rw [← hab, hnorm, show (9 : ℤ) = 3 ^ 2 by decide] at normab
  rcases eq_of_mul_eq_sq_of_prime a.norm b.norm 3 (norm_nonneg a) (norm_nonneg b)
    prime_three normab.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    apply (ex_8 a).mpr h1
  · unfold norm at h1
    have := sq_add_sq_not_congruent_neg_one_mod_four a.re a.im 1
    rw [show 4 * 1 - 1 = (3 : ℤ) by decide] at this
    exfalso
    exact this h1
  right
  apply (ex_8 b).mpr h2

@[simp] lemma mul_def (a b c d : ℤ) :
  (⟨a, b⟩ : MyGaussian) * ⟨c, d⟩ = ⟨a* c - b * d, a * d + b * c⟩ := rfl

/-- We can now prove that `5 : MyGaussian` is not prime. -/
theorem ex_10 : ¬IsPrime 5 := by
  intro ⟨_, _, h⟩
  have eq : (5 : MyGaussian) = ⟨1, 2⟩ * ⟨1, -2⟩ := by
    ext <;> rfl
  specialize h ⟨1, 2⟩ ⟨1, -2⟩ eq
  have h1 : ¬ IsUnit (⟨1, 2⟩ : MyGaussian) := by
    intro hunit
    have : (⟨1, 2⟩ : MyGaussian).norm = 5 := by decide
    rw [ex_8] at hunit
    linarith
  have h1 : ¬ IsUnit (⟨1, -2⟩ : MyGaussian) := by
    intro hunit
    have : (⟨1, -2⟩ : MyGaussian).norm = 5 := by decide
    rw [ex_8] at hunit
    linarith
  tauto

/-!
Here are a couple of questions, to be answered only on paper:
* what happens for a number that is composite in `ℤ`?
* is `(2 : MyGaussian)` prime?
* are `7` and `11` primes in `MyGaussian`? Can you formulate a conjecture? (There is a very easy
characterization of primes in `MyGaussian`, but one of the two directions is not easy to prove.)

-/
end MyGaussian

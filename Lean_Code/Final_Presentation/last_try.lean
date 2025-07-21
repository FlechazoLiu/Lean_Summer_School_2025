/-
Copyright (c) 2024 @Hanbo Zou, @Zhenghao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @Hanbo Zou, @Zhenghao Liu
-/
import Mathlib

open Polynomial

noncomputable section

variable {F : Type*} [Field F] -- [Finite F] --(f g h : F[X])

/-!
# Reciprocal Polynomials and Irreducibility

This file formalizes properties of `reciprocal polynomials`, including:
- The definition and basic properties of reciprocal polynomials
- Irreducibility of reciprocal polynomials (Theorem 3.12)
- Factorization structure of self-reciprocal polynomials (Theorem 3.13)

## Main Definitions

* `Polynomial.reverse` (notated as `f⁎`): The reciprocal polynomial of `f`, defined as `x^{natDegree f} * f(1/x)`
* `self_reciprocal f`: A predicate stating that a polynomial equals its reciprocal

## Main Theorems

1. `reciprocal_irreducible`: If `f` is irreducible with nonzero constant term, then its reciprocal is irreducible.
2. `self_reciprocal_factor_structure`: The structure theorem for self-reciprocal polynomials with two irreducible factors.

## Implementation Notes

* The reciprocal requires the polynomial to have a nonzero constant term (`coeff 0 ≠ 0`) for involutivity
* Reverse notation `f⁎` is used throughout instead of explicit `reverse f`

## References

* Finite fields [© Cambridge University Press, 2009]

## Tags

polynomial, reciprocal, irreducible, self-reciprocal
-/

/-! ### Reciprocal Polynomial Definition -/

/--
Notation for the reciprocal polynomial: `f⁎ = reverse f`.
This is defined as `x^{natDegree f} * f(1/x)` and requires `f(0) ≠ 0`.
-/
notation f "⁎" => reverse f

/-- Simplification lemma for reciprocal notation -/
@[simp]
lemma reciprocal_r {F : Type*} [Field F] {f : F[X]} : reverse f = f⁎ := rfl

/-! ### Basic Properties of Reciprocal Polynomials -/

/--
The natural degree remains unchanged under reciprocal when constant term is nonzero.
This formalizes that reciprical operation preserves the `degree` structure.
-/
@[simp]
lemma natDegree_reverse {F : Type*} [Field F] {f : F[X]} (he : f.coeff 0 ≠ 0) :
    f.reverse.natDegree = f.natDegree := by
  simp [*, natDegree_eq_reverse_natDegree_add_natTrailingDegree f, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero]

/--
The leading coefficient of the reciprocal is the original constant term.
This shows how `coefficients` transform under reciprocal operation.
-/
@[simp]
lemma coeffs_reverse {F : Type*} [Field F] {f : F[X]} (he : f.coeff 0 ≠ 0) :
    (f⁎).leadingCoeff = f.coeff 0 := by
    rw [leadingCoeff]
    simp only [coeff_reverse, revAt]
    simp only [ne_eq, Function.Embedding.coeFn_mk] at *
    simp only [ne_eq, not_false_eq_true, natDegree_reverse, le_refl, ↓reduceIte, tsub_self, he]

/--
The reciprocal is `involutive` when the constant term is nonzero.
Applying reciprocal twice gives the original polynomial.
-/
@[simp]
lemma reciprocal_involutive {F : Type*} [Field F] {f : F[X]} (hf : f.coeff 0 ≠ 0) : f⁎⁎ = f := by
  ext n
  simp only [coeff_reverse, revAt]
  have (hn : n ≤ f.natDegree) : f.natDegree - (f.natDegree - n) = n := Nat.sub_sub_self hn
  aesop

/--
Constant polynomials are units when nonzero.
This is used in irreducibility proofs for handling constant factors.
-/
lemma const_poly_is_unit {F : Type*} [Field F] (w : F) (hw : w ≠ 0) : IsUnit (C w) := by
  apply isUnit_C.2
  apply isUnit_iff_ne_zero.mpr
  exact hw

/-! ### Theorem 3.12: Irreducibility of Reciprocals -/

/--
**Theorem 3.12**: If `f` is irreducible and has nonzero constant term,
then its reciprocal is also irreducible.

This shows that the reciprocal operation preserves irreducibility for polynomials
with nonzero constant terms. The proof uses:
1. Reciprocal preserves nonzero degree
2. Factorization through the double reciprocal property
-/

theorem reciprocal_irreducible (f : F[X]) (hf : Irreducible f) (h0 : f.coeff 0 ≠ 0)  : Irreducible (f⁎) := by
  /- Unfold the definition of `Irreducible` -/
  replace hf := irreducible_iff.mp hf
  apply irreducible_iff.mpr
  rcases hf with ⟨h₁, h₂⟩
  constructor
  · /- Prove that `¬IsUnit (f⁎)` -/
    refine not_isUnit_of_natDegree_pos (f⁎) ?_

    show 0 < (f⁎).natDegree
    rw [Polynomial.reverse_natDegree f]
    have l_zero : f.natTrailingDegree = 0 := by
      apply Polynomial.natTrailingDegree_eq_zero.mpr; exact Or.inr h0
    /- Prove that f.natDegree > 0 -/
    by_cases j : f.natDegree = 0
    · /- f.natDegree = 0 => Contradiction -/
      apply Polynomial.natDegree_eq_zero.mp at j
      rcases j with ⟨w, j⟩
      rw [← j] at h₁
      have non_zero : w ≠ 0 := by
        rw [← j] at h0; simp at h0; tauto
      have w_unit : IsUnit (C w) := const_poly_is_unit w non_zero
      tauto
    · /- f.natDegree > 0 -/
      have pos : f.natDegree > 0 := Nat.zero_lt_of_ne_zero j
      rw [l_zero]; simp; exact pos

  · intro a b h
    /- We prove `f ≠ 0` , `f.coeff 0 ≠ 0` , `a.coeff 0 ≠ 0` , `b.coeff 0 ≠ 0`  in advance -/
    have f_neq_zero : f ≠ 0 := by
      exact Ne.symm (ne_of_apply_ne (fun f => f.coeff 0) fun a => h0 (id (Eq.symm a)))
    have f0_neq_zero : (f⁎).coeff 0 ≠ 0 := by simp [f_neq_zero]
    have ab0_neq_zero : a.coeff 0 * b.coeff 0 ≠ 0 := by
      rw [← mul_coeff_zero, ← h]; exact f0_neq_zero
    simp at ab0_neq_zero

    have r := reciprocal_involutive h0
    rw [h] at r
    simp at r
    have abUnit := h₂ r.symm
    rcases abUnit with ar | br
    · apply Polynomial.isUnit_iff.mp at ar
      rcases ar with ⟨r, ⟨ar, g⟩⟩
      apply_fun reverse at g
      simp [*] at g
      rw [← g]
      exact Or.inl (Polynomial.isUnit_C.mpr ar)
    · apply Polynomial.isUnit_iff.mp at br
      rcases br with ⟨r, ⟨br, g⟩⟩
      apply_fun reverse at g
      simp [*] at g
      rw [← g]
      exact Or.inr (Polynomial.isUnit_C.mpr br)

/-! ### Self-Reciprocal Polynomials and Theorem 3.13 -/

/--
**Definition**: A polynomial is self-reciprocal if it equals its reciprocal and is nonzero.
This captures polynomials symmetric under coefficient reversal.
-/
def self_reciprocal (f : F[X]) : Prop := f ≠ 0 ∧ f⁎ = f

/--
**Theorem 3.13**: Structure of self-reciprocal polynomials with two irreducible factors.

If a self-reciprocal polynomial `f` factors as `f = g * h` where both `g` and `h` are
irreducible with nonzero constant terms, then either:
1. `h⁎` is a scalar multiple of `g`, or
2. There's a scalar `b` with `b^2 = 1` such that `g⁎ = b•g` and `h⁎ = b•h`.

The proof uses:
1. The irreducibility of reciprocals (Theorem 3.12)
2. Prime factorization properties in polynomial rings
3. Unit group structure of the coefficient field
-/
theorem self_reciprocal_factor_structure {f g h : F[X]}
  (hf : f = g * h)
  (hg : Irreducible g) (hh : Irreducible h)
  (h0g : g.coeff 0 ≠ 0) (h0h : h.coeff 0 ≠ 0)
  (hs : self_reciprocal f) :
  (∃ a : Fˣ, h⁎ = a • g) ∨ (∃ b : Fˣ, b ^ 2 = 1 ∧ g⁎ = b • g ∧ h⁎ = b • h) := by
  --这里‘•’和‘*’的意义不同分别代表标量乘法和普通乘法，在进行这两种乘法类型的转换问题上查了很多资料，感觉lean4很严谨但也很逆天，而且感觉lean4的搜索引擎和AI有很大的提高空间......
  rw[self_reciprocal] at hs
  rcases hs with ⟨h1, h2⟩
  rw[hf] at h2; simp at h2
  --shit (),使用Lean4的时候总能碰到因为多加或者少加括号但是不知道自己到底为什么报错的问题
  --此处证明一些后面要用到的条件
  have g_neq_zero : g ≠ 0 := by
      intro h; rw[h] at h0g; simp at h0g
  have h_g : Irreducible (g⁎) := by
    exact reciprocal_irreducible g hg h0g
  have h_h : Irreducible (h⁎) := by
    exact reciprocal_irreducible h hh h0h
  --lean4中充要条件的转换很灵活
  have prime_g : Prime g := irreducible_iff_prime.mp hg
  have g_dvd : g ∣ g⁎ * h⁎ := by exact Dvd.intro h (id (Eq.symm h2))
  rcases prime_g.dvd_mul.mp g_dvd with (dvd_g' | dvd_h')
  --在写代码的时候发现have命名对于定理证明有很大帮助，从名字得到命题内容很方便
  · right
    have : Associated g (g⁎) := Irreducible.associated_of_dvd hg h_g dvd_g'
    obtain ⟨u, hu⟩ := this
    --证明u在F[X]中可逆
    have u_unit : IsUnit (u : F[X]) := Units.isUnit u
    rcases (Polynomial.isUnit_iff).1 u_unit with ⟨c, c_unit⟩
    rcases c_unit with ⟨hl, hr⟩
    have c_ne_zero : c ≠ 0 := by exact IsUnit.ne_zero hl
    --因为c本身是F类型，但是题目要求的是Fˣ类型，所以必须要做转换（逆天doge）
    let c_unit' : Fˣ :=  Units.mk0 c c_ne_zero  ---- 类型转换
    --Lean4中实现了从有限域道到有限域可逆元乘法群的转换 &&&
    rw[← hr, mul_comm] at hu
    have hh : (C c * g)⁎ = C c * (g⁎) := by simp
    have h₀ : C c * g⁎ = g := by
      rw [← hh, hu]; simp [*]
    rw[← hu, ← mul_assoc] at h₀
    have hh1 : C c * C c = 1 := by exact (mul_eq_right₀ g_neq_zero).mp h₀
    rw[← hu, mul_comm (C c) g,mul_assoc] at h2
    have hh2 :(C c) * h⁎ =  h := by
      apply mul_left_cancel₀ g_neq_zero
      exact h2
    use c_unit'
    rw[← smul_eq_C_mul] at hu
    rw[← smul_eq_C_mul] at hh2
    constructor
    · have c_sq_eq_one : c * c = 1 := by
      -- 应用常数多项式的单射性
        apply_fun (eval 0) at hh1
      -- 化简系数
        simp [eval_mul, eval_C, eval_C, eval_C, eval_one] at hh1
      -- 提取常数项
        exact hh1
      rw[pow_two]
      apply Units.ext
      exact c_sq_eq_one  ---  ! 类型转换
    constructor
    · rw[← hu]
      rw [show c • g = (c_unit' : F) • g by rw [Units.val_mk0]]
      norm_cast
    · --c_unit'其实属于F，但是因为添加了c_unit' ≠ 0 的条件，也属于Fˣ（annoyed but useful）&&&
      have hhh : c • h = (c_unit' : F) • h := by rw [Units.val_mk0]
      have hhh1 : c • h =c_unit' • h := by exact hhh
      rw[← hhh1]
      nth_rewrite 2[← hh2]
      repeat rw[smul_eq_C_mul]
      rw[← mul_assoc,hh1]
      simp
  · left
    have : Associated g (h⁎) := Irreducible.associated_of_dvd hg h_h dvd_h'
    obtain ⟨u, hu⟩ := this
    -- 将多项式单位 u 转换为域单位
    have u_unit : IsUnit (u : F[X]) := Units.isUnit u
    rcases (Polynomial.isUnit_iff).1 u_unit with ⟨a, a_unit⟩
    rcases a_unit with ⟨hl,hr⟩
    have a_ne_zero : a ≠ 0 := IsUnit.ne_zero hl
    let a_unit' : Fˣ := Units.mk0 a a_ne_zero
    rw[← hr, mul_comm] at hu
    use a_unit'
    rw [← hu, ← smul_eq_C_mul]
    rw [show a • g = (a_unit' : F) • g by rw [Units.val_mk0]]
    norm_cast

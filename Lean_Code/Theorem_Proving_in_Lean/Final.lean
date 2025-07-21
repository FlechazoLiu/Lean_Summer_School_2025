import Mathlib


-- 10 pt
example : ∀ a b c : ℝ, ∃ x : ℝ, a ≠ 0 → b ^ 2 - 4 * a * c ≥ 0 → a * x ^ 2 + b * x + c = 0 := by
  intro a b c
  set D := b ^ 2 - 4 * a * c with q
  use if a = 0 then 0 else (-b + Real.sqrt D) / (2 * a)
  intro ha₀ hD
  have hx : ite (a = 0) 0 ((-b + Real.sqrt D) / (2 * a)) = (-b + Real.sqrt D) / (2 * a) :=
    if_neg ha₀
  rw [hx]
  rw [add_assoc]
  have h2a : 2 * a ≠ 0 := mul_ne_zero two_ne_zero ha₀
  field_simp [h2a, mul_comm, mul_left_comm, sub_eq_add_neg, add_comm, add_assoc, add_left_comm]
  ring_nf
  have h : √D ^ 2 = D := by
    apply Real.sq_sqrt
    exact hD
  simp [h]
  rw [q]
  ring


section

open Classical Real

-- 5pt
theorem sqrt2_pow_sqrt2_pow_sqrt2_eq_2 : (√2 ^ √2) ^ √2 = 2 := by
  have : 0 ≤ √2 := by simp
  have h := Real.rpow_mul this √2 √2
  simp at h
  symm
  exact h

#check Real.rpow_mul
#print Irrational
-- 5pt
theorem ne_irrational_eq_rational (a : ℝ) : ¬ Irrational a ↔ ∃ (q : ℚ), a = q := by
  constructor
  · intro h
    rw [Irrational] at h
    simp at h
    rcases h with ⟨p, h⟩
    use p
    rw [h]
  · intro h
    rcases h with ⟨c, d⟩
    rw [d]
    rw [Irrational]
    simp



-- 10pt
theorem exist_irrat_power_rat : ∃ a b : ℝ, Irrational a ∧ Irrational b
    ∧ ∃ (q : ℚ), a ^ b = q := by
  have w := sqrt2_pow_sqrt2_pow_sqrt2_eq_2
  by_cases Irrational (√2 ^ √2)
  · case pos h =>
      use (√2 ^ √2), √2
      constructor
      · exact h
      · constructor
        · exact irrational_sqrt_two
        · use 2
          norm_cast
  · case neg h =>
      have h : ∃ (q : ℚ), √2 ^ √2 = q := (ne_irrational_eq_rational (√2 ^ √2)).mp h
      use √2, √2
      constructor
      · exact irrational_sqrt_two
      · constructor
        · exact irrational_sqrt_two
        · exact h

end

section
@[ext]
structure Vec2D where
  x : ℝ
  y : ℝ

namespace Vec2D

instance : Add Vec2D where
  add := fun v1 v2 => ⟨v1.1 + v2.1, v1.2 + v2.2⟩

instance : Zero Vec2D where
  zero := ⟨0, 0⟩

instance : Neg Vec2D where
  neg := fun v => ⟨-v.1, -v.2⟩

@[simp] lemma add_def (v1 v2 : Vec2D) : v1 + v2 = ⟨v1.1 + v2.1, v1.2 + v2.2⟩ := rfl
@[simp] lemma zero_def : (0 : Vec2D) = ⟨0, 0⟩ := rfl
@[simp] lemma neg_def (v : Vec2D) : -v = ⟨-v.1, -v.2⟩ := rfl

instance : AddCommGroup Vec2D where
  add_comm := fun v1 v2 => by ext <;> simp [add_comm]
  add_assoc := fun v1 v2 v3 => by ext <;> simp [add_assoc]
  zero_add := fun v => by ext <;> simp
  add_zero := fun v => by ext <;> simp
  neg_add_cancel := fun v => by ext <;> simp
  nsmul := fun n v => ⟨n * v.1, n * v.2⟩
  zsmul := fun z v => ⟨z * v.1, z * v.2⟩
  nsmul_zero := fun v => by ext <;> simp
  nsmul_succ := fun n v => by ext <;> dsimp <;> push_cast <;> linarith
  zsmul_zero' := fun v => by ext <;> simp
  zsmul_succ' := fun n v => by ext <;> dsimp <;> push_cast <;> linarith
  zsmul_neg' := fun n v => by ext <;> dsimp <;> push_cast <;> linarith

instance : HMul ℝ Vec2D Vec2D where
  hMul := fun n v => ⟨n * v.1, n * v.2⟩

@[simp] lemma mul_def (n : ℝ) (v : Vec2D) : n * v =  ⟨n * v.1, n * v.2⟩ := rfl

def linearIndependent (v1 v2 : Vec2D) := ∀ k1 k2 : ℝ, k1 * v1 + k2 * v2 = 0 → k1 = 0 ∧ k2 = 0

-- 5pt
lemma linearIndependent_symm (v1 v2 : Vec2D) :  v1.linearIndependent v2 ↔ v2.linearIndependent v1 := by
  constructor
  all_goals
    rw [linearIndependent]
    intro h
    intro k1 k2
    intro f
    rw [add_comm] at f
    apply (h k2 k1) at f
    tauto

-- 5pt
lemma not_zero_linear_independent : ∀ v : Vec2D, ¬ v.linearIndependent 0 := by
  intro v
  by_contra!
  rw [linearIndependent] at this
  have w := this (0 : ℝ) (1 : ℝ)
  have s : (0 : ℝ) * v + (1 : ℝ) * (0 : Vec2D) = 0 := by
    simp
  rw [s] at w
  have h₀ : (0 : Vec2D) = (0 : Vec2D) := rfl
  have c := (w h₀).right
  apply one_ne_zero c


-- 10pt
theorem det_neq_zero_linear_independent {v1 v2 : Vec2D} : v1.linearIndependent v2 → v1.x * v2.y - v1.y * v2.x ≠ 0 := by
  rw [linearIndependent]
  intro h
  simp at h
  by_contra!
  have q : v2.y * v1.x + -v1.y * v2.x = 0 := by
    rw [← this]
    ring
  have r : v2.y * v1.y + -v1.y * v2.y = 0 := by ring
  have s := h v2.y (-v1.y) q r
  have v2y : v2.y = 0 := by tauto
  have v1y : v1.y = 0 := by
    have : -v1.y = 0 := s.right
    exact neg_eq_zero.mp this
  simp [*] at h
  have i : v2.x * v1.x + -v1.x * v2.x = 0 := by ring
  have i := h v2.x (-v1.x) i
  have v1x : v1.x = 0 := by
    have : -v1.x = 0 := i.right
    exact neg_eq_zero.mp this
  have v2x : v2.x = 0 := by tauto
  rw [v1x, v2x] at h
  simp at h
  have := (h 1 1).right
  apply one_ne_zero this


-- 5pt
lemma exist_linear_comb : ∀ v1 v2 : Vec2D, v1.linearIndependent v2 → ∀ x, ∃ n₁ n₂ : ℝ, x = n₁ * v1 + n₂ * v2 := by
  intro v1 v2 h
  rw [linearIndependent] at h
  intro x
  rcases v1 with ⟨a1, b1⟩
  rcases v2 with ⟨a2, b2⟩
  rcases x with ⟨x, y⟩
  simp
  simp at h
  have s1 : a1 * b2 - a2 * b1 ≠ 0 := by
    by_contra!
    have r : b2 * a1 + -b1 * a2 = 0 := by
      rw [← this]
      ring
    have t : b2 * b1 + -b1 * b2 = 0 := by ring
    have q := h b2 (-b1) r t
    have b20 : b2 = 0 := q.1
    have b10 : b1 = 0 := by
      have : -b1 = 0 := q.2
      exact neg_eq_zero.mp this
    have i : a2 * a1 + -a1 * a2 = 0 := by ring
    have o : a2 * b1 + -a1 * b2 = 0 := by
      rw [b10, b20]
      ring
    have i := h a2 (-a1) i o
    have a20 : a2 = 0 := i.1
    have a10 : a1 = 0 := by
      have : -a1 = 0 := i.2
      exact neg_eq_zero.mp this
    rw [a10, a20, b10, b20] at h
    simp at h
    have := (h 1 1).right
    apply one_ne_zero this
  use (b2 * x - a2 * y) / (a1 * b2 - a2 * b1), (- b1 * x + a1 * y) / (a1 * b2 - a2 * b1)
  field_simp
  ring_nf
  tauto

/- x = n₁ * a1 + n₂ * a2
   y = n₁ * b1 + n₂ * b2 -/
end Vec2D

@[ext]
structure Mat2D where
  fstc : Vec2D
  sndc : Vec2D

namespace Mat2D

def mul (m1 m2 : Mat2D) : Mat2D where
  fstc := {
    x := m1.fstc.x * m2.fstc.x + m1.sndc.x * m2.fstc.y
    y := m1.fstc.y * m2.fstc.x + m1.sndc.y * m2.fstc.y
  }
  sndc := {
    x := m1.fstc.x * m2.sndc.x + m1.sndc.x * m2.sndc.y
    y := m1.fstc.y * m2.sndc.x + m1.sndc.y * m2.sndc.y
  }

instance : Mul Mat2D where
  mul := mul

@[simp] lemma mul_def (m1 m2 : Mat2D) : m1 * m2 = ⟨⟨m1.fstc.x * m2.fstc.x + m1.sndc.x * m2.fstc.y, m1.fstc.y * m2.fstc.x + m1.sndc.y * m2.fstc.y⟩, ⟨m1.fstc.x * m2.sndc.x + m1.sndc.x * m2.sndc.y, m1.fstc.y * m2.sndc.x + m1.sndc.y * m2.sndc.y⟩⟩ := rfl
@[simp] lemma mul_assoc (m1 m2 m3 : Mat2D) : m1 * m2 * m3 = m1 * (m2 * m3) := by
  ext <;> dsimp <;> ring

instance : HMul Mat2D Vec2D Vec2D where
  hMul := fun m v => ⟨m.fstc.x * v.x + m.sndc.x * v.y, m.fstc.y * v.x + m.sndc.y * v.y⟩

@[simp] lemma mul_vec_def (m : Mat2D) (v : Vec2D) : m * v = ⟨m.fstc.x * v.x + m.sndc.x * v.y, m.fstc.y * v.x + m.sndc.y * v.y⟩ := rfl

def det (m : Mat2D) : ℝ := m.fstc.x * m.sndc.y - m.fstc.y * m.sndc.x

-- 5pt
lemma det_mul_eq_mul_det (m1 m2 : Mat2D) : (m1 * m2).det = m1.det * m2.det := by
  rcases m1 with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases m2 with ⟨⟨e, f⟩, ⟨g, h⟩⟩
  repeat rw [det]
  simp
  ring

def IsLinearSolvable (m : Mat2D) (v : Vec2D) := ∃ x : Vec2D, x ≠ 0 ∧ m * x = v

instance : One Mat2D where
  one := ⟨⟨1, 0⟩, ⟨0, 1⟩⟩

@[simp] lemma one_def : (1 : Mat2D) = ⟨⟨1, 0⟩, ⟨0, 1⟩⟩ := rfl

instance : MulOneClass Mat2D where
  one_mul := fun m => by ext <;> simp
  mul_one := fun m => by ext <;> simp

instance : Zero Mat2D where
  zero := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

@[simp] lemma zero_def : (0 : Mat2D) = ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ := rfl

instance : MulZeroClass Mat2D where
  zero_mul := fun m => by ext <;> simp
  mul_zero := fun m => by ext <;> simp

def IsInvertible (m : Mat2D) := ∃ m' : Mat2D, m * m' = 1 ∧ m' * m = 1

-- 5pt
lemma left_inv_eq_right_inv {m m1 m2 : Mat2D} (hm1 : m * m1 = 1) (hm2 : m2 * m = 1) :
    m1 = m2 := by
  have assoc {a b c : Mat2D} : a * b * c = a * (b * c) := by
    rcases a with ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
    rcases b with ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩
    rcases c with ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩
    simp
    ring_nf
    tauto
  have l : m2 * m * m1 = m1 := by simp [*]
  have r : m2 * m * m1 = m2 := by
    rw [assoc]
    simp [*]
  nth_rewrite 1 [← l]
  exact r

-- You don't need to prove this lemma
lemma exist_left_inv {m m1 : Mat2D} (h : m * m1 = 1) : ∃ m2, m2 * m = 1 := by
  sorry

-- 5pt
lemma left_inv_iff_right_inv {m m' : Mat2D} : m * m' = 1 ↔ m' * m = 1 := by
  constructor
  · intro h
    have := exist_left_inv h
    rcases this with ⟨m2, t⟩
    have : m' = m2 := left_inv_eq_right_inv h t
    rw [this]
    exact t
  · intro h
    have := exist_left_inv h
    rcases this with ⟨m2, t⟩
    have : m = m2 := left_inv_eq_right_inv h t
    rw [this]
    exact t

end Mat2D

open Mat2D Vec2D

-- 30pt for all sorries, else 10+10+5+5 (Unordered)
theorem main (m : Mat2D) : List.TFAE [m.IsInvertible, m.det ≠ 0, m.fstc.linearIndependent m.sndc, ∀ v ≠ 0, IsLinearSolvable m v] := by
  tfae_have 1 → 2 := by
    intro h
    rw [IsInvertible] at h
    rcases h with ⟨n, h⟩
    replace h := h.1
    apply_fun det at h
    rw [det_mul_eq_mul_det m n] at h
    have : det 1 = 1 := by rw [det]; simp
    rw [this] at h
    by_contra g
    rw [g] at h
    simp at h
  tfae_have 2 → 3 := by
    intro h
    rw [linearIndependent]
    rcases m with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp
    rw [det] at h
    simp at h
    intro k1 k2
    intro t y
    have s : k1 * a * d + k2 * c * d = 0 := by
      rw [← add_mul]
      rw [t]
      ring
    have p : k2 * c * d = - k1 * b * c := by
      have o : k1 * b * c + k2 * d * c = 0 := by
        rw [← add_mul, y]
        ring
      linarith
    rw [p] at s
    have : k1 * (a * d - b * c) = 0 := by
      rw [← s]
      ring
    have q := mul_eq_zero.mp this
    rcases q with q | q
    · rw [q] at t
      simp at t
      rw [q] at y
      simp at y
      rcases t with t | t
      · rcases y with y | y
        · tauto
        · tauto
      · rcases y with y | y
        · tauto
        · have : a * d - b * c = 0 := by
            rw [t, y]
            ring
          tauto
    · tauto
  tfae_have 3 → 4 := by
    intro h
    rcases m with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    have s := det_neq_zero_linear_independent h
    simp at s
    intro v h
    rw [IsLinearSolvable]
    rcases v with ⟨p, q⟩
    simp
    sorry
  tfae_have 4 → 1 := by
    intro h
    rw [IsInvertible]
    rcases m with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp
    sorry
  tfae_finish

end
/- a * x_1.x + c * x_1.y = x
∧  b * x_1.x + d * x_1.y = y -/

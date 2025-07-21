import Mathlib

open Polynomial FiniteField
noncomputable section


/- **问题：** 设 b 是素域 Fₚ 中的非零元素。证明三项式 x ^ p - x - b 在 Fₚⁿ[x] 中不可约当且仅当 n 不被 p 整除。 -/

theorem problem_3_83 (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) (b : ZMod p) (hb : b ≠ 0) :
    Irreducible (map (algebraMap (ZMod p) (GaloisField p n)) (X ^ p - X - C b)) ↔
    ¬p ∣ n := by sorry
  /- 需要证明的三项式不可约条件:
     x^p - x - b 在 GaloisField p n[x] 中不可约
     当且仅当 p 不整除 n
  -/



variable (p : ℕ) [Fact p.Prime] (n : ℕ) (b : ZMod p) (hb : b ≠ 0)

/-- 定义目标多项式：x^p - x - b -/
def f : Polynomial (ZMod p) := X ^ p - X - C b
#print f

/-- 若 α 是 f(x)=0 的根，则 α + jb 也是根 (j = 0,1,...,p-1) -/
lemma root_iteration (α : SplittingField (f p b)) (hα : aeval α (f p b) = 0) :
    ∀ j : ZMod p, aeval (α + algebraMap (ZMod p) (SplittingField (f p b)) (j * b)) (f p b) = 0 := by sorry

/-- 引理 2：在素域 F_p 上不可约
    f(x) 在 F_p[x] 中不可约且分裂域为 F_{p^p} -/
lemma irreducible_over_prime_field : Irreducible (f p b) := by
  -- 利用反证法：若可约则必有根，但 f(c)=c^p-c-b= -b ≠ 0
  rw [f]
  have fermat (c : ZMod p) : c ^ p = c := ZMod.pow_card c
  have eval_f (c : ZMod p): aeval c (f p b) = c ^ p - c - b := by
    sorry

  sorry


/-- 主引理 3： * 括号，变量 -/
lemma minpoly_degree (α : SplittingField (f p b)) (hα : aeval α (f p b) = 0) : (minpoly (ZMod p) α).natDegree = p := by
   sorry

lemma minpoly_degree' (α : SplittingField (f p b)) (hα : aeval α (f p b) = 0) : (minpoly (GaloisField p n) α).natDegree = p / (Nat.gcd p n) := by sorry





-- /-- 引理 3：最小多项式次数计算
--     α 在 F_{p^n} 上的最小多项式次数 = p / gcd(p,n) -/
-- lemma minpoly_degree (hn : n ≠ 0) (α : AlgebraicClosure (ZMod p))
--     (hα : aeval α (f p b) = 0) :
--     letI : Field (GaloisField p n) := by infer_instance
--     let K := GaloisField p n
--     letI : Algebra K (AlgebraicClosure (ZMod p)) := by infer_instance
--     (minpoly K α).natDegree = p / Nat.gcd p n := by
--   -- 证明将通过域扩张维数公式完成
--   sorry




lemma minpoly_degree'' (hn : n ≠ 0) (α : AlgebraicClosure (ZMod p))
    (hα : aeval α (f p b) = 0) :
    let K := GaloisField p n
    letI : Algebra K (AlgebraicClosure (ZMod p)) := by infer_instance  -- 关键修复
    (minpoly K α).natDegree = p / Nat.gcd p n := by
  sorry



#check ZMod.pow_card





theorem artinSchreier_irreducible_iff :
    Irreducible (artinSchreierPoly p n b) ↔ ¬ p ∣ n := by
  let K := Fqn p n
  let f := artinSchreierPoly p n b

  -- “→” 方向：若 f 不可约，则 p ∤ n
  constructor
  · intro h_irred
    by_contra! hdiv
    -- 若 p ∣ n，则 ∃ x ∈ K, x^p - x = b （因为 Tr(x^p - x) = 0 恒为真 ⇒ 所有 b ∈ 𝔽_p 都在像中）
    -- 所以 f 有根 ⇒ 可约，与假设矛盾
    haveI : CharP K p := inferInstance
    -- Artin-Schreier 映射的像包含 𝔽_p
    -- 所以 b ∈ 𝔽_p ⊆ Im(φ) ⇒ f 有根 ⇒ 可约，矛盾
    obtain ⟨x, hx⟩ : ∃ x : K, x ^ p - x = b := by
      -- 用迹映射满射推得 b ∈ ker Tr = Im(φ)
      sorry
    -- 所以 f(x) = 0，f 有根
    have h_root : f.eval x = 0 := by
      simp [artinSchreierPoly, hx]
    -- 所以 f 可约，矛盾
    exact h_irred.not_dvd_X_sub_C x h_root

  -- “←” 方向：若 p ∤ n，则 f 不可约
  · intro h_not_dvd
    -- 用 Artin-Schreier 不可约性判据：若 b ∉ Im(φ)，则 f 不可约
    -- b ∈ 𝔽_p ⇒ 若 Tr(b) ≠ 0 ⇒ b ∉ ker Tr ⇒ 不在像中
    haveI : CharP K p := inferInstance
    haveI : FiniteField K := inferInstance

    have htrace : FiniteField.trace K (ZMod p) b ≠ 0 := by
      -- 若 p ∤ n，则 Tr|_{𝔽_p} = n·id ⇒ Tr(b) = n·b ≠ 0
      have : (n : ZMod p) ≠ 0 := by
        exact ZMod.natCast_ne_zero.mpr h_not_dvd
      rw [FiniteField.trace_zmod]
      simp [ZMod.natCast_zmod, ZMod.mul_eq_zero_iff, hb, this]
    -- 所以 b ∉ ker Tr ⇒ b ∉ Im(φ) ⇒ f 不可约
    exact irreducible_of_root_not_in_AS_map htrace

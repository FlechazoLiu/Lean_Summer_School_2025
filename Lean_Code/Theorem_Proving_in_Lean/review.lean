import Mathlib

/-!
# 基本概念

Lean中的所有对象都有类型，主要分为以下三类：

- **Inductive Type**: 基本类型如 `Nat`, `Int`，以及依赖其他类型的inductive families如 `List α`都属于该类型。
- **Function Type**: 使用 `→` 连接两个类型 `α` `β` 构成 `α → β` 的函数类型。
- **Type Universe**: 如 `Type` `Prop` `Type 1` 等。
-/

-- 使用 `#check` 命令可查看对象的类型
#check (1 : Nat)
#check 2
#check -1
#check 1.0
#check Nat
#check Type
#check Type 32
#check (fun x => x) 1
#check 1 + 1 = 2
#check Prop
#check True
#check False
#check true
#check false

-- 使用 `def` 命令可定义对象，即为具体对象命名

def x : Nat := 1

#check x
#eval x

def f : Nat → Nat := fun x => x + 1
def g : Nat → Nat → Nat → Nat := fun x y z => x + y + z
def h : (Nat × Nat × Nat) → Nat := fun t => t.1 + t.2.1 + t.2.2
#print Prod
-- 函数应用
#eval f x
#check g 1
#eval h ⟨1, ⟨2, 3⟩⟩


def NatList : Type := List Nat

/-!
在 Lean 中，所有具体命题的类型均为 `Prop`，比如 `1 + 1 = 2 : Prop`, `3 < 4 : Prop`，而 `Prop` 的类型为 `Type`。构造一个类型
为具体命题的值即构造该命题的证明。定理可以被视为一个函数，接受前提条件对应的证明（即类型为对应命题的值），返回目标命题的证明。在定义函数
时，用户需要使用参数给定的值构造出目标类型的值，证明定理时，相应的也是用前提中的命题构造目标命题的证明。

`theorem` 关键词与 `def` 类似，但所定义对象的类型必须为 `Prop`。`example` 可用于定义匿名对象，不限类型，但也无法在后续代码中使用。
-/

example (a b c: Nat) (h : a + b = a + c) : b = c := by
  -- 使用 `by` 进入 tactic mode，可在infoview中看到当前证明状态。注意 `by` 可在任何你需要提供一个指定类型的值时使用。
  apply add_left_cancel h

def n : Nat := by exact 2

-- 你也可以不使用tactic mode，而通过直接构造该类型的值进行证明，即 term proof。

example (a b c: Nat) (h : a + b = a + c) : b = c := add_left_cancel h

-- 你可以通过在 `by` 前加 `show_term` 查看 tactic 实际构造的值。

example (a b c: Nat) (h : a + b = a + c) : b = c := show_term by
  apply add_left_cancel h

/-!
Lean 中的函数有多种参数类型，常见的有显式参数、隐式参数、实例隐式参数，分别以 `()` `{}` `[]` 包裹。

- **显式参数**：以小括号包裹，每次调用函数时必须由用户提供。
- **隐式参数**：以花括号包裹，用户无需提供，由Lean从上下文中推断，也可强行提供。
- **实例隐式参数**：以方括号包裹，用户无需提供，由Lean进行实例搜索获得，详情见 *类型系统* 一节。
-/

def f₁ (n : Nat) := n + 1
#eval f₁ 2  -- 手动提供参数

def f₂ {α : Type} (x : α) := x

#check f₂ 2  -- Lean根据上下文推断，此处由输入值类型推断得到 `α` 为 `Nat`
#check f₂ (α := Int) 1  -- 强行提供隐式参数

def f₃ {α : Type} [Add α] (x y : α) := x + y

#synth Add Nat

#check f₃ 1 2  -- Lean根据输入值推断得到 `α` 为 `Nat`，然后进行实例搜索得到 `Add Nat` 实例。

inductive Color where
  | Blue
  | Red

-- #check f₃ Color.Blue Color.Red  --failed to synthesize Add Color

/-
# 证明技巧

本节主要介绍证明中常用的自动化 tactic，你可以在
[https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref](reference page)

找到相对全面的 tactic 指南。当你知道一个 tactic 的名字时，你可以使用 `#help tactic tactic_name` 来查看其文档（需要 `import Mathlib`）
-/

-- `simp`
/-
`simp` 是最常用的 tactic 之一，你可以将引理注册为 `simp` 引理，在使用 `simp` 进行化简时，Lean 会自动查找可用的 `simp` 引理。
如果 `simp` 生效，你可以使用 `simp?` 看到使用的引理。`simp only` 即只使用这些引理进行化简，可以优化程序效率。
-/
@[ext]
structure MyComplex where
  re : ℝ
  im : ℝ

namespace MyComplex

instance : Add MyComplex where
  add x y := ⟨x.re + y.re, x.im + y.im⟩
instance : Mul MyComplex where
  mul x y := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

@[simp]
lemma add_re (x y : MyComplex) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : MyComplex) : (x + y).im = x.im + y.im := rfl
@[simp] lemma mul_re (x y : MyComplex) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma mul_im (x y : MyComplex) : (x * y).im = x.re * y.im + x.im * y.re := rfl

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

theorem ex_1 (x y z : MyComplex) : x * (y + z) = x * y + x * z := by
  ext <;> dsimp only [mul_im, add_im, add_re, mul_re] <;> ring

end MyComplex

-- `field_simp`
/-
`field_simp` 常用于存在除号的场合。
-/
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x ^ 2 + d / x ^ 3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field_simp
  ring

-- `ring`
/-
`ring` 可用于化简交换环条件下的表达式。
-/
example {a b c : ℝ} :
  (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * a * c + 2 * b * c := by ring

-- `linarith`
/-
`linarith` 常用于证明线性等式与不等式，并且可以提供外部定理作为辅助。
-/

example {a b c d : ℝ} (ha : a = b) (hb : b = c) (hc : c = d) : a = d := by
  linarith

example {a b c d : ℝ} (ha : a ≤ b) (hb : c ≤ d) (hc : a ≤ c) : a ≤ d := by
  linarith

example {a b c : ℝ} (h : a ≤ b) : c + Real.exp a ≤ c + Real.exp b := by
  linarith [Real.exp_le_exp.mpr h]

example : ¬ ∃ (x : ℝ), x ^ 2 = -1 := by
  intro ⟨x, hx⟩
  linarith [sq_nonneg x]

-- `decide` / `norm_num`
/-
两者常用于解决数值计算相关问题，`decide` 还可用于解决实现了 `Decidable` instance的相关命题。
-/

example : 72 / 6 = 12 := by decide
example : Nat.Prime 7 := by norm_num
example : Nat.gcd 6 8 = 2 := by decide
example : Nat.Coprime 3 8 := by norm_num
example : 3 ≤ 8 := by decide

example : (3 : ℝ) ≤ 8 := by norm_num

-- `unfold`
/-
`unfold` 与 `rw` 均可用于展开定义，但 `unfold` 会展开所有出现的部分。
-/

abbrev complicateFun : Nat → Nat := fun n => (n * 3 + 2) % 4

example : complicateFun 3 = 3 ∧ complicateFun 5 = 1 := by
  -- rw [complicateFun, complicateFun]
  -- norm_num
  -- unfold complicateFun
  norm_num

-- `calc`
/-
`calc` 可用于对目标进行分步变换
-/

example {n : ℝ} : n * (n + 1) * (n + 2) = n ^ 3 + 3 * n ^ 2 + 2 * n := by
  calc
    _ = (n ^ 2 + n) * (n + 2) := by ring
    _ = n ^ 3 + 2 * n ^ 2 + n ^ 2 + 2 * n := by ring
    _ = _ := by ring

-- `omega`
#help tactic omega
example (n : Nat) (hn : n ≤ 3) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  omega

-- `positivity`

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity
example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

-- `tauto`

-- `norm_cast`

#help tactic tauto

/-!
# 类型系统

在 Lean 中有许多方法自定义类型，如 `inductive`、`structure`、`class`等。其中，使用 `inductive` 定义类型即声明该类型的值的构造
方式。每个 inductive type 都可以定义多个构造方式。
-/

inductive Number where
  | nat : Nat → Number
  | int : Int → Number
  | real : Real → Number
  | complex : Complex → Number

#print Number

#print Complex
#check Number.nat 1
#check Number.int (-1)
#check Number.real (1 : ℝ)
#check Number.complex ⟨1, 1⟩

inductive Color' where
  | Red
  | Blue
  | Yellow

#print Color'

/- 可以使用模式匹配关键词 `match` 对 inductive type 的值进行匹配。-/
def Number.get_complex (n : Number)  :=
  match n with
  | Number.complex n => n
  | _ => ⟨0, 0⟩

-- 常见有多个 constructor 的 inductive type 的例子
#print Or
#print Sum

#check Sum ℕ ℤ
#check (Sum.inl 3 : Sum ℕ ℤ)

#print Option

-- inductive families
/- 以下 `MyList` 实际上为type constructor，即接受一个类型返回一个新类型的函数。实际上定义了一族类型，称为 inductive family。-/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

/-
1 -> 2 -> nil
-/
#check MyList.cons 1 (MyList.cons 2 MyList.nil)
#check MyList


def MyList.head? {α : Type} (l : MyList α) : Option α :=
  match l with
  | .nil => .none
  | .cons h _ => .some h


/- `structure` 可用于定义只有一个 constructor 的 inductive type，并且能够生成一些辅助函数。-/
@[ext]  -- `@[ext]` 可用于生成引理
structure Point where
  x : ℕ
  y : ℕ
  z : ℕ

#print Point

#check Point.mk
#check Point.x
#check Point.y
#check Point.z
#check Point.mk.injEq
#check Point.mk.inj

#check Point.ext
#check Point.ext_iff


example (p1 p2 : Point) (hx : p1.x = p2.x) (hy : p1.y = p2.y) (hz : p1.z = p2.z) : p1 = p2 := by
  ext <;> assumption

-- 对于只有一个 constructor 的 inductive type，我们可以使用如下语法构造对应类型的值

def p1 := Point.mk 1 2 3

def p2 : Point := ⟨1, 2, 3⟩

def p3 : Point := {
  x := 1
  y := 2
  z := 3
}

def p4 : Point where
  x := 1
  y := 2
  z := 3

def p5 : Point := by
  exact ⟨1, 2, 3⟩

def p6 : Point := by
  constructor
  · exact 1
  · exact 2
  · exact 3

-- 常见 structure 的例子
#print And
#print Prod

#print Fin
#print Subtype

def MySpecialNumber := Subtype Nat.Prime
def MySpecialNumberTerm : MySpecialNumber := Subtype.mk 2 Nat.prime_two
#check MySpecialNumberTerm

#check MySpecialNumber


-- 错误范例，应当使用 `structure`
class Point' where
  x : ℕ
  y : ℕ
  z : ℕ

#check Point'.x

instance : Point' where
  x := 1
  y := 2
  z := 3

#eval Point'.x


class Dia (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ " => Dia.dia

#check Dia Nat

instance : Dia Nat where
  dia := Nat.add

#eval (1 : Nat) ⋄ 2

#print MulZeroClass
#print AddZeroClass

example {α : Type} [MulZeroClass α] [AddZeroClass α] (x : α ) : x + 0 = x ∧ x * 0 = 0 := by
  sorry

#print AddMonoid
#print Ring


/-!
# 拾遗
-/

namespace Point

def add (p1 p2 : Point) : Point := ⟨p1.1 + p2.1, p1.2 + p2.2, p1.3 + p2.3⟩

#eval p1.add p2

def mul (p1 p2 : Point) : ℕ := p1.1 * p2.1 + p1.2 * p2.2 + p1.3 * p2.3

#eval p1.mul p2


instance : Add Point where
  add := add

instance : HMul Point Point ℕ where
  hMul := mul

#eval p1 + p2
#eval p2 * p3

end Point

#check Point.add

#check _root_.add_comm
#check Nat.add_comm
#check Int.add_comm


class Indexed (α : Type) (β : outParam Type) where
  fst : α → β
  snd : α → β

instance : Indexed Point Nat where
  fst := Point.x
  snd := Point.y

#check Indexed.fst

structure Tuple (α : Type) where
  fst : α
  snd : α

instance {γ : Type} : Indexed (Tuple γ) γ where
  fst := fun t => t.fst
  snd := fun t => t.snd

#print Coe

instance {α : Type} : Coe (List α) (Option α) where
  coe := fun l => l.head?


#eval ([1, 2] : Option Nat)

section
variable {α : Type*} (p : α → Prop)
open Classical BigOperators Finset

noncomputable def func (x : α) := if p x then 1 else 0

example (s : Finset α) (h : ∀ x ∈ s, ¬p x) : ∑ x ∈ s, func p x = 0 := by
  unfold func
  rw [← sum_attach]
  conv =>
    enter [1, 2, x]
    rw [if_neg (h _ x.property)]
  simp only [sum_const_zero]
end

#help tactic induction'



example (c : 1 = 0) : False := by
  tauto

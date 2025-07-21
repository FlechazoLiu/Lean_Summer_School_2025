import Mathlib

/-
# 函数类型

本节课我们先从函数类型开始. 回顾在上节课中, 我们介绍了 Lean 中函数类型的定义: 即给定两个类型 `A` 和 `B`, 我们用单箭头 `→` 将其连接起来就可以得到类型 `A → B`, 其元素对应了数学中函数的概念. 不难看出, 这样的函数只是对应着数学中一元函数的概念. 那么多元函数在 Lean 中该如何实现呢?

## 多元函数

我们先从二元函数入手. 在数学上, 一个二元函数 `f(x, y)` 接受两个自变量 `x` 和 `y`, 返回一个值. 如果我们提供了一个自变量 `x₀`, `f(x₀, y)` 此时就变成了关于变量 `y` 的一元函数. 从这样的观点出发, `f(x, y)` 可以被视为这样一个一元函数 `F(x)`: 它接受一个自变量 `x₀`, 返回一个以 `y` 为变量的一元函数 `F(x₀) := f(x₀, y)`. 由此, 我们可以按照如下方式在 Lean 中定义二元函数: 一个从类型 `A` 和类型 `B` 分别接受参数, 返回一个类型 `C` 的二元函数类型为 `A → (B → C)`. 那么, 一个二元函数 `f : A → (B → C)` 接受一个来自类型 `A` 的元素 `a : A` 之后, 得到的函数值 `f a : B → C` 此时就是从类型 `B` 到类型 `C` 的函数; 再接受一个类型 `B` 的元素 `b : B` 后, 得到一个类型 `C` 的元素 `(f a) b`.

在上述定义中, 由于箭头 `→` 是右结合的运算符 (即不加括号时, 从右向左计算), 因此二元函数类型 `A → (B → C)` 也可以写成 `A → B → C`, 这样的写法从直觉上相对更好理解: 把整个函数取参的过程看成一个生产车间里的传送带, 箭头表示传送带运转的方向, 二元函数类型就表示从类型 `A` 开始, 传送带要依次接受一个类型 `A` 的参数和一个类型 `B` 的参数, 最终得到一个类型 `C` 的产品. 此外, 由于 Lean 中函数在自变量上的取值是用空格分隔表示, 而不是用括号, 所以在多变量函数的情形下, 这种多次取值被定义成左结合的连续空格分隔, 即上述表达式 `(f a) b` 可以被写成 `f a b`.
-/

section sec₁
variable (A B C : Type)
variable (a : A) (b : B) (f : A → B → C)

/-
f a : B → C
-/
#check f a

/-
f a b : C
-/
#check (f a) b

variable (c : A) (g : B → C) (h : A → B)
#check g (h c) -- 区分：复合函数

/-
这里 `section` 和下文第 43 行的 `end` 是配合使用的. 其作用是创造一块区块, 在这个区块里使用 `variable` 声明的变量只会在这个区块中起作用. 如果我们在第 43 行之后去 `#check` 第 17 行声明的变量 `a`, Lean 会向我们抛出一个错误. 此外, 我们还可以对区块进行命名以使它们成对出现, 比如这里的 `sec₁` 就是这个区块的名字.

由于两个自变量类型 `A` 和 `B` 的地位应该是等价的, 因此如果我们想把 `f` 看成是关于自变量 `b : B` 的值为 `A → C` 的一元函数, 我们可以通过使用占位符 `·` 的方式来传入自变量. 比如:
-/

/-
fun x ↦ f x b : A → C
-/
#check (f · b)

/-
多元函数类型的定义同理, 只需要不断延申连续箭头的长度即可.
-/
end sec₁

/-
error message: unknown identifier 'a'
-/
-- #check a

/-
## 函数的构造

上节课中, 我们简单讲解了如何构造一个函数 -- 使用 `fun` 关键字, 通过表达式 `fun (a : A) => f(a)` 来构造一个将自变量 `a` 映射成表达式 `f(a)` 的函数. 在这节课中, 我们对于这种构造方式做进一步的介绍. 除了使用 `fun (a : A) => ...` 这种格式, 我们还可以遵循以下原则来构造函数:

1. 标识符 `fun` 可以用上文的 `λ` 替代.
2. 如果从自变量的值的表达式中可以推断出自变量的类型, 则自变量的类型可以被省略.
3. 双箭头 `=>` 可以被替换成 `↦`.

比如我们可以通过以下几种方法来构造将自然数映射成它的二倍的函数:
-/

def f₁ : ℕ → ℕ :=
  fun (n : ℕ) => 2 * n

def f₂ : ℕ → ℕ :=
  λ (n : ℕ) => 2 * n

def f₃ : ℕ → ℕ :=
  fun n => 2 * n

def f₄ :=
  fun n ↦ 2 * n

#eval f₄ 2

def r :=
  λ n ↦ 2.0 * n

#eval r 0.5

/-
这里值得一提的是上述原则的第 2 条, 我们可以从 `f₃` 和 `f₄` 的定义中看到这一点. 在 `f₃` 的定义中, 我们在引入一个自变量 `n` 的时候省略了其类型, 但是因为我们提供了 `f₃` 的类型 `ℕ → ℕ`, 所以 Lean 可以推断出该自变量的类型是 `ℕ`. 在 `f₄` 的定义中, 我们省略了定义整体的类型, 但 Lean 可以从 `:=` 后的具体定义中推断出 `f₄` 的类型是一个函数类型. 至于该函数类型的自变量类型和值域类型, 则需要从自变量 `n` 被映射的值 `2 * n` 中推断出. 在上节课中, 我们说过数字默认是自然数类型的元素, 因此这里的 `2` 的类型是 `ℕ`, 而自变量 `n` 与一个自然数类型的元素做乘法, Lean 就会优先认为这里 `n` 的类型也是 `ℕ`. 那么其乘积 `2 * n` 的类型自然也是 `ℕ`, 整个函数就是 `ℕ → ℕ` 类型的了.

至于多元函数的构造, 按照其定义来说, 我们只需要把它当成是值为函数的函数就可以了. 因此我们可以如下简单地构造出多元函数:
-/

def f₅ : ℕ → ℕ → ℕ :=
  fun (n : ℕ) => (fun (m : ℕ) => n + m)

/-
5
-/
#eval f₅ 2 3

/-
如上, 我们定义了一个二元函数, 它接受两个自然数并返回它们的和.

Lean 也为我们提供了一个语法糖 (语法糖是指能够简化代码书写的语法), 允许我们只使用一个 `fun` 来同时提供多个参数. 比如上面的 `f₅` 又可被定义成:
-/

def f₅' : ℕ → ℕ → ℕ :=
  fun (n m : ℕ) => n + m

/-
5
-/
#eval f₅' 2 3

/-
## 依赖函数

最后我们来介绍依赖函数, 这是一类比较特殊的函数, 其定义如下: 首先给定一个函数 `B : A → Type`, 表示一个以类型 `A` 的元素为索引 (指标) 的函数, 即对于每个 `A` 中的元素 `a : A`, `B a` 表示一个类型, 对于不同的 `a : A`, `B a` 表示的类型可能不同. 现在我们构造这样一个函数 `f`, 使得其在每一个 `a : A` 上的取值都来自于相应的 `B a`, 即 `f a : B a`. 这样的函数被称为依赖函数, 因为其在每个自变量处取值的类型依赖于自变量本身. 对于上文的 `f`, 我们其类型记为 `(a : A) → B a`, 在 Mathlib 中, 我们还可以用 `Π a : A, B a` 来表示这个类型.
-/

section
variable (A : Type) (B : A → Type)
variable (f : (a : A) → B a)
variable (x : A)

/-
(a : A) → B a : Type
-/
#check (a : A) → B a

/-
f : (a : A) → B a
-/
#check f

/-
f x : B x
-/
#check f x

/-
(a : A) → B a : Type
-/
#check (Π a : A, B a)

example : ((a : A) → B a) = (Π a : A, B a) := by
  rfl


end

/-
上面的例子中, 我们使用自反策略 `rfl` 证明了 `((a : A) → B a) = (Π a : A, B a)` 这个命题. 这是可以理解的, 因为我们说, Mathlib 中的 `Π a : A, B a` 就是用 `(a : A) → B a` 来定义的, 所以它们当然应该是同一个东西, 也就满足等于号 `=` 的自反性. 实际上在 Lean 中, 我们把这种从定义上就相等的等价关系称为 **依定义等价**, 而与之相对的则是 **命题等价**. 比如给出一个闭区间 `[1, 5]` 上的函数 `f(x) = x`, 在这个区间上, 我们有 `max f(x) = 5`. 这个等价关系就是一个命题等价. 因为 `max f(x)` 的定义是实数 `k`, 满足 `∃ x₀ ∈ [1, 5], s.t. f(x₀) = k` 并且 `∀ x ∈ [1, 5], f(x) ≤ k`, 但实数 `5` 的定义显然不是前者 (一种定义方式是 `5, 5, 5...` 这个柯西列所代表的等价类). 这样的等价关系并不是从定义上得来的, 而是需要经过计算和逻辑推导, 因此被叫做命题等价.

我们在上节课引入了这样一个观点: 每个定理实际上都可以看作是一个函数, 它接受一些元素和证明作为参数, 返回目标结论的证明. 实际上大部分需要依赖变量的定理都可以看作是依赖函数. 比如我们的老朋友 `mul_assoc`:
-/

/-
mul_assoc.{u_1} {G : Type u_1} [Semigroup G] (a b c : G) : a * b * c = a * (b * c)
-/
#check mul_assoc

/-
我们将圆括号里的参数 `a b c : G` 放到类型中, `(a b c : G) → a * b * c = a * (b * c)` 恰好就是我们刚刚提到的依赖函数, 对于不同的参数 `a`, `b`, `c`, 我们得到的函数值类型也不同 -- 它们是不同命题的证明. 比如 `mul_assoc 1 2 3` 和 `mul_assoc 3 2 1`.

依赖函数的构造和普通的函数没有区别, 我们仍可以使用 `fun` 等一系列关键字来构造一个具体的依赖函数.
-/

/-
## 全称命题

更进一步地, 命题逻辑中的全称命题, 也即任意性命题, 也可以被视作是依赖函数类型. 在 Lean 中, 我们使用 `∀ (x : t), p(x)` 这样的格式来定义一个全称命题, 其中 `p(x)` 是关于变量 `x` 的一个命题. 比如, 我们可以定义全称命题 `∀ (n : ℕ), n ≤ 1` 来表示 "对于任意的自然数 `n`, `n` 都小于或等于 `1`".
-/

/-
∀ (n : ℕ), n ≤ 1 : Prop
-/
#check ∀ (n : ℕ), n ≤ 1

/-
特别地, 这样定义出来的当然是一个命题, 所以其类型是 `Prop`. 我们可以将一个全称命题的证明理解成一个函数, 假设我们有一个全称命题的证明 `h : ∀ (x : t), p(x)`, 那也就是说这个全称命题是真命题, 我们就可以将这个命题应用于任何的变量 `x₀ : t` 上, 从而得到命题 `p(x₀)` 的一个证明. 因此 `h` 可以看成是从类型 `t` 出发的一个函数, 但是又因为对不同的自变量 `x`, 我们得到的是不同命题 `p(x)` 的证明, 因此这是一个依赖函数, 实际上我们有如下等式:
-/

example : (∀ (n : ℕ), n ≤ 1) = ((n : ℕ) → n ≤ 1) := by
  rfl

#check (n : ℕ) → n ≤ 1


universe u v
variable (A : Type u) (B : Type v) (C : Sort u) (D : Sort v) (E : Prop)
#check A → B
#check C → D
#check A → E


/-
这说明在 Lean 中, 一个全称命题实际上就是一个依赖函数类型. 从这样的观点出发, 我们可以像使用依赖函数类型那样来使用一个全称命题. 我们只展示一些例子, 并做简单讲述.
-/

/-
∀ (n : Nat), n > 100 : Prop
-/
#check ∀ (n : Nat), n > 100

/-
∀ (n : Nat), n > 100 : Prop
-/
#check ∀ n : Nat, n > 100

/-
∀ (n : Nat), n > 100 : Prop
-/
#check ∀ n, n > 100

/-
∀ (n : Nat), n > 100 : Prop
-/
#check (n : Nat) → n > 100

example (f : ℕ → ℝ) (h : ∀ n : ℕ, f n ≤ 1) : f 0 ≤ 1 := by
  exact h 0

/-
上面几个使用了 `#check` 命令的例子告诉我们, 我们也可以像构造普通函数那样, 在全称命题中省略部分元素的类型 -- 只要 Lean 能够通过其他部分推断出这些被省略的类型即可. 此外, 我们也可以像使用函数那样来使用一个全称命题的证明, 直接将其作用在一个自变量上.

值得注意的一点是, Lean 允许这样的写法: `∀ n > 0, p(n)` (这里 `p(n)` 是一个关于变量 `n` 的命题). 即将一个关于全称命题引入的变量的条件放到全称符号中. 此时, 这个命题相等于命题 `∀ n, n > 0 → p(n)`, 而后者实际上可以被看作是一个二元的依赖函数.
-/

example (f : ℝ → ℝ) : (∀ n > 0, f n = 0) = (∀ n, n > 0 → f n = 0) := by
  rfl

example (f : ℝ → ℝ) (h : ∀ n > 0, f n = 0) : ∀ n > 1, f n = 0 := by
  intro n
  intro gt_one
  refine h n ?_
  refine gt_trans gt_one ?_
  exact zero_lt_one

/-
从上面的例子中可以看出, 我们可以完全可以像使用和证明多元函数的方式来使用和证明这个条件. 其中第二个例子需要我们学习完本节课的内容之后才能够完全理解.
-/


/-
# 局部定义

接下来我们介绍两个十分好用的关键字 -- `have` 和 `let`. 我们先来看一个上节课的作业题.
-/

example (a b : ℝ) : min a b = min b a := by
  refine le_antisymm ?_ ?_
  · refine le_min ?_ ?_
    · exact min_le_right _ _
    · exact min_le_left _ _
  · refine le_min ?_ ?_
    · exact min_le_right _ _
    · exact min_le_left _ _

/-
我们可以看到, 在第 211 行使用了 `refine le_antisymm ?_ ?_` 后, 我们需要证明的目标分别是 `min a b ≤ min b a` 和 `min b a ≤ min a b`. 为此我们在下文用极其类似的方法分别证明了两个子目标. 但实际上通过对称性, 如果我们能够证明命题 `∀ x y : ℝ, min x y ≤ min y x` 的话, 我们就可以通过这个命题的证明来直接得到两个子目标的证明 -- 把这个证明分别作用于 `a`, `b` 和 `b`, `a` 上即可.
-/

theorem aux : ∀ x y : ℝ, min x y ≤ min y x := by
  sorry

example (a b : ℝ) : min a b = min b a := by
  refine le_antisymm ?_ ?_
  · exact aux a b
  · exact aux b a

/-
这样的操作实际上和我们在数学中引入引理是极其类似的. 即我们可以将重复使用的相似结论提取归纳出来, 将其变为一个引理, 从而直接使用即可. 但如果我们像上面例子这样, 将用到的每个引理都写在最终的主定理之上, 当引理数量很多的时候, 这样的写法未免有点喧宾夺主了. 因此我们需要能够进行局部定义的手段 -- 即在证明主定理的过程中, 插入一段引理并证明它, 然后再利用这个证明好的引理继续主定理的证明.

为了做到这一点, 我们就需要使用 `have` 和 `let` 这两个关键字了.

`have` 和 `let` 用于在证明过程中引入局部变量, 被引入的变量既可以是一个命题的证明, 也可以非命题类型的元素. 其使用方法与之前介绍的 `theorem`, `def` 等基本一致. 比如:
-/

example (a b : ℝ) : min a b = min b a := by
  have aux' (x y : ℝ) : min x y ≤ min y x := by
    sorry
  refine le_antisymm ?_ ?_
  · exact aux' a b
  · exact aux' b a

example (a b : ℝ) : min a b = min b a := by
  let aux' (x y : ℝ) : min x y ≤ min y x := by
    sorry
  refine le_antisymm ?_ ?_
  · exact aux' a b
  · exact aux' b a

/-
需要注意的一点是, 使用 `have` 或 `let` 引入的定理, 其证明过程需要比 `have` 所在位置多一个缩进.

有了 `have` 和 `let`, 我们之前一道看起来比较复杂的例题也可以用结构更加清晰的方式写出来:
-/

open Real

example (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₁ : 0 < 1 + exp a := by
    exact add_pos zero_lt_one (exp_pos _)
  let h₂ : 1 + exp a ≤ 1 + exp b := by
    exact add_le_add_left (exp_le_exp_of_le h) 1
  exact log_le_log h₁ h₂

/-
实际上, `have` 和 `let` 之间是存在区别的. 当我们使用 `have x₁ : t₁ := ...` 的时候, Lean 不会为我们保留 `x₁` 的具体定义 `...`, 但 `let x₂ : t₂ := ...` 则会保留 `x₂` 的定义 `...`. 我们可以通过下面这个例子来形象地看到这一点:
-/

example {a : ℝ} : 1 + 1 = 3 :=
  let b : ℝ := a
  have c : ℝ := a

  have : a = b := by
    rfl

  /-
    tactic 'rfl' failed, the left-hand side
      a
    is not definitionally equal to the right-hand side
      c
  -/
  -- have : a = c := by
  --   rfl
  sorry

/-
可以看到, 对于实数 `a : ℝ`, 如果我们使用 `have c := a` 引入一个新的实数 `c : ℝ`, 由于 `have` 不保留被引入变量的定义, 所以现在的 `b` 只是一个新的实数, 其类型为 `ℝ`, 我们再也无法得到 `c = a` 这个信息, 因此我们没有办法使用自反策略 `rfl` 来证明 `a = c`. 而如果我们使用 `let b := a` 来引入一个新的实数 `b : ℝ`, 由于 `let` 会保留被引入变量的定义, 所以我们可以使用自反策略 `rfl` 来证明 `a = b`.

一般来讲, 当被引入变量是一个命题的证明时, 我们通常使用 `have` 来引入这个局部变量. 这是因为一个命题的所有证明都是依定义相等的, 因此我们不需要知道某个证明的具体定义是怎样的; 而当被引入变量是一个非命题类型的元素时 (我们一般将之称为 *数据*), 我们通常要使用 `let` 来引入这个变量. 因为我们往往需要知道这个变量到底是怎么定义的, 从而才能使用它. 在这种情况下, 它的定义是重要的.

此外需要注意的是, 在使用 `have` 和 `let` 时, 我们应该尽量只在关键处, 从而保持代码整体的清晰性与可读性. 千万不要频繁滥用, 甚至将每一小步骤、小命题都写成一个 `have`. 这会使代码过于琐碎, 降低可读性, 缺少整洁的风格. 如下就是一个过度引入局部变量的例子:
-/

/- A bad example. -/
example {a b : ℝ} (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₁ : exp a ≤ exp b := by
    exact exp_le_exp_of_le h
  have h₂ : 1 + exp a ≤ 1 + exp b := by
    exact add_le_add_left h₁ 1
  have h₃ : 0 < (1 : ℝ) := by
    exact zero_lt_one
  have h₄ : 0 < exp a := by
    exact exp_pos _
  have h₅ : 0 < 1 + exp a := by
    exact add_pos h₃ h₄
  have h₆ : log (1 + exp a) ≤ log (1 + exp b) := by
    exact log_le_log h₅ h₂
  exact h₆

/-
这样的代码看起来无疑会让人抓不住重点, 过于凌乱.
-/

/-
# 函数相关策略

函数类型的使用和构造相对比较简单, 但我们仍然介绍一些策略来帮助更好地处理它们.

## 引入策略 `intro`

在之前介绍的函数构造方法中, 我们使用 `fun` 等一系列关键字来构造函数, 引入函数自变量的操作也通过 `fun (a : A) => ...` 这个步骤实现. 而在策略模式中, 我们可以通过 `intro` 策略来做到这一点. 比如:
-/

def f₆ : ℕ → ℕ → ℕ :=
  fun n m => n + m

def f₆' : ℕ → ℕ → ℕ := by
  intro n
  intro m
  exact n + m

def f₆'' : ℕ → ℕ → ℕ := by
  intro n m
  exact n + m

def f₆''' : ℕ → ℕ → ℕ := by
  exact fun n m => n + m

/-
可以看到, 我们可以通过 `intro _被引入的变量名_` 这样的语法来引入一个函数的自变量. 特别地, 如果这个函数是一个多元函数, 我们可以通过 `intro _变量1_ _变量2_ ...` 这样的格式一次引入全部变量.

对于依赖函数的情形, `intro` 仍然适用.
-/

example : ∀ a b c : ℝ, a * b * c = a * (b * c) := by
  intro x y z
  rw [mul_assoc x y z]

example : (a b c : ℝ) → a * b * c = a * (b * c) := by
  intro a b c
  exact mul_assoc a b c

/-
## 函数外延性策略 `funext`

介绍了这么多关于函数类型的性质, 我们还没有谈论过两个函数相等的情形. 在数学上, 我们认为两个函数相等, 当且仅当, 它们在每个自变量处的取值相同. 在 Lean 中, 这一点同样成立, 事实上我们可以容易地证明其充分性:
-/

example (f g : ℝ → ℝ) (h : f = g) : ∀ x : ℝ, f x = g x := by
  intro x
  rw [h]

/-
只需要使用改写策略 `rw`, 我们就可以将函数 `f` 替换成与之相等的 `g`, 从而两个函数在每个自变量处的取值相同. 但必要性证明起来并不容易, 我们需要使用函数外延性策略 `funext` 来做到这一点.
-/

example (f g : ℝ → ℝ) (h : ∀ x : ℝ, f x = g x) : f = g := by
  funext a
  exact h a

/-
当我们的证明目标是一个函数等于另一个函数, 比如 `f = g` 时, 我们可以使用 `funext _被引入的变量名_` 这个语法将目标变为 `f _变量名_ = g _变量名_`. 这表示对于任意被引入的变量, 两个函数在这个变量处的值都相等.

Lean 中函数外延性的实现并不显然, 实际上这一性质的证明需要用到 Lean 依赖的公理之一 -- 商类型公理 `Quot.sound`. 我们将两者放在附录中, 供感兴趣的同学参考¹.
-/

#check Quot.sound
#print funext
#print axioms funext

/-
# 存在性命题

在本节课的最后, 我们来简单介绍一下存在性命题和其处理方法.

在 Lean 中, 我们可以通过类似全称命题的格式来定义一个存在性命题:
-/

/-
∃ n, n ^ 2 ≤ 2 : Prop
-/
#check ∃ n : ℕ, n ^ 2 ≤ 2

/-
从存在性命题的含义我们可以看出, 对于一个存在性命题 `∃ (x : t), p(x)` (其中 `p(x)` 是关于变量 `x` 的一个命题), 其一个证明 `h` 实际上相等于包含两个部分 -- 某个变量 `x₀ : t`, 以及这个变量满足命题 `p(x₀)` 的证明 `h₀ : p(x₀)`. 即我们应当可以从存在性命题中 "取出" 一个满足命题的元素. 这一操作可以通过策略 `rcases` 来实现. 具体来讲, 对于一个存在性命题的证明 `h` 来说, 我们可以使用
```
rcases h with ⟨x, hx⟩
```
的语法将该元素及其满足命题的证明取出来, 就像下面的例子展示的这样:
-/

example (f : ℝ → ℝ) (h : ∃ r : ℝ, f r = 0) : ∃ y : ℝ, f (y + 1) = 0 := by
  /-
    f : ℝ → ℝ
    x : ℝ
    hx : f x = 0
    ⊢ ∃ x, f (x + 1) = 0
  -/
  rcases h with ⟨x, hx⟩
  use x - 1
  rw [sub_add_cancel]
  exact hx

/-
将光标放在第 406 行的后边, 我们可以看到, 在使用 `rcases` 从存在性命题的证明 `h : ∃ x : ℝ, f x = 0` 中取出元素 `x` 和证明 `hx` 后, 原证明 `h` 从变量列表中消失, 取而代之的是得到的元素 `x` 以及 `x` 满足 `f x = 0` 的证明 `hx`.

如果要证明一个存在性命题, 我们往往需要使用构造性的证明方法, 即找到一个满足条件的元素并将它告诉 Lean. 比如上面的例子中, 我们希望使用 `x - 1` 来完成命题的证明, 这时我们可以使用策略 `use` 来告诉 Lean, `x - 1` 是我们想要的元素.

在使用了 `use` 后, Lean 会将我们希望使用的元素带入到存在性命题的后半部分中, 并将证明目标改为证明这个元素满足所需性质. 在上面的例子中, 我们使用 `use x - 1` 后, 证明目标就变成了证明 `f(x - 1 + 1) = 0`, 接下来我们就可以使用其他策略来像之前一样完成证明了.

此外, 和全称命题类似, 存在性命题也允许 `∃ n > 0, n + 1 < 3` 这样的写法, 即我们可以将一个条件并入到存在符号后面的变量中. 这个命题实际上相等于命题 `∃ n, n > 0 ∧ n + 1 < 3`, 即且命题的形式. 对于这样的命题, 我们同样可以使用 `rcases` 和 `use` 来处理它, 只不过需要一些小小的变化. 我们看下面这个例子:
-/

example (f : ℝ → ℝ) (h : ∃ r < 0, f r = 0) : ∃ y < -1, f (y + 1) = 0 := by
  rcases h with ⟨x, x_pos, hx⟩
  have lt_minus_one : x - 1 < -1 := by
    rw [← zero_add (-1), ← sub_eq_add_neg]
    refine sub_lt_sub_right ?_ 1
    exact x_pos
  use x - 1, lt_minus_one
  rw [sub_add_cancel]
  exact hx




-- Lean' s Axioms
#check propext
#check Classical.choice
#check Quot.sound

/-
可以看到, 对于一个绑定了条件的存在性命题, 我们在使用 `rcases` 从其中取出元素的时候, 需要在尖角括号 `⟨⟩` 中多添加一个参数来将这个被绑定的条件取出. 在上面的例子中, 我们用 `x_pos` 来承载这个证明, 它被添加的位置在变量 `x` 和证明 `hx` 中间.

当我们想要证明一个被绑定了条件的存在性命题时, 我们需要通过 `use ..., ...` 来同时提供所需的变量和这个被绑定的条件. 比如将光标放在第 432 行的开头, 我们可以看到, 证明目标为被绑定了条件的存在性命题 `∃ y < -1, f (y + 1) = 0`, 接下来我们使用 `use x - 1, lt_minus_one` 同时提供了元素 `x - 1` 以及 `x - 1 < -1` 的证明, 接下来目标就变成了 `f (x - 1 + 1) = 0`, 与之前的情形别无二致了.
-/

/-
# 随堂练习

按照要求完成定义或证明. 每道题目的上方标出了一些可能用到的定理. 你也可以不使用这些定理, 而是在 Mathlib 库中自行查找想用的定理.
-/



/-
# Appendix I: Lean 中 函数外延性的证明 [¹]
-/

#check funext
#print funext

#print axioms funext

#check Quot.sound
#print Quot.sound




-- L03 Exercise
/- 1. 定义二元函数 `f`, 将自变量 `x : ℝ`, `y : ℝ` 映射为 `x * y - x - y`. -/
def f : ℝ → ℝ → ℝ :=
  fun x y => x * y - x - y


/- 2. 先证明如下引理. -/
#check sub_mul
#check mul_sub
#check one_mul
#check mul_one
#check sub_add
#check add_sub_cancel_right
theorem lem (x y : ℝ) : f x y = (x - 1) * (y - 1) - 1 := by
  rw [f, sub_mul]
  rw [mul_sub]
  rw [mul_one x, one_mul (y - 1)]
  rw [← sub_add (x * y - x) y 1]
  simp


/- 3. 证明如下全称命题. -/
#check zero_add
#check sub_eq_add_neg
#check sub_le_sub_right
#check mul_self_nonneg
example : ∀ x, -1 ≤ f x x := by
  intro x
  rw [lem x x]
  have h : 0 ≤ (x - 1) * (x - 1)  := by
    apply mul_self_nonneg
  have h₁ := sub_le_sub_right h 1
  rw [zero_sub] at h₁
  exact h₁


/- 4. 证明如下存在性命题. -/
#check add_sub_cancel_right
#check sub_left_le_of_le_add
#check add_zero
#check le_trans
#check neg_sub
#check neg_mul
#check neg_nonpos_of_nonneg
#check mul_self_nonneg
example (y : ℝ) : ∃ x : ℝ, f x y ≤ 0 := by
  use 1
  rw [f, one_mul]
  simp

---------------------------------------------------------------------------------------

-- open Real
-- #check abs

-- /- 1. 请用 `ε - N` 语言给出数列收敛到某个极限的定义. -/
-- def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
--   /- 提示: 函数 `u` 可以被理解为一个以自然数为指标的实数列. `l` 则为指定的极限值. -/
--   ∀ (ε : ℝ), ε > 0 -> ∃ (N : ℕ), ∀ (n : ℕ), n > N -> abs (u n - l) < ε
--   -- ∀ ε > 0, ∃ N > 0, ∀ n > N, l x < ε


-- /- 2. 请用 `ε - δ` 语言给出实数集上的实值函数在某点处连续的定义. -/
-- def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
--   ∀ (ε : ℝ), ε > 0 -> ∃ (δ : ℝ), δ > 0 -> ∀ (x : ℝ), abs (x - x₀) < δ -> abs (f x - f x₀) < ε


-- /- 3. 证明连续函数和数列极限可交换顺序. -/
-- example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) : seq_limit (f ∘ u) (f x₀) := by
--   /- 提示: `f ∘ u` 表示函数之间的复合, 可以被理解为新的函数列 `{ f(uₖ) }`. 你可能需要引入如下引理来化简它. -/
--   have compl_simp (n : ℕ) : (f ∘ u) n = f (u n) := by
--     rfl
--   intro e
--   have h₁ := hf e
--   rcases h₁ with ⟨d, d_pos, hd⟩
--   have h₂ := hu d
--   sorry


-- /- 4. 证明连续函数的局部有界性. -/
-- #check zero_lt_one
-- #check le_add_of_sub_left_le
-- #check le_trans
-- #check abs_sub_abs_le_abs_sub
-- example (f : ℝ → ℝ) (x₀ : ℝ) (hf : continuous_at f x₀) : ∃ (d M : ℝ), ∀ x : ℝ, |x - x₀| ≤ d → |f x| ≤ M := by
--   sorry




--------------------------

open Real

/- 1. 请用 `ε - N` 语言给出数列收敛到某个极限的定义. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  /- 提示: 函数 `u` 可以被理解为一个以自然数为指标的实数列. `l` 则为指定的极限值. -/
  -- ∀ ε > 0, ∃ N, ∀ n > N, abs (u n - l) < ε
  ∀ (ε : ℝ), (0 < ε) →
  ∃ (N : ℕ),
    ∀ (n : ℕ), (N ≤ n) →
      abs (u n - l) ≤  ε


/- 2. 请用 `ε - δ` 语言给出实数集上的实值函数在某点处连续的定义. -/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - x₀) ≤ δ → abs (f x - f x₀) ≤ ε

/- 3. 证明连续函数和数列极限可交换顺序. -/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) : seq_limit (f ∘ u) (f x₀) := by
  /- 提示: `f ∘ u` 表示函数之间的符合, 可以被理解为新的函数列 `{ f(uₖ) }`. 你可能需要引入如下引理来化简它. -/
  have compl_simp (n : ℕ) : (f ∘ u) n = f (u n) := by
    rfl
  intro ε hε
  obtain ⟨δ, δ_pos, hf_δ⟩ := hf ε hε
  obtain ⟨N, hu_δ⟩ := hu δ δ_pos
  use N
  intro n hn
  apply hf_δ
  exact hu_δ n hn


/- 4. 证明连续函数的局部有界性. -/
#check zero_lt_one
#check le_add_of_sub_left_le
#check le_trans
#check abs_sub_abs_le_abs_sub
example (f : ℝ → ℝ) (x₀ : ℝ) (hf : continuous_at f x₀) : ∃ (d M : ℝ), ∀ x : ℝ, |x - x₀| ≤ d → |f x| ≤ M := by
  rcases hf (1 : ℝ) zero_lt_one with ⟨δ, δ_pos, hδ⟩
  use δ, |f x₀| + 1
  intro x hx
  exact le_add_of_sub_left_le (le_trans (abs_sub_abs_le_abs_sub (f x) (f x₀)) (hδ x hx))

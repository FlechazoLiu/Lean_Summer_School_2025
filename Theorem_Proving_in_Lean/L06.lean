import Mathlib


#check Nat

def Natfunc := Nat → Nat → Nat
#check Natfunc

#check Prod

#check Prod Nat Int

@[ext]
structure Point where
  x : Nat
  y : Nat
  z : Nat

#check Point

#print Point

#check Point.mk
#check Point.x
#check Point.y
#check Point.z

def p1 := Point.mk 1 2 3
#eval p1

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

#print And
#check Point.mk.injEq
#check Point.ext
#check Point.ext_iff

example (p q : Point) (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  ext <;> assumption

example {p q : Prop} (hp : p) (hq : q) : p ∧ q where
  left := hp
  right := hq


structure SpecialNumber where
  val : ℕ
  property : Nat.Prime val := by decide

#print SpecialNumber
def sn₁ : SpecialNumber := SpecialNumber.mk 2
def sn₂ : SpecialNumber := ⟨2, by decide⟩
def sn₃ : SpecialNumber where
  val := 3

structure IsSpecialPoint (p : Point) : Prop where
  x_prime : Nat.Prime p.x := by decide
  y_prime : Nat.Prime p.y := by decide
  z_prime : Nat.Prime p.z := by decide


example : IsSpecialPoint ⟨2, 3, 5⟩ where

structure SpecialPoint (prop : Point → Prop) extends Point where
  property : prop toPoint

#print SpecialPoint

def sp₁ : SpecialPoint (fun p => Odd p.x ∧ Odd p.y ∧ Odd p.z) where
  x := 1
  y := 3
  z := 5
  property := by
   repeat
    constructor
    decide
    decide

#print Subtype

abbrev SpecialPoint' (prop : Point → Prop) := { p // prop p }

#check  ((⟨⟨1, 2, 3⟩, by decide⟩ : SpecialPoint' (fun p => p.x = 1)) : Point)



structure A where
  x : Nat

structure B extends A where
  y : Nat

structure C extends A where
  z : Nat

structure D extends B, C

#print D


inductive Point' where
  | mk (x : Nat) (y : Nat) (z : Nat) : Point'

#print Point'

def p1' : Point' := Point'.mk 1 2 3

namespace Point'

def x (p : Point'): Nat :=
  match p with
  | mk x _ _ => x

#eval x p1'
#eval p1'.x

def y : Point' → Nat
  | mk _ y _ => y

def z (p : Point') : Nat := by
  match p with
  | mk _ _ z => exact z

#eval p1'.z

#check Point.mk.inj

#print Or
#print Sum

#check Sum Nat Int
end Point'

inductive ZMod' (n : Nat) where
  | mk (val : Nat) (prop : val < n) : ZMod' n

inductive ZMod'' (n : Nat) where
  | zero_case (val : Int) (prop : n = 0) : ZMod'' n
  | other_case (val : Nat) (prop : val < n) : ZMod'' n

def ZMod'.val {n : Nat} (z : ZMod' n) : Nat :=
  match z with
  | mk val _ => val

def ZMod''.val {n : Nat} (z : ZMod'' n) :=
  match z with
  | zero_case val _ => val
  | other_case val _ => val

#check 1 + 2
#check (1 : ℝ) + 2

class Plus (α : Type) where
  plus : α → α → α

instance : Plus Nat where
  plus := Nat.add

#check Plus.plus 1 2

def Point.add (p1 p2 : Point) : Point :=
  ⟨p1.1 + p2.1, p1.2 + p2.2, p1.3 + p2.3⟩

#eval p1.add p2


#print Add

#print Mul

#print HAdd

instance (priority := 1000): HAdd Point Nat Int where
  hAdd := fun p n => n - p.1 + p.2 - p.3

instance (priority := 100): HAdd Point Nat Int where
  hAdd := fun p n => n + p.1 - p.2 + p.3


#eval (⟨1, 2, 3⟩ : Point) +  1


#print MulZeroClass
#print AddZeroClass

#check zero_add
#check zero_mul
#check Zero.zero

#print Ring
#print AddMonoid




-- example {α : Type} [MulZeroClass α] [AddZeroClass α] (x : α) : 0 * x = 0 ∧ 0 + x = x := by
--   constructor
--   · rw [zero_mul]
--   rw [zero_add]

class Dia (α : Type) where
  dia : α → α → α
  dia' : α → α

prefix:80 " ⋄ " => Dia.dia'
-- ⁻¹
instance : Dia Nat where
  dia := Nat.mul
  dia' := fun n => n + 1

#eval ⋄1

#check (1 : Int)

#check ((⟨1, by decide⟩ : { n // n = 1}) : Nat)

#print Coe
-- coercion

class Indexed (α : Type) (β : outParam Type) where
  fst : α → β
  snd : α → β

#print Membership
instance : Indexed Point Nat where
  fst := fun p => p.x
  snd := fun p => p.y

structure Tuple (α : Type) where
  fst : α
  snd : β

instance {α β : Type} : CoeFun (α ≃ β) (fun _ => α → β) where
  coe e := e.toFun

variable (n : Nat)

#check Equiv.Perm (Fin n)

def e := Equiv.refl (Fin n)

#eval e 5 2

instance {α : Type} : Coe (Tuple α) α where
  coe := fun t => t.fst

#check semiOutParam

-- #eval ((⟨1,2⟩ : Tuple Nat) : Nat)

-- instance {prop : Point → Prop} : Coe (SpecialPoint prop) Point where
  -- coe := fun p => p.toPoint

#print CoeDep

instance {prop : Point → Prop} {p : SpecialPoint prop}: CoeDep (SpecialPoint prop) p Point where
  coe := p.toPoint

#check  ((⟨⟨1, 2, 3⟩, by decide⟩ : SpecialPoint (fun p => p.x = 1)) : Point)

#print CoeFun

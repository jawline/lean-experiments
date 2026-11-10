module

import Mathlib.Data.Nat.Bits
import Aesop

namespace HelloWorld

public def hello := "world"

public def double (n : Nat) : Nat := n + n
public def incr (n : Nat) : Nat := n + 1

public def is_pow2 (n:Nat) : Bool := (Nat.bits n).count true == 1
public def double_if_pow2(n:Nat) := if is_pow2 n then double n else n

inductive ValueTag where
  | unit
  | i32
  | f32
  | bool
deriving DecidableEq

public inductive Value where
  | unit
  | bool (val : Bool)
  | i32 (val : Int32)
  | f32 (val : Float32)

def Value.tag : Value → ValueTag
  | Value.unit => ValueTag.unit
  | Value.bool _ => ValueTag.i32
  | Value.i32 _ => ValueTag.i32
  | Value.f32 _ => ValueTag.f32

public inductive Expr where
  | atom (val : Value)
  | add (lhs : Value) (rhs : Value)
  | sub (lhs : Value) (rhs : Value)

abbrev sameType (lhs : Value) (rhs : Value) : Prop := lhs.tag = rhs.tag
abbrev notBool (lhs : Value) : Prop := lhs.tag ≠ ValueTag.bool

abbrev SafeArithmetic : Type :=
  (lhs rhs : Value) → sameType lhs rhs → notBool lhs → Value

def applySafeArithmetic (f_i32 : (Int32 -> Int32 -> Int32)) : SafeArithmetic :=
  fun lhs rhs _ _ => by
    match lhs, rhs with
    | Value.unit, Value.unit => exact Value.unit
    | Value.i32 a, Value.i32 b => exact Value.i32 (f_i32 a b)
    | _, _ => aesop

def ensure (p : Prop) [Decidable p] (err : String) : Except String (PLift p) :=
  if h : p then Except.ok ⟨h⟩ else Except.error err

def doArithmeticOrTypeError (f : SafeArithmetic) (lhs rhs : Value)
    : Except String Value := do
  let ⟨h⟩ ← ensure (sameType lhs rhs) "Add is illegal on values of different types"
  let ⟨q⟩ ← ensure (notBool lhs) "Add is illegal on bools"
  return f lhs rhs h q

public def eval : Expr → Except String Value
  | Expr.atom val => Except.ok val
  | Expr.add lhs rhs => doArithmeticOrTypeError (applySafeArithmetic (. + .)) lhs rhs
  | Expr.sub lhs rhs => doArithmeticOrTypeError (applySafeArithmetic (. - .)) lhs rhs

end HelloWorld

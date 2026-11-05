module

import Mathlib.Data.Nat.Bits
import Aesop

namespace HelloWorld

public def hello := "world"

public def double (n : Nat) : Nat := n + n
public def incr (n : Nat) : Nat := n + 1

public def is_pow2 (n:Nat) : Bool :=  (Nat.bits n).count true == 1
public def double_if_pow2(n:Nat) := if is_pow2 n then double n else n

inductive ValueTag where
  | unit
  | i32 
  | bool deriving DecidableEq

public inductive Value where
  | unit
  | i32 (val : Int32)
  | bool (val : Bool)

def Value.tag : Value → ValueTag
  | Value.unit => ValueTag.unit
  | Value.i32 _ => ValueTag.i32
  | Value.bool _ => ValueTag.i32

public inductive Expr where
  | atom (val : Value)
  | add (lhs : Value) (rhs : Value)

def add (lhs rhs : Value) (h : lhs.tag = rhs.tag) (q : lhs.tag ≠ ValueTag.bool) : Value :=
  by match lhs, rhs with
     | Value.unit, Value.unit => exact Value.unit
     | Value.i32 a, Value.i32 b => exact Value.i32 (a + b)
     | _, _ => aesop



def apply (f : Value  → Value → Value) (lhs : Value) (rhs : Value) (_h : lhs.tag = rhs.tag) : Value :=
  f lhs rhs

abbrev sameType (lhs : Value) (rhs : Value) : Prop := lhs.tag = rhs.tag

abbrev notBool (lhs : Value) : Prop := lhs.tag ≠ ValueTag.bool

def ensure (p : Prop) [Decidable p] (err : String) : Except String (PLift p) :=
  if h : p then Except.ok ⟨h⟩ else Except.error err

public def eval : Expr → Except String Value
  | Expr.atom val => Except.ok val
  | Expr.add lhs rhs => do
    let ⟨h⟩ ← ensure (sameType lhs rhs) "Add is illegal on values of different types"
    let ⟨q⟩ ← ensure (notBool lhs) "Add is illegal on bools"
    return add lhs rhs h q

end HelloWorld

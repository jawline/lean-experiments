module

import Mathlib.Data.Nat.Bits
import Aesop

namespace BaseLang

public def hello := "world"

public def double (n : Nat) : Nat := n + n
public def incr (n : Nat) : Nat := n + 1

public def is_pow2 (n:Nat) : Bool :=  (Nat.bits n).count true == 1
public def double_if_pow2(n:Nat) := if is_pow2 n then double n else n

public inductive ValueTag where
  | unit
  | i32 
  | f32
  | bool deriving DecidableEq

public def ValueTag.is_arithmetic : ValueTag → Bool
  | .unit 
  | .i32   
  | .f32  => true
  | .bool => false

public inductive Value where
  | unit
  | bool (val : Bool)
  | i32 (val : Int32)
  | f32 (val : Float32)

public def Value.tag : Value → ValueTag
  | Value.unit => ValueTag.unit
  | Value.bool _ => ValueTag.i32
  | Value.i32 _ => ValueTag.i32
  | Value.f32 _ => ValueTag.f32

public inductive Expr where
  | atom (val : Value)
  | add (lhs : Expr) (rhs : Expr)
  | sub (lhs : Expr) (rhs : Expr)

public abbrev sameType (lhs : Value) (rhs : Value) : Prop := lhs.tag = rhs.tag
public abbrev isArithmetic (lhs : Value) : Prop := (lhs.tag).is_arithmetic

 

end BaseLang

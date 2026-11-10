module

import Mathlib.Data.Nat.Bits
import Aesop

namespace Value

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

public inductive Value : Tag → Type 
  | unitVal : Value .unit
  | boolVal (val : Bool) : Value .bool
  | i32Val (val : i32) : Value .i32
  | f32Val (val : Float32) : Value .f32

public def add {t : Tag} (lhs : Value t) (rhs : Value t) (h : t.is_arithmetic) : Value t :=
  match h, t, lhs, rhs with
  | _, .unit, _, _ => .unitVal
  | _, .i32, .i32Val l, .i32Val r => .i32Val(l + r)
  | _, .f32, .f32Val l, .f32Val r => .f32Val(l + r)


public abbrev sameType (lhs : Value) (rhs : Value) : Prop := lhs.tag = rhs.tag
public abbrev isArithmetic (lhs : Value) : Prop := (lhs.tag).is_arithmetic
 
end Value

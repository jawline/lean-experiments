module

import Mathlib.Data.Nat.Bits
import Aesop

namespace Value

public inductive ValueTag where
  | unit
  | i32
  | f32
  | bool
deriving DecidableEq

public inductive Value : ValueTag → Type
  | unitVal : Value .unit
  | boolVal (val : Bool) : Value .bool
  | i32Val (val : Int32) : Value .i32
  | f32Val (val : Float32) : Value .f32


end Value

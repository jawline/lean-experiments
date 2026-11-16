module

import Mathlib.Data.Nat.Bits
import Aesop

public import HelloWorld.Value

namespace Value

public inductive ComparisonBinOp where
  | equal
  | not_equal
  | greater_than
  | less_than

@[expose] public def ComparisonBinOp.is_legal_operation_for_type (op : ComparisonBinOp) (tag : ValueTag) : Bool :=
  match tag with
  | .unit => false
  | .bool =>
      match op with
      | .greater_than | .less_than => false
      | .equal | .not_equal => true
  | .i32 | .f32 => true

public def ComparisonBinOp.implementation (op : ComparisonBinOp)
    : (tag : ValueTag) → op.is_legal_operation_for_type tag = true → Value tag → Value tag → Value .bool
  | .unit, h, _, _ => nomatch h
  | .bool, h, .boolVal a, .boolVal b =>
      match op with
      | .equal => .boolVal (a == b)
      | .not_equal => .boolVal (a != b)
      | .greater_than => nomatch h
      | .less_than => nomatch h
  | .i32, _, .i32Val a, .i32Val b =>
      .boolVal
        (match op with
          | .equal => a == b
          | .not_equal => a != b
          | .greater_than => a > b
          | .less_than => a < b)
  | .f32, _, .f32Val a, .f32Val b =>
      .boolVal
        (match op with
          | .equal => a == b
          | .not_equal => a != b
          | .greater_than => a > b
          | .less_than => a < b)

end Value

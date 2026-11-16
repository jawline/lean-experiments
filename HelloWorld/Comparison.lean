module

import Mathlib.Data.Nat.Bits
import Aesop

namespace Value

public inductive ComparisonBinOp where
  | equal
  | not_equal
  | greater_than
  | less_than


public def ComparisonBinOp.implementation (op : ArithmeticBinOp)
    : (tag : ValueTag) → Value tag → Value tag → Value tag
  | .unit, _, _, _ => .unitVal
  | .i32, _, .i32Val a, .i32Val b =>
      .i32Val
        (match op with
          | .add => a + b
          | .subtract => a - b
          | .multiply => a * b
          | .divide => a / b)
  | .f32, _, .f32Val a, .f32Val b =>
      .f32Val
        (match op with
          | .add => a + b
          | .subtract => a - b
          | .multiply => a * b
          | .divide => a / b)
  | .bool, h, _, _ => nomatch h

end Value

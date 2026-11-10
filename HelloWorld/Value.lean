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

public def ValueTag.is_arithmetic : ValueTag → Bool
  | .unit
  | .i32
  | .f32 => true
  | .bool => false

public inductive Value : ValueTag → Type
  | unitVal : Value .unit
  | boolVal (val : Bool) : Value .bool
  | i32Val (val : Int32) : Value .i32
  | f32Val (val : Float32) : Value .f32

public inductive ArithmeticBinOp where
  | add
  | subtract
  | multiply
  | divide

public def ArithmeticBinOp.implementation (op : ArithmeticBinOp)
    : (tag : ValueTag) → tag.is_arithmetic = true → Value tag → Value tag → Value tag
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

public def binOp {t : ValueTag}
    (select_implementation
      : (tag : ValueTag) → tag.is_arithmetic = true → Value tag → Value tag → Value tag)
    (lhs : Value t) (rhs : Value t) (h : t.is_arithmetic = true)
    : Value t :=
  select_implementation t h lhs rhs


public def ArithmeticBinOp.is_commutative (op : ArithmeticBinOp) (tag : ValueTag)
    : Prop :=
  ∀ (h : tag.is_arithmetic = true) (a b : Value tag),
    ArithmeticBinOp.implementation op tag h a b
    = ArithmeticBinOp.implementation op tag h b a

public def ArithmeticBinOp.is_commutative_i32 : ArithmeticBinOp → Bool
  | .add | .multiply => true
  | .subtract | .divide => false

public theorem ArithmeticBinOp.is_commutative_i32_correct (op : ArithmeticBinOp)
    : match ArithmeticBinOp.is_commutative_i32 op with
      | true => ArithmeticBinOp.is_commutative op .i32
      | false => ¬ ArithmeticBinOp.is_commutative op .i32 := by
  cases op with
  | add =>
      intro (h : ValueTag.i32.is_arithmetic = true) (a : Value .i32) (b : Value .i32)
      cases a with
      | i32Val x =>
          cases b with
          | i32Val y =>
              simp [ArithmeticBinOp.implementation, Int32.add_comm]
  | multiply =>
      intro (h : ValueTag.i32.is_arithmetic = true) (a : Value .i32) (b : Value .i32)
      cases a with
      | i32Val x =>
          cases b with
          | i32Val y =>
              simp [ArithmeticBinOp.implementation, Int32.mul_comm]
  | subtract =>
      intro (h : ArithmeticBinOp.is_commutative .subtract .i32)
      have h' := h rfl (.i32Val 5) (.i32Val 3)
      simp [ArithmeticBinOp.implementation] at h'
  | divide =>
      intro (h : ArithmeticBinOp.is_commutative .divide .i32)
      have h' := h rfl (.i32Val 6) (.i32Val 3)
      simp [ArithmeticBinOp.implementation] at h'

end Value
